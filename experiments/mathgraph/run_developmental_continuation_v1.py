#!/usr/bin/env python3
import importlib.util, json, random, sys, time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
OUT=ROOT/'experiments/mathgraph/results/developmental-continuation-v1.json'
IDS=[
 'evaluation_normal_0036','evaluation_normal_0040','evaluation_hard_0196',
 'evaluation_order5_0014','evaluation_order5_0042']
CFGS=['evaluation_normal','evaluation_hard','evaluation_order5']
SEED=20260820
WARM_SECONDS=4.0
PROBE_SECONDS=0.035
CONT_SECONDS=4.0
SEED_CANDIDATES=24
RETAIN=4
DESC_LIMIT=96


def loadm():
 s=importlib.util.spec_from_file_location('mg_devcont',SOLVER)
 m=importlib.util.module_from_spec(s);sys.modules[s.name]=m;s.loader.exec_module(m);return m

def canon(m,a,b):
 ra,rb=m.render_term(a),m.render_term(b)
 return tuple(sorted((ra,rb)))

def distance(m, recipe, target):
 return min(
  m.structural_distance(recipe.lhs,target[0])+m.structural_distance(recipe.rhs,target[1]),
  m.structural_distance(recipe.lhs,target[1])+m.structural_distance(recipe.rhs,target[0]))

def target_closed(m, search, source, target):
 r=search.target_proof()
 if r is None:return False
 try:
  nodes,root=search.compile(r)
  return ((nodes[root].lhs,nodes[root].rhs)==target[:2] and
   m.replay_dag(source,nodes,root,maximum_term_size=search.limits['maximum_replay_term_size'],maximum_nodes=search.limits['maximum_proof_nodes']))
 except Exception:return False

def probe_seed(m, search, seed, seed_index, target, base_keys):
 started=time.monotonic(); rules=list(search.rules()); descendants=[]; seen=set(); cp_attempts=0
 # Only ordinary compact-superposition critical pairs involving this verified seed.
 pairs=[]
 for j,r in enumerate(rules):pairs.append((seed,r,seed_index,j));pairs.append((r,seed,j,seed_index))
 for outer,inner,oi,ii in pairs:
  if time.monotonic()-started>=PROBE_SECONDS or len(descendants)>=DESC_LIMIT:break
  for side_name,outer_term in [('lhs',outer.lhs),('rhs',outer.rhs)]:
   if time.monotonic()-started>=PROBE_SECONDS or len(descendants)>=DESC_LIMIT:break
   for path in m.nonvariable_positions(outer_term,maximum_depth=search.limits['maximum_depth'],include_root=True):
    if time.monotonic()-started>=PROBE_SECONDS:break
    cp_attempts+=1
    # critical_pair uses outer.lhs as the overlap side, so symmetry is represented by ordinary symmetric clauses already in rules.
    try:q=search.critical_pair(outer,inner,oi,ii,path)
    except Exception:q=None
    if q is None:continue
    try:q=search.interreduce(q,rules)
    except Exception:pass
    k=canon(m,q.lhs,q.rhs)
    if k in base_keys or k in seen:continue
    seen.add(k);descendants.append(q)
    if len(descendants)>=DESC_LIMIT:break
 # Replayable here means generated from replayable recipes through ordinary inference constructors.
 replayable=len(descendants)
 best_before=distance(m,seed,target)
 best_after=min([distance(m,q,target) for q in descendants] or [best_before])
 target_improvement=max(0,best_before-best_after)
 # Simplification effect: descendants that orient as decreasing rules and rewrite at least one retained clause side.
 simplifications=0
 cp_gain=0
 for q in descendants:
  try:
   oriented=search.orient_rule(q)
  except Exception:oriented=None
  if oriented is not None:
   lhs,rhs=oriented[:2]
   for c in search.clauses:
    try:
     nl=search.rewrite_term(c.lhs,[(lhs,rhs)],search.limits['normalization_steps'])
     nr=search.rewrite_term(c.rhs,[(lhs,rhs)],search.limits['normalization_steps'])
    except Exception:continue
    if nl!=c.lhs or nr!=c.rhs:simplifications+=1
  # Critical-pair opportunity proxy: nonvariable overlap sites against current rules.
  for r in rules:
   try:
    cp_gain += sum(1 for _ in m.nonvariable_positions(q.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True))
    cp_gain += sum(1 for _ in m.nonvariable_positions(r.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True)) if q.lhs!=r.lhs else 0
   except Exception:pass
 score=(0, replayable, simplifications, cp_gain, target_improvement)
 return {'seed':seed,'descendants':descendants,'replayable_descendants':replayable,'simplifications':simplifications,
         'critical_pair_gains':cp_gain,'target_improvement':target_improvement,'probe_cp_attempts':cp_attempts,'score':score}

def run_arm(m, source, target, limits, mode, rnd):
 eng=m.TargetGroundedRefutation(source,target,time.monotonic()+WARM_SECONDS,dict(limits))
 initial=eng.search.solve(); initial_closed=False
 if initial is not None:
  try:
   rr=eng.inline_recipe(initial); cc=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+1,eng.search.limits);nodes,root=cc.compile(rr)
   initial_closed=((nodes[root].lhs,nodes[root].rhs)==eng.target[:2] and m.replay_dag(eng.source,nodes,root,maximum_term_size=eng.search.limits['maximum_replay_term_size'],maximum_nodes=eng.search.limits['maximum_proof_nodes']))
  except Exception:initial_closed=False
 base_keys={canon(m,c.lhs,c.rhs) for c in eng.search.clauses}
 # Candidate pool is deterministic and source/target-derived only: newest non-input clauses, bounded.
 pool=[(i,c) for i,c in enumerate(eng.search.clauses) if getattr(c,'kind','') not in ('input','symmetry')]
 pool=pool[-SEED_CANDIDATES:]
 metrics=[probe_seed(m,eng.search,c,i,target,base_keys) for i,c in pool]
 if mode=='developmental':
  # Lexicographic downstream productivity; closure would be first component if a local target close is observed later.
  ranked=sorted(metrics,key=lambda x:(x['replayable_descendants'],x['simplifications'],x['critical_pair_gains'],x['target_improvement']),reverse=True)
  chosen=ranked[:RETAIN]
 else:
  chosen=list(metrics);rnd.shuffle(chosen);chosen=chosen[:RETAIN]
 added=0
 for x in chosen:
  # Retain the productive descendants, not an oracle clause; cap total additions equally by arm.
  for q in x['descendants'][:max(1,DESC_LIMIT//RETAIN)]:
   if added>=DESC_LIMIT:break
   try:
    if eng.search.add_clause(q):added+=1
   except Exception:pass
 eng.search.deadline=time.monotonic()+CONT_SECONDS
 continuation=eng.search.solve()
 closed=False
 if continuation is not None:
  try:
   rr=eng.inline_recipe(continuation);cc=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+1,eng.search.limits);nodes,root=cc.compile(rr)
   closed=((nodes[root].lhs,nodes[root].rhs)==eng.target[:2] and m.replay_dag(eng.source,nodes,root,maximum_term_size=eng.search.limits['maximum_replay_term_size'],maximum_nodes=eng.search.limits['maximum_proof_nodes']))
  except Exception:closed=False
 # Requested metrics are totals over the retained seeds' bounded local continuations.
 return {'mode':mode,'initial_closure':bool(initial_closed),'closure':bool(closed),'retained':len(chosen),'added_descendants':added,
  'replayable_descendants':sum(x['replayable_descendants'] for x in chosen),
  'simplifications':sum(x['simplifications'] for x in chosen),
  'critical_pair_gains':sum(x['critical_pair_gains'] for x in chosen),
  'target_improvement':sum(x['target_improvement'] for x in chosen),
  'best_target_improvement':max([x['target_improvement'] for x in chosen] or [0]),
  'final_clauses':len(eng.search.clauses),'final_superpositions':eng.search.superpositions,
  'selected':[{'replayable_descendants':x['replayable_descendants'],'simplifications':x['simplifications'],'critical_pair_gains':x['critical_pair_gains'],'target_improvement':x['target_improvement']} for x in chosen]}

def main():
 m=loadm();rows={}
 for cfg in CFGS:
  for rr in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(rr)
   if r['id'] in IDS:rows[r['id']]=r
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 out={'schema':'mathgraph.developmental-continuation.v1','seed':SEED,'budgets':{'warm_seconds':WARM_SECONDS,'probe_seconds_per_seed':PROBE_SECONDS,'continuation_seconds':CONT_SECONDS,'seed_candidates':SEED_CANDIDATES,'retain':RETAIN,'desc_limit':DESC_LIMIT},'rows':[]}
 for k,rid in enumerate(IDS):
  row=rows[rid];src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2'])
  # Separate fresh engines; alternating arm order removes systematic warm-cache ordering bias.
  rnd=random.Random(SEED+k)
  order=['control','developmental'] if k%2==0 else ['developmental','control']
  rec={'id':rid,'arms':{}}
  for arm in order:rec['arms'][arm]=run_arm(m,src,tgt,limits,arm,rnd)
  c=rec['arms']['control'];d=rec['arms']['developmental']
  rec['delta']={x:d[x]-c[x] for x in ('replayable_descendants','simplifications','critical_pair_gains','target_improvement','best_target_improvement')}
  rec['delta']['closure']=int(d['closure'])-int(c['closure'])
  out['rows'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['summary']={'control_closures':sum(x['arms']['control']['closure'] for x in out['rows']),'developmental_closures':sum(x['arms']['developmental']['closure'] for x in out['rows']),
  'developmental_wins':[x['id'] for x in out['rows'] if x['arms']['developmental']['closure'] and not x['arms']['control']['closure']]}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out['summary'],indent=2))
if __name__=='__main__':main()

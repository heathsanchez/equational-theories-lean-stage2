#!/usr/bin/env python3
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
OUT=ROOT/'experiments/mathgraph/results/active-view-replacement-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_hard_0196','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_hard','evaluation_order5']
SECONDS=15.0
BACKWARD_PER_ROUND=256


def loadm():
 s=importlib.util.spec_from_file_location('mg_active_replace',SOLVER);m=importlib.util.module_from_spec(s);sys.modules[s.name]=m;s.loader.exec_module(m);return m

def replay_result(m,eng,recipe):
 if recipe is None:return False
 try:
  rr=eng.inline_recipe(recipe);cc=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+2.0,eng.search.limits);nodes,root=cc.compile(rr)
  return nodes[root].lhs==eng.target[0] and nodes[root].rhs==eng.target[1] and m.replay_dag(eng.source,nodes,root,maximum_term_size=eng.search.limits['maximum_replay_term_size'],maximum_nodes=eng.search.limits['maximum_proof_nodes'])
 except Exception:return False

def rebuild_active_signatures(search):
 search.signatures=set()
 for clause in search.clauses:
  search.signatures.add(search.alpha_signature(clause.lhs,clause.rhs))

def superposition_round(m,search,rules):
 snapshot=rules;proposals=[]
 for oi,outer in enumerate(snapshot):
  for ii,inner in enumerate(snapshot):
   for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
    if search.expired():return 0
    q=search.critical_pair(outer,inner,oi,ii,path)
    if q is None:continue
    q=search.interreduce(q,rules);proposals.append((search.target_score(q),q))
 proposals.sort(key=lambda x:x[0]);added=0
 for _,q in proposals:
  if search.add_clause(q):
   search.superpositions+=1;added+=1
   if added>=search.limits['new_clauses_per_round']:break
 return added

def additive_backward(search):
 new_rules=search.rules();original=list(search.clauses);retro=[];attempted=0
 for clause in original:
  if search.expired() or len(retro)>=BACKWARD_PER_ROUND:break
  attempted+=1;reduced=search.interreduce(clause,new_rules)
  if reduced.lhs==clause.lhs and reduced.rhs==clause.rhs:continue
  retro.append((search.target_score(reduced),reduced))
 retro.sort(key=lambda x:x[0]);added=0
 for _,q in retro:
  if search.add_clause(q):added+=1
  if added>=BACKWARD_PER_ROUND:break
 return attempted,added,0

def active_replace(search):
 # Immutable proof history is preserved through Recipe parent pointers.
 # Only the active inference view (search.clauses) is rewritten.
 new_rules=search.rules();old=list(search.clauses);next_active=[];seen=set();attempted=0;replaced=0;dropped_dupes=0
 for clause in old:
  if search.expired():
   next_active.append(clause);continue
  attempted+=1
  reduced=search.interreduce(clause,new_rules)
  candidate=reduced if (reduced.lhs!=clause.lhs or reduced.rhs!=clause.rhs) else clause
  if candidate is not clause:replaced+=1
  sig=search.alpha_signature(candidate.lhs,candidate.rhs);rev=search.alpha_signature(candidate.rhs,candidate.lhs)
  if sig in seen or rev in seen:
   dropped_dupes+=1;continue
  seen.add(sig);next_active.append(candidate)
 # This is the intervention: superseded clauses leave the active agenda.
 search.clauses=next_active
 rebuild_active_signatures(search)
 return attempted,replaced,dropped_dupes

def solve_mode(m,search,mode):
 attempts=changes=dropped=0
 for round_index in range(search.limits['maximum_rounds']):
  search.rounds=round_index+1
  rules=search.rules();goal=search.target_proof(rules)
  if goal is not None:return goal,attempts,changes,dropped
  added=superposition_round(m,search,rules)
  if search.expired():return None,attempts,changes,dropped
  delta=0
  if mode=='additive':
   a,c,d=additive_backward(search);attempts+=a;changes+=c;dropped+=d;delta=c
  elif mode=='replace':
   a,c,d=active_replace(search);attempts+=a;changes+=c;dropped+=d;delta=c
  if (not added and not delta) or len(search.clauses)>=search.limits['maximum_clauses']:break
 return search.target_proof(search.rules()),attempts,changes,dropped

def run(m,source,target,mode):
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':SECONDS,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 eng=m.TargetGroundedRefutation(source,target,time.monotonic()+SECONDS,limits)
 if mode=='baseline':
  recipe=eng.search.solve();attempts=changes=dropped=0
 else:
  recipe,attempts,changes,dropped=solve_mode(m,eng.search,mode)
 return {'closure':replay_result(m,eng,recipe),'active_clauses':len(eng.search.clauses),'rules':len(eng.search.rules()),'rounds':eng.search.rounds,'superpositions':eng.search.superpositions,'reductions':eng.search.reductions,'rewrite_attempts':attempts,'active_rewrites_or_additions':changes,'retired_duplicate_views':dropped}

def main():
 m=loadm();rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 out={'schema':'mathgraph.active-view-replacement-gate.v1','seconds':SECONDS,'backward_per_round':BACKWARD_PER_ROUND,'arms':['baseline','additive','replace'],'rows':[]}
 orders=[['baseline','additive','replace'],['replace','baseline','additive'],['additive','replace','baseline']]
 for k,rid in enumerate(IDS):
  r=rows[rid];src=m.parse_equation(r['equation1']);tgt=m.parse_equation(r['equation2']);arms={}
  for arm in orders[k%3]:arms[arm]=run(m,src,tgt,arm)
  rec={'id':rid,'arms':arms,'replace_gain':bool(arms['replace']['closure'] and not arms['baseline']['closure']),'replace_over_additive':bool(arms['replace']['closure'] and not arms['additive']['closure'])};out['rows'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['summary']={a+'_closures':sum(x['arms'][a]['closure'] for x in out['rows']) for a in out['arms']}
 out['summary']['replace_gains']=[x['id'] for x in out['rows'] if x['replace_gain']]
 out['summary']['replace_over_additive']=[x['id'] for x in out['rows'] if x['replace_over_additive']]
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out['summary'],indent=2,sort_keys=True))
if __name__=='__main__':main()

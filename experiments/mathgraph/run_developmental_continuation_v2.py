#!/usr/bin/env python3
import importlib.util,json,random,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]; SOLVER=ROOT/'submissions/mathgraph/solver.py'; OUT=ROOT/'experiments/mathgraph/results/developmental-continuation-v2.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_hard_0196','evaluation_order5_0014','evaluation_order5_0042']; CFGS=['evaluation_normal','evaluation_hard','evaluation_order5']
SEED=20260820; WARM=4.0; PROBE=.035; CONT=4.0; SEEDS=24; RETAIN=4; DESC_LIMIT=96

def loadm():
 s=importlib.util.spec_from_file_location('mg_v2',SOLVER);m=importlib.util.module_from_spec(s);sys.modules[s.name]=m;s.loader.exec_module(m);return m
def canon(m,a,b):return tuple(sorted((m.render_term(a),m.render_term(b))))
def dist(m,q,t):return min(m.structural_distance(q.lhs,t[0])+m.structural_distance(q.rhs,t[1]),m.structural_distance(q.lhs,t[1])+m.structural_distance(q.rhs,t[0]))
def replay_close(m,e,r):
 if r is None:return False
 try:
  r=e.inline_recipe(r);c=m.CompactSuperposition(m,e.source,e.target,time.monotonic()+1,e.search.limits);n,root=c.compile(r)
  return (n[root].lhs,n[root].rhs)==e.target[:2] and m.replay_dag(e.source,n,root,maximum_term_size=e.search.limits['maximum_replay_term_size'],maximum_nodes=e.search.limits['maximum_proof_nodes'])
 except Exception:return False

def probe(m,s,seed,idx,target,base):
 started=time.monotonic();rules=list(s.rules());desc=[];seen=set();cp_attempts=0
 for outer,inner,oi,ii in [(seed,r,idx,j) for j,r in enumerate(rules)]+[(r,seed,j,idx) for j,r in enumerate(rules)]:
  if time.monotonic()-started>=PROBE or len(desc)>=DESC_LIMIT:break
  for path in m.nonvariable_positions(outer.lhs,maximum_depth=s.limits['maximum_depth'],include_root=True):
   if time.monotonic()-started>=PROBE:break
   cp_attempts+=1
   try:q=s.critical_pair(outer,inner,oi,ii,path)
   except Exception:q=None
   if q is None:continue
   try:q=s.interreduce(q,rules)
   except Exception:pass
   k=canon(m,q.lhs,q.rhs)
   if k in base or k in seen:continue
   seen.add(k);desc.append(q)
   if len(desc)>=DESC_LIMIT:break
 before=dist(m,seed,target); dists=[dist(m,q,target) for q in desc]; best=min(dists or [before]); improvement=max(0,before-best)
 orientable=0;simpl=0;relevant_cp=0
 for q,qd in zip(desc,dists):
  try:o=s.orient_rule(q)
  except Exception:o=None
  if o is not None:
   orientable+=1;lhs,rhs=o[:2]
   for c in s.clauses:
    try:
     nl=s.rewrite_term(c.lhs,[(lhs,rhs)],s.limits['normalization_steps']);nr=s.rewrite_term(c.rhs,[(lhs,rhs)],s.limits['normalization_steps'])
    except Exception:continue
    if nl!=c.lhs or nr!=c.rhs:simpl+=1
  if qd<=before:
   try:sites=sum(1 for _ in m.nonvariable_positions(q.lhs,maximum_depth=s.limits['maximum_depth'],include_root=True))
   except Exception:sites=0
   relevant_cp += sites*len(rules)
 return {'seed':seed,'desc':desc,'replayable':len(desc),'simplifications':simpl,'orientable':orientable,'relevant_cp':relevant_cp,'target_improvement':improvement,'best_distance':best,'probe_cp_attempts':cp_attempts}

def choose(metrics,mode,rnd):
 if mode=='control':x=list(metrics);rnd.shuffle(x);return x[:RETAIN]
 if mode=='v1':return sorted(metrics,key=lambda x:(x['replayable'],x['simplifications'],x['relevant_cp'],x['target_improvement']),reverse=True)[:RETAIN]
 # closure proxy cannot be known without compile; rank convergence/rewrite first, raw abundance last.
 return sorted(metrics,key=lambda x:(x['simplifications'],x['orientable'],x['relevant_cp'],x['target_improvement'],x['replayable']),reverse=True)[:RETAIN]

def arm(m,source,target,limits,mode,rnd):
 e=m.TargetGroundedRefutation(source,target,time.monotonic()+WARM,dict(limits));r=e.search.solve();initial=replay_close(m,e,r)
 base={canon(m,c.lhs,c.rhs) for c in e.search.clauses};pool=[(i,c) for i,c in enumerate(e.search.clauses) if getattr(c,'kind','') not in ('input','symmetry')][-SEEDS:]
 metrics=[probe(m,e.search,c,i,target,base) for i,c in pool];chosen=choose(metrics,mode,rnd);added=0
 for x in chosen:
  for q in x['desc'][:max(1,DESC_LIMIT//RETAIN)]:
   if added>=DESC_LIMIT:break
   try:
    if e.search.add_clause(q):added+=1
   except Exception:pass
 e.search.deadline=time.monotonic()+CONT;r=e.search.solve();closed=replay_close(m,e,r)
 return {'mode':mode,'initial_closure':initial,'closure':closed,'retained':len(chosen),'added_descendants':added,'replayable_descendants':sum(x['replayable'] for x in chosen),'simplifications':sum(x['simplifications'] for x in chosen),'orientable_descendants':sum(x['orientable'] for x in chosen),'target_relevant_cp':sum(x['relevant_cp'] for x in chosen),'target_improvement':sum(x['target_improvement'] for x in chosen),'best_target_improvement':max([x['target_improvement'] for x in chosen] or [0]),'final_clauses':len(e.search.clauses),'final_superpositions':e.search.superpositions}

def main():
 m=loadm();rows={}
 for cfg in CFGS:
  for rr in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(rr)
   if r['id'] in IDS:rows[r['id']]=r
 lim=dict(m.COMPACT_SUPERPOSITION_PROBE);lim.update({'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 out={'schema':'mathgraph.developmental-continuation.v2','seed':SEED,'rows':[]}
 for k,rid in enumerate(IDS):
  src=m.parse_equation(rows[rid]['equation1']);tgt=m.parse_equation(rows[rid]['equation2']);rnd=random.Random(SEED+k);rec={'id':rid,'arms':{}}
  order=['control','v1','v2'] if k%2==0 else ['v2','v1','control']
  for mode in order:rec['arms'][mode]=arm(m,src,tgt,lim,mode,rnd)
  out['rows'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['summary']={x+'_closures':sum(r['arms'][x]['closure'] for r in out['rows']) for x in ('control','v1','v2')};out['summary']['v2_unique_wins']=[r['id'] for r in out['rows'] if r['arms']['v2']['closure'] and not r['arms']['control']['closure'] and not r['arms']['v1']['closure']]
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out['summary'],indent=2))
if __name__=='__main__':main()

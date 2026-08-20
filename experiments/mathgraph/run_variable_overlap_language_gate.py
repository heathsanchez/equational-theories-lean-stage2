#!/usr/bin/env python3
"""Generic language escalation: admit variable-position overlaps as replay-gated proof continuations."""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
GATE=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py'
OUT=ROOT/'experiments/mathgraph/results/variable-overlap-language-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']
SECONDS=8.0

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def engine(m,row):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2'])
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':SECONDS,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':384,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 return m.TargetGroundedRefutation(src,tgt,time.monotonic()+SECONDS,limits)

def replay(m,e,r):
 if r is None:return False
 try:
  rr=e.inline_recipe(r);cc=m.CompactSuperposition(m,e.source,e.target,time.monotonic()+2,e.search.limits);nodes,root=cc.compile(rr)
  return bool(nodes[root].lhs==e.target[0] and nodes[root].rhs==e.target[1] and m.replay_dag(e.source,nodes,root,maximum_term_size=e.search.limits['maximum_replay_term_size'],maximum_nodes=e.search.limits['maximum_proof_nodes']))
 except Exception:return False

def sym(m,c):return m.Recipe(c.rhs,c.lhs,'symmetry',parents=(c,))
def views(m,c):return (c,sym(m,c)) if c.lhs!=c.rhs else (c,)

def all_positions(term,depth,path=()):
 yield path
 if depth<=0 or term[0]!='op':return
 yield from all_positions(term[1],depth-1,path+('L',))
 yield from all_positions(term[2],depth-1,path+('R',))

def solve(m,gate,search):
 passive=list(search.clauses);active=[];age={id(c):i for i,c in enumerate(passive)};next_age=len(passive)
 given=generated=backward=attempts=variable_attempts=0
 while passive and given<384 and not search.expired():
  rules=gate.active_rules(search,active);goal=search.target_proof(rules)
  if goal is not None:return goal,locals_stats()
  idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
  selected=passive.pop(idx);r=search.interreduce(selected,rules)
  if r.lhs!=selected.lhs or r.rhs!=selected.rhs:selected=r
  active.append(selected);given+=1;rules=gate.active_rules(search,active)
  goal=search.target_proof(rules)
  if goal is not None:return goal,locals_stats()
  proposals=[]
  for oi,other in enumerate(active):
   for sv in views(m,selected):
    for ov in views(m,other):
     for outer,inner,a,b in ((sv,ov,given,oi),(ov,sv,oi,given)):
      for path in all_positions(outer.lhs,search.limits['maximum_depth']):
       if search.expired():break
       attempts+=1
       if m.get_subterm(outer.lhs,path)[0]=='var':variable_attempts+=1
       q=search.critical_pair(outer,inner,a,b,path)
       if q is None:continue
       q=search.interreduce(q,rules)
       if q.lhs==q.rhs:continue
       proposals.append((search.target_score(q),q))
  proposals.sort(key=lambda x:x[0])
  for _,q in proposals[:search.limits['new_clauses_per_round']]:
   if search.add_clause(q):search.superpositions+=1;generated+=1;passive.append(q);age[id(q)]=next_age;next_age+=1
  new=[];seen=set()
  for c in passive:
   if search.expired():break
   r=search.interreduce(c,rules)
   if r.lhs!=c.lhs or r.rhs!=c.rhs:backward+=1;c=r
   k=gate.key_clause(m,c)
   if k in seen:continue
   seen.add(k);new.append(c)
  passive=new
 def locals_stats():
  return {'given':given,'generated':generated,'backward_replaced':backward,'pair_attempts':attempts,'variable_attempts':variable_attempts,'active':len(active),'passive':len(passive)}
 return search.target_proof(gate.active_rules(search,active)),locals_stats()

def main():
 m=load(SOLVER,'mg_var');gate=load(GATE,'gate_var');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 recs=[]
 for rid in IDS:
  e=engine(m,rows[rid]);t=time.monotonic();recipe,stats=solve(m,gate,e.search);ok=replay(m,e,recipe)
  rec={'id':rid,'mode':'variable-overlap-language','closure':ok,'seconds':round(time.monotonic()-t,6),'stats':stats};recs.append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out={'schema':'mathgraph.variable-overlap-language.v1','seconds':SECONDS,'records':recs,'gains':[r['id'] for r in recs if r['closure']]}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'gains':out['gains']},indent=2))
if __name__=='__main__':main()

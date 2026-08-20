#!/usr/bin/env python3
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
BASE=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py'
OUT=ROOT/'experiments/mathgraph/results/given-clause-retention-policy-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']
POLICIES=['replace','delay16','keep_both','none']
SECONDS=8.0

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def engine(m,row):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2'])
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':SECONDS,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':1024,'new_clauses_per_round':384,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 return m.TargetGroundedRefutation(src,tgt,time.monotonic()+SECONDS,limits)

def replay(m,e,r):
 if r is None:return False
 try:
  rr=e.inline_recipe(r);cc=m.CompactSuperposition(m,e.source,e.target,time.monotonic()+2,e.search.limits);nodes,root=cc.compile(rr)
  return nodes[root].lhs==e.target[0] and nodes[root].rhs==e.target[1] and m.replay_dag(e.source,nodes,root,maximum_term_size=e.search.limits['maximum_replay_term_size'],maximum_nodes=e.search.limits['maximum_proof_nodes'])
 except Exception:return False

def solve(m,g,search,policy):
 passive=list(search.clauses);active=[];age={id(c):i for i,c in enumerate(passive)};nxt=len(passive);given=generated=backward=attempts=0
 while passive and given<384 and not search.expired():
  rules=g.active_rules(search,active);goal=search.target_proof(rules)
  if goal is not None:break
  idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
  selected=passive.pop(idx);r=search.interreduce(selected,rules)
  if r.lhs!=selected.lhs or r.rhs!=selected.rhs:selected=r
  active.append(selected);given+=1;rules=g.active_rules(search,active)
  proposals=[]
  for oi,other in enumerate(active):
   for outer,inner,a,b in ((selected,other,given,oi),(other,selected,oi,given)):
    for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
     if search.expired():break
     attempts+=1;q=search.critical_pair(outer,inner,a,b,path)
     if q is not None:proposals.append((search.target_score(q),search.interreduce(q,rules)))
  proposals.sort(key=lambda x:x[0])
  for _,q in proposals[:search.limits['new_clauses_per_round']]:
   if search.add_clause(q):search.superpositions+=1;generated+=1;passive.append(q);age[id(q)]=nxt;nxt+=1
  do=policy in ('replace','keep_both') or (policy=='delay16' and given%16==0)
  new=[];seen=set()
  for c in passive:
   cs=[c]
   if do:
    r=search.interreduce(c,rules)
    if r.lhs!=c.lhs or r.rhs!=c.rhs:
     backward+=1
     cs=[r] if policy in ('replace','delay16') else [c,r]
   for z in cs:
    k=g.key_clause(m,z)
    if k not in seen:seen.add(k);new.append(z)
  passive=new
 goal=search.target_proof(g.active_rules(search,active))
 return goal,{'given':given,'generated':generated,'backward_replaced':backward,'pair_attempts':attempts,'active':len(active),'passive':len(passive)}

def main():
 m=load(SOLVER,'mg_retention');g=load(BASE,'gate_retention');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 recs=[]
 for rid in IDS:
  for p in POLICIES:
   e=engine(m,rows[rid]);t=time.monotonic();r,st=solve(m,g,e.search,p);ok=replay(m,e,r)
   rec={'id':rid,'policy':p,'closure':ok,'seconds':round(time.monotonic()-t,6),'stats':st};recs.append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 gains={rid:[x['policy'] for x in recs if x['id']==rid and x['closure']] for rid in IDS}
 out={'schema':'mathgraph.given-clause-retention-policy.v1','records':recs,'gains':gains};OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(gains,indent=2,sort_keys=True))
if __name__=='__main__':main()

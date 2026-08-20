#!/usr/bin/env python3
"""Frozen follow-up: selector sweep for live-frontier residual and bidirectional-clause escalation for exhausted residuals."""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
GATE=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py'
OUT=ROOT/'experiments/mathgraph/results/residual-regime-escalation-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']
SECONDS=8.0

def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m

def replay(m,eng,recipe):
 if recipe is None:return False
 try:
  rr=eng.inline_recipe(recipe);cc=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+2.0,eng.search.limits);nodes,root=cc.compile(rr)
  return bool(nodes[root].lhs==eng.target[0] and nodes[root].rhs==eng.target[1] and m.replay_dag(eng.source,nodes,root,maximum_term_size=eng.search.limits['maximum_replay_term_size'],maximum_nodes=eng.search.limits['maximum_proof_nodes']))
 except Exception:return False

def engine(m,row):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2'])
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':SECONDS,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':384,'maximum_clauses':10000,'normalization_steps':256,'maximum_proof_nodes':50000})
 return m.TargetGroundedRefutation(src,tgt,time.monotonic()+SECONDS,limits)

def symmetry(m,c):
 return m.Recipe(c.rhs,c.lhs,'symmetry',parents=(c,))

def dir_key(m,c):
 names={};return (m.alpha_canonical_term(c.lhs,names),m.alpha_canonical_term(c.rhs,names))

def solve_bidirectional(m,gate,search):
 passive=[]
 for c in search.clauses:
  passive.append(c);passive.append(symmetry(m,c))
 active=[];age={id(c):i for i,c in enumerate(passive)};next_age=len(passive)
 given=generated=backward_replaced=pair_attempts=0
 while passive and given<384 and not search.expired():
  rules=gate.active_rules(search,active);goal=search.target_proof(rules)
  if goal is not None:return goal,dict(given=given,generated=generated,backward_replaced=backward_replaced,pair_attempts=pair_attempts,active=len(active),passive=len(passive))
  idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
  selected=passive.pop(idx);reduced=search.interreduce(selected,rules)
  if reduced.lhs!=selected.lhs or reduced.rhs!=selected.rhs:selected=reduced
  active.append(selected);given+=1;rules=gate.active_rules(search,active)
  goal=search.target_proof(rules)
  if goal is not None:return goal,dict(given=given,generated=generated,backward_replaced=backward_replaced,pair_attempts=pair_attempts,active=len(active),passive=len(passive))
  proposals=[]
  for oi,other in enumerate(active):
   for outer,inner,a,b in ((selected,other,given,oi),(other,selected,oi,given)):
    for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
     if search.expired():break
     pair_attempts+=1;q=search.critical_pair(outer,inner,a,b,path)
     if q is None:continue
     q=search.interreduce(q,rules);proposals.append((search.target_score(q),q))
  proposals.sort(key=lambda x:x[0])
  for _,q in proposals[:search.limits['new_clauses_per_round']]:
   if search.add_clause(q):
    search.superpositions+=1;generated+=1
    for z in (q,symmetry(m,q)):
     passive.append(z);age[id(z)]=next_age;next_age+=1
  new=[];seen=set()
  for c in passive:
   if search.expired():break
   r=search.interreduce(c,rules)
   if r.lhs!=c.lhs or r.rhs!=c.rhs:backward_replaced+=1;c=r
   k=dir_key(m,c)
   if k in seen:continue
   seen.add(k);new.append(c)
  passive=new
 return search.target_proof(gate.active_rules(search,active)),dict(given=given,generated=generated,backward_replaced=backward_replaced,pair_attempts=pair_attempts,active=len(active),passive=len(passive))

def main():
 m=load(SOLVER,'mg_regime');gate=load(GATE,'given_regime');rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 records=[]
 row=rows['evaluation_normal_0036']
 for focus in [1,2,4,8,16]:
  gate.FOCUS_PER_AGE=focus;gate.MAX_GIVEN=1024;e=engine(m,row);t=time.monotonic();recipe,stats=gate.solve_given(m,e.search);ok=replay(m,e,recipe)
  rec={'id':row['id'],'mode':'selector','focus_per_age':focus,'closure':ok,'seconds':round(time.monotonic()-t,6),'stats':stats};records.append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
  if ok:break
 for rid in ['evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']:
  e=engine(m,rows[rid]);t=time.monotonic();recipe,stats=solve_bidirectional(m,gate,e.search);ok=replay(m,e,recipe)
  rec={'id':rid,'mode':'bidirectional-language','closure':ok,'seconds':round(time.monotonic()-t,6),'stats':stats};records.append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out={'schema':'mathgraph.residual-regime-escalation.v1','seconds':SECONDS,'records':records,'gains':[r['id'] for r in records if r['closure']]}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'gains':out['gains']},indent=2))

if __name__=='__main__':main()

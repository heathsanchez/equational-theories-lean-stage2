#!/usr/bin/env python3
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
OUT=ROOT/'experiments/mathgraph/results/given-clause-saturation-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_hard_0196','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_hard','evaluation_order5']
SECONDS=15.0
MAX_GIVEN=512
FOCUS_PER_AGE=4


def loadm():
 s=importlib.util.spec_from_file_location('mg_given',SOLVER);m=importlib.util.module_from_spec(s);sys.modules[s.name]=m;s.loader.exec_module(m);return m

def replay_result(m,eng,recipe):
 if recipe is None:return False
 try:
  rr=eng.inline_recipe(recipe);cc=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+2.0,eng.search.limits);nodes,root=cc.compile(rr)
  return nodes[root].lhs==eng.target[0] and nodes[root].rhs==eng.target[1] and m.replay_dag(eng.source,nodes,root,maximum_term_size=eng.search.limits['maximum_replay_term_size'],maximum_nodes=eng.search.limits['maximum_proof_nodes'])
 except Exception:return False

def active_rules(search,active):
 out=[]
 for clause in active:
  rule=search.orient(clause)
  if rule is not None:out.append(rule)
 return out

def canonical_pair(m,lhs,rhs):
 names={};return (m.alpha_canonical_term(lhs,names),m.alpha_canonical_term(rhs,names))

def key_clause(m,c):
 return min(canonical_pair(m,c.lhs,c.rhs),canonical_pair(m,c.rhs,c.lhs))

def solve_given(m,search):
 passive=list(search.clauses);active=[];age={id(c):i for i,c in enumerate(passive)};next_age=len(passive)
 given=0;generated=0;backward_replaced=0;pair_attempts=0
 while passive and given<MAX_GIVEN and not search.expired():
  rules=active_rules(search,active)
  goal=search.target_proof(rules)
  if goal is not None:return goal,dict(given=given,generated=generated,backward_replaced=backward_replaced,pair_attempts=pair_attempts,active=len(active),passive=len(passive))
  if given%(FOCUS_PER_AGE+1)==FOCUS_PER_AGE:
   idx=min(range(len(passive)),key=lambda i:age.get(id(passive[i]),10**18))
  else:
   idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
  selected=passive.pop(idx)
  reduced=search.interreduce(selected,rules)
  if reduced.lhs!=selected.lhs or reduced.rhs!=selected.rhs:
   search.add_clause(reduced);selected=reduced
  active.append(selected);given+=1
  rules=active_rules(search,active)
  goal=search.target_proof(rules)
  if goal is not None:return goal,dict(given=given,generated=generated,backward_replaced=backward_replaced,pair_attempts=pair_attempts,active=len(active),passive=len(passive))
  proposals=[]
  for other_index,other in enumerate(active):
   for outer,inner,oi,ii in ((selected,other,given,other_index),(other,selected,other_index,given)):
    for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
     if search.expired():break
     pair_attempts+=1
     q=search.critical_pair(outer,inner,oi,ii,path)
     if q is None:continue
     q=search.interreduce(q,rules);proposals.append((search.target_score(q),q))
  proposals.sort(key=lambda x:x[0])
  for _,q in proposals[:search.limits['new_clauses_per_round']]:
   if search.add_clause(q):
    search.superpositions+=1;generated+=1;passive.append(q);age[id(q)]=next_age;next_age+=1
  new_passive=[];seen=set()
  for clause in passive:
   if search.expired():break
   reduced=search.interreduce(clause,rules)
   if reduced.lhs!=clause.lhs or reduced.rhs!=clause.rhs:
    backward_replaced+=1
    if search.add_clause(reduced):age[id(reduced)]=age.get(id(clause),next_age);next_age+=1
    clause=reduced
   k=key_clause(m,clause)
   if k in seen:continue
   seen.add(k);new_passive.append(clause)
  passive=new_passive
 return search.target_proof(active_rules(search,active)),dict(given=given,generated=generated,backward_replaced=backward_replaced,pair_attempts=pair_attempts,active=len(active),passive=len(passive))

def run(m,source,target,mode):
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':SECONDS,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 eng=m.TargetGroundedRefutation(source,target,time.monotonic()+SECONDS,limits)
 if mode=='baseline':
  recipe=eng.search.solve();stats={'given':0,'generated':0,'backward_replaced':0,'pair_attempts':0,'active':len(eng.search.clauses),'passive':0}
 else:recipe,stats=solve_given(m,eng.search)
 out={'closure':replay_result(m,eng,recipe),'clauses':len(eng.search.clauses),'rules':len(eng.search.rules()),'rounds':eng.search.rounds,'superpositions':eng.search.superpositions,'reductions':eng.search.reductions};out.update(stats);return out

def main():
 m=loadm();rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 out={'schema':'mathgraph.given-clause-saturation-gate.v1','seconds':SECONDS,'max_given':MAX_GIVEN,'focus_per_age':FOCUS_PER_AGE,'rows':[]}
 for k,rid in enumerate(IDS):
  r=rows[rid];src=m.parse_equation(r['equation1']);tgt=m.parse_equation(r['equation2']);arms={}
  order=['baseline','given'] if k%2==0 else ['given','baseline']
  for arm in order:arms[arm]=run(m,src,tgt,arm)
  rec={'id':rid,'arms':arms,'gain':bool(arms['given']['closure'] and not arms['baseline']['closure'])};out['rows'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['summary']={'baseline_closures':sum(x['arms']['baseline']['closure'] for x in out['rows']),'given_closures':sum(x['arms']['given']['closure'] for x in out['rows']),'gains':[x['id'] for x in out['rows'] if x['gain']]}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out['summary'],indent=2,sort_keys=True))
if __name__=='__main__':main()

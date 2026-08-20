#!/usr/bin/env python3
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
OUT=ROOT/'experiments/mathgraph/results/given-clause-memoization-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_hard_0196','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_hard','evaluation_order5']
SECONDS=15.0
MAX_GIVEN=1024
FOCUS_PER_AGE=4

def loadm():
 s=importlib.util.spec_from_file_location('mg_memo',SOLVER);m=importlib.util.module_from_spec(s);sys.modules[s.name]=m;s.loader.exec_module(m);return m

def canonical_pair(m,lhs,rhs):
 names={};return (m.alpha_canonical_term(lhs,names),m.alpha_canonical_term(rhs,names))

def key_clause(m,c):return min(canonical_pair(m,c.lhs,c.rhs),canonical_pair(m,c.rhs,c.lhs))

def key_rule(m,r):return canonical_pair(m,r[0],r[1]) if isinstance(r,tuple) else canonical_pair(m,r.lhs,r.rhs)

def active_rules(search,active):
 out=[]
 for clause in active:
  rule=search.orient(clause)
  if rule is not None:out.append(rule)
 return out

def replay_result(m,eng,recipe):
 if recipe is None:return False
 try:
  rr=eng.inline_recipe(recipe);cc=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+2.0,eng.search.limits);nodes,root=cc.compile(rr)
  return nodes[root].lhs==eng.target[0] and nodes[root].rhs==eng.target[1] and m.replay_dag(eng.source,nodes,root,maximum_term_size=eng.search.limits['maximum_replay_term_size'],maximum_nodes=eng.search.limits['maximum_proof_nodes'])
 except Exception:return False

def solve_given(m,search,memoized):
 passive=list(search.clauses);active=[];age={id(c):i for i,c in enumerate(passive)};next_age=len(passive)
 given=generated=backward_replaced=pair_attempts=pair_cache_hits=interreduce_cache_hits=0
 pair_seen=set();reduce_cache={}
 def ir(clause,rules):
  nonlocal interreduce_cache_hits
  if not memoized:return search.interreduce(clause,rules)
  # Cache only no-op interreductions. Reusing a changed recipe would reuse the
  # wrong proof parent; a no-op is provenance-neutral and therefore safe.
  rf=tuple(sorted(key_rule(m,r) for r in rules))
  ck=(key_clause(m,clause),rf)
  if ck in reduce_cache:
   interreduce_cache_hits+=1
   return clause
  reduced=search.interreduce(clause,rules)
  if reduced.lhs==clause.lhs and reduced.rhs==clause.rhs:reduce_cache[ck]=True
  return reduced
 while passive and given<MAX_GIVEN and not search.expired():
  rules=active_rules(search,active);goal=search.target_proof(rules)
  if goal is not None:break
  if given%(FOCUS_PER_AGE+1)==FOCUS_PER_AGE:idx=min(range(len(passive)),key=lambda i:age.get(id(passive[i]),10**18))
  else:idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
  selected=passive.pop(idx);reduced=ir(selected,rules)
  if reduced.lhs!=selected.lhs or reduced.rhs!=selected.rhs:search.add_clause(reduced);selected=reduced
  active.append(selected);given+=1;rules=active_rules(search,active);goal=search.target_proof(rules)
  if goal is not None:break
  proposals=[]
  for other_index,other in enumerate(active):
   for outer,inner,oi,ii in ((selected,other,given,other_index),(other,selected,other_index,given)):
    ok=key_clause(m,outer);ik=key_clause(m,inner)
    for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
     if search.expired():break
     pair_attempts+=1
     pk=(ok,ik,tuple(path))
     if memoized and pk in pair_seen:
      pair_cache_hits+=1;continue
     if memoized:pair_seen.add(pk)
     q=search.critical_pair(outer,inner,oi,ii,path)
     if q is None:continue
     q=ir(q,rules);proposals.append((search.target_score(q),q))
  proposals.sort(key=lambda x:x[0])
  for _,q in proposals[:search.limits['new_clauses_per_round']]:
   if search.add_clause(q):
    search.superpositions+=1;generated+=1;passive.append(q);age[id(q)]=next_age;next_age+=1
  new_passive=[];seen=set()
  for clause in passive:
   if search.expired():break
   reduced=ir(clause,rules)
   if reduced.lhs!=clause.lhs or reduced.rhs!=clause.rhs:
    backward_replaced+=1
    if search.add_clause(reduced):age[id(reduced)]=age.get(id(clause),next_age);next_age+=1
    clause=reduced
   k=key_clause(m,clause)
   if k in seen:continue
   seen.add(k);new_passive.append(clause)
  passive=new_passive
 goal=search.target_proof(active_rules(search,active))
 return goal,dict(given=given,generated=generated,backward_replaced=backward_replaced,pair_attempts=pair_attempts,pair_cache_hits=pair_cache_hits,interreduce_cache_hits=interreduce_cache_hits,active=len(active),passive=len(passive))

def run(m,source,target,memoized):
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':SECONDS,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 eng=m.TargetGroundedRefutation(source,target,time.monotonic()+SECONDS,limits);recipe,stats=solve_given(m,eng.search,memoized)
 out={'closure':replay_result(m,eng,recipe),'clauses':len(eng.search.clauses),'rules':len(eng.search.rules()),'superpositions':eng.search.superpositions,'reductions':eng.search.reductions};out.update(stats);return out

def main():
 m=loadm();rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 out={'schema':'mathgraph.given-clause-memoization-gate.v1','seconds':SECONDS,'max_given':MAX_GIVEN,'rows':[]}
 for k,rid in enumerate(IDS):
  r=rows[rid];src=m.parse_equation(r['equation1']);tgt=m.parse_equation(r['equation2']);arms={}
  order=['plain','memo'] if k%2==0 else ['memo','plain']
  for arm in order:arms[arm]=run(m,src,tgt,arm=='memo')
  rec={'id':rid,'arms':arms,'memo_gain':bool(arms['memo']['closure'] and not arms['plain']['closure'])};out['rows'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['summary']={'plain_closures':sum(x['arms']['plain']['closure'] for x in out['rows']),'memo_closures':sum(x['arms']['memo']['closure'] for x in out['rows']),'memo_gains':[x['id'] for x in out['rows'] if x['memo_gain']],'pair_cache_hits':sum(x['arms']['memo']['pair_cache_hits'] for x in out['rows']),'interreduce_cache_hits':sum(x['arms']['memo']['interreduce_cache_hits'] for x in out['rows'])}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out['summary'],indent=2,sort_keys=True))
if __name__=='__main__':main()

#!/usr/bin/env python3
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
OUT=ROOT/'experiments/mathgraph/results/backward-demodulation-gate.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_hard_0196','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_hard','evaluation_order5']
SECONDS=15.0
BACKWARD_PER_ROUND=256


def loadm():
 s=importlib.util.spec_from_file_location('mg_backdemod',SOLVER);m=importlib.util.module_from_spec(s);sys.modules[s.name]=m;s.loader.exec_module(m);return m

def replay_result(m,eng,recipe):
 if recipe is None:return False
 try:
  rr=eng.inline_recipe(recipe);cc=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+2.0,eng.search.limits);nodes,root=cc.compile(rr)
  return nodes[root].lhs==eng.target[0] and nodes[root].rhs==eng.target[1] and m.replay_dag(eng.source,nodes,root,maximum_term_size=eng.search.limits['maximum_replay_term_size'],maximum_nodes=eng.search.limits['maximum_proof_nodes'])
 except Exception:return False

def solve_backward(m,search):
 backward_added=0;backward_attempted=0
 for round_index in range(search.limits['maximum_rounds']):
  search.rounds=round_index+1
  rules=search.rules();goal=search.target_proof(rules)
  if goal is not None:return goal,backward_attempted,backward_added
  snapshot=rules;proposals=[]
  for oi,outer in enumerate(snapshot):
   for ii,inner in enumerate(snapshot):
    for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
     if search.expired():return None,backward_attempted,backward_added
     q=search.critical_pair(outer,inner,oi,ii,path)
     if q is None:continue
     q=search.interreduce(q,rules);proposals.append((search.target_score(q),q))
  proposals.sort(key=lambda x:x[0]);added=0
  for _,q in proposals:
   if search.add_clause(q):
    search.superpositions+=1;added+=1
    if added>=search.limits['new_clauses_per_round']:break
  # Key intervention: rules learned this round may simplify clauses retained earlier.
  # Keep originals for proof safety; add replayable simplified descendants and let
  # them participate in the next ordinary superposition generation.
  new_rules=search.rules();original=list(search.clauses);retro=[]
  for clause in original:
   if search.expired() or len(retro)>=BACKWARD_PER_ROUND:break
   backward_attempted+=1
   reduced=search.interreduce(clause,new_rules)
   if reduced.lhs==clause.lhs and reduced.rhs==clause.rhs:continue
   retro.append((search.target_score(reduced),reduced))
  retro.sort(key=lambda x:x[0]);retro_added=0
  for _,q in retro:
   if search.add_clause(q):backward_added+=1;retro_added+=1
   if retro_added>=BACKWARD_PER_ROUND:break
  if (not added and not retro_added) or len(search.clauses)>=search.limits['maximum_clauses']:break
 return search.target_proof(search.rules()),backward_attempted,backward_added

def run(m,source,target,mode):
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':SECONDS,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 eng=m.TargetGroundedRefutation(source,target,time.monotonic()+SECONDS,limits)
 if mode=='baseline':
  recipe=eng.search.solve();ba=bb=0
 else:recipe,ba,bb=solve_backward(m,eng.search)
 return {'closure':replay_result(m,eng,recipe),'clauses':len(eng.search.clauses),'rules':len(eng.search.rules()),'rounds':eng.search.rounds,'superpositions':eng.search.superpositions,'reductions':eng.search.reductions,'backward_attempted':ba,'backward_added':bb}

def main():
 m=loadm();rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 out={'schema':'mathgraph.backward-demodulation-gate.v1','seconds':SECONDS,'backward_per_round':BACKWARD_PER_ROUND,'rows':[]}
 for k,rid in enumerate(IDS):
  r=rows[rid];src=m.parse_equation(r['equation1']);tgt=m.parse_equation(r['equation2']);arms={}
  order=['baseline','backward'] if k%2==0 else ['backward','baseline']
  for arm in order:arms[arm]=run(m,src,tgt,arm)
  rec={'id':rid,'arms':arms,'gain':bool(arms['backward']['closure'] and not arms['baseline']['closure'])};out['rows'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['summary']={'baseline_closures':sum(x['arms']['baseline']['closure'] for x in out['rows']),'backward_closures':sum(x['arms']['backward']['closure'] for x in out['rows']),'gains':[x['id'] for x in out['rows'] if x['gain']]}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out['summary'],indent=2,sort_keys=True))
if __name__=='__main__':main()

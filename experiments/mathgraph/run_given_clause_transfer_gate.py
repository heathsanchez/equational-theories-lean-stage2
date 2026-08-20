#!/usr/bin/env python3
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
OUT=ROOT/'experiments/mathgraph/results/given-clause-transfer-gate.json'
KNOWN={'evaluation_normal_0036','evaluation_normal_0040','evaluation_hard_0196','evaluation_order5_0014','evaluation_order5_0042'}
CONFIGS=['evaluation_normal','evaluation_hard','evaluation_extra_hard','evaluation_order5']
SECONDS=3.0


def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m

def replay(m,eng,recipe):
 if recipe is None:return False
 try:
  rr=eng.inline_recipe(recipe);cc=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+1.0,eng.search.limits);nodes,root=cc.compile(rr)
  return nodes[root].lhs==eng.target[0] and nodes[root].rhs==eng.target[1] and m.replay_dag(eng.source,nodes,root,maximum_term_size=eng.search.limits['maximum_replay_term_size'],maximum_nodes=eng.search.limits['maximum_proof_nodes'])
 except Exception:return False

def run(m,gate,row,mode):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2'])
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':SECONDS,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':256,'maximum_clauses':6000,'normalization_steps':256,'maximum_proof_nodes':50000})
 eng=m.TargetGroundedRefutation(src,tgt,time.monotonic()+SECONDS,limits)
 if mode=='baseline': recipe=eng.search.solve(); stats={'given':0,'generated':0}
 else: recipe,stats=gate.solve_given(m,eng.search)
 return {'closure':replay(m,eng,recipe),'clauses':len(eng.search.clauses),'superpositions':eng.search.superpositions,**stats}

def main():
 m=load(SOLVER,'mg_transfer');gate=load(ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py','given_gate_transfer')
 rows=[]
 for cfg in CONFIGS:
  true=[dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train') if bool(r.get('answer')) and r.get('id') not in KNOWN]
  for i in (17,73):
   if i<len(true): rows.append(true[i])
 out={'schema':'mathgraph.given-clause-transfer-gate.v1','seconds':SECONDS,'rows':[]}
 for k,row in enumerate(rows):
  arms={};order=['baseline','given'] if k%2==0 else ['given','baseline']
  for arm in order:arms[arm]=run(m,gate,row,arm)
  rec={'id':row['id'],'arms':arms,'gain':bool(arms['given']['closure'] and not arms['baseline']['closure']),'regression':bool(arms['baseline']['closure'] and not arms['given']['closure'])}
  out['rows'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out['summary']={'n':len(out['rows']),'baseline_closures':sum(r['arms']['baseline']['closure'] for r in out['rows']),'given_closures':sum(r['arms']['given']['closure'] for r in out['rows']),'gains':[r['id'] for r in out['rows'] if r['gain']],'regressions':[r['id'] for r in out['rows'] if r['regression']]}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out['summary'],indent=2,sort_keys=True))

if __name__=='__main__':main()

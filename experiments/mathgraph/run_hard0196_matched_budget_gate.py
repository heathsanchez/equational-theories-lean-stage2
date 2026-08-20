#!/usr/bin/env python3
"""Matched/overmatched runtime falsifier for the hard_0196 control-law gain.

Baseline gets strictly more wall-clock budget than the successful generic
controller arm.  Search grammar, replay, and target are otherwise identical.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
GATE=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py'
OUT=ROOT/'experiments/mathgraph/results/hard0196-matched-budget-gate.json'
RID='evaluation_hard_0196'
BASELINE_SECONDS=(3.0,6.0,12.0,24.0)
GIVEN_SECONDS=3.0

def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m

def mk_engine(m,row,seconds):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2'])
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':seconds,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':128,'new_clauses_per_round':512,'maximum_clauses':24000,'normalization_steps':512,'maximum_proof_nodes':80000})
 return m.TargetGroundedRefutation(src,tgt,time.monotonic()+seconds,limits)

def replay(m,e,r):
 if r is None:return False
 try:
  rr=e.inline_recipe(r);cc=m.CompactSuperposition(m,e.source,e.target,time.monotonic()+2.0,e.search.limits);nodes,root=cc.compile(rr)
  return bool(nodes[root].lhs==e.target[0] and nodes[root].rhs==e.target[1] and m.replay_dag(e.source,nodes,root,maximum_term_size=e.search.limits['maximum_replay_term_size'],maximum_nodes=e.search.limits['maximum_proof_nodes']))
 except Exception:return False

def main():
 m=load(SOLVER,'mg_budget');gate=load(GATE,'given_gate_budget')
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_hard',split='train') if r.get('id')==RID)
 results={'id':RID,'baseline':[]}
 for s in BASELINE_SECONDS:
  t=time.monotonic();e=mk_engine(m,row,s);r=e.search.solve();ok=replay(m,e,r)
  rec={'budget_seconds':s,'elapsed_seconds':round(time.monotonic()-t,6),'closure':ok,'clauses':len(e.search.clauses),'superpositions':e.search.superpositions,'rounds':e.search.rounds,'reductions':e.search.reductions}
  results['baseline'].append(rec);print('baseline',json.dumps(rec,sort_keys=True),flush=True)
 t=time.monotonic();e=mk_engine(m,row,GIVEN_SECONDS);r,stats=gate.solve_given(m,e.search);ok=replay(m,e,r)
 results['given']={'budget_seconds':GIVEN_SECONDS,'elapsed_seconds':round(time.monotonic()-t,6),'closure':ok,'clauses':len(e.search.clauses),'superpositions':e.search.superpositions,**stats}
 results['causal_gate']=bool(ok and not any(x['closure'] for x in results['baseline']))
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(results,indent=2,sort_keys=True)+'\n');print(json.dumps(results,indent=2,sort_keys=True))
 if not results['causal_gate']:raise SystemExit(1)

if __name__=='__main__':main()

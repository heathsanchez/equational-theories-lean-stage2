#!/usr/bin/env python3
"""Residual-state applicability gate for the given-clause capability.

Frozen routing law:
1. Preserve any baseline closure.
2. On baseline failure, run the given-clause controller for SHORT seconds.
3. If still open and passive>0, interpret as a live continuation frontier and rerun at LONG seconds.
4. If still open and passive==0, do not spend more search budget: classify as exhausted-frontier residual.

No theorem IDs, proof traces, answer-specific rules, or Vampire proof bodies are used for routing.
"""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
GATE=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py'
OUT=ROOT/'experiments/mathgraph/results/given-clause-applicability-gate.json'
RESIDUALS={'evaluation_normal_0036','evaluation_normal_0040','evaluation_hard_0196','evaluation_order5_0014','evaluation_order5_0042'}
CONFIGS=['evaluation_normal','evaluation_hard','evaluation_extra_hard','evaluation_order5']
INDICES=[0,11,22,33,44,55,66,77,88,99]
SHORT=3.0
LONG=15.0


def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m

def replay(m,eng,recipe):
 if recipe is None:return False
 try:
  rr=eng.inline_recipe(recipe);cc=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+2.0,eng.search.limits);nodes,root=cc.compile(rr)
  return bool(nodes[root].lhs==eng.target[0] and nodes[root].rhs==eng.target[1] and m.replay_dag(eng.source,nodes,root,maximum_term_size=eng.search.limits['maximum_replay_term_size'],maximum_nodes=eng.search.limits['maximum_proof_nodes']))
 except Exception:return False

def engine(m,row,seconds):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2'])
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':seconds,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
 return m.TargetGroundedRefutation(src,tgt,time.monotonic()+seconds,limits)

def baseline(m,row):
 e=engine(m,row,SHORT);r=e.search.solve();return replay(m,e,r)

def given(m,gate,row,seconds):
 e=engine(m,row,seconds);r,s=gate.solve_given(m,e.search);return replay(m,e,r),s

def main():
 m=load(SOLVER,'mg_applicability');gate=load(GATE,'given_gate_applicability')
 by_id={};transfer=[]
 for cfg in CONFIGS:
  ds=[dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train')]
  for r in ds:by_id[r['id']]=r
  true=[r for r in ds if bool(r.get('answer')) and r.get('id') not in RESIDUALS]
  for i in INDICES:
   if i<len(true):transfer.append(true[i])
 rows=[('residual',by_id[i]) for i in sorted(RESIDUALS) if i in by_id]
 seen=set()
 for r in transfer:
  if r['id'] not in seen:
   rows.append(('transfer',r));seen.add(r['id'])
 out={'schema':'mathgraph.given-clause-applicability.v1','short_seconds':SHORT,'long_seconds':LONG,'routing_rule':'baseline -> short_given; if open and passive>0 -> long_given; else exhausted','records':[]}
 for cohort,row in rows:
  t0=time.monotonic();b=baseline(m,row)
  short=None;long=None;stats_short={};stats_long={};route='baseline' if b else 'open';final=b
  if not b:
   short,stats_short=given(m,gate,row,SHORT)
   if short:
    final=True;route='short_given'
   elif int(stats_short.get('passive',0))>0:
    long,stats_long=given(m,gate,row,LONG)
    final=bool(long);route='long_given' if long else 'live_frontier_open'
   else:
    route='exhausted_frontier'
  rec={'cohort':cohort,'id':row['id'],'baseline':b,'short_given':short,'long_given':long,'final':final,'route':route,'stats_short':stats_short,'stats_long':stats_long,'seconds':round(time.monotonic()-t0,6)}
  out['records'].append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 transfer_rows=[r for r in out['records'] if r['cohort']=='transfer']
 residual_rows=[r for r in out['records'] if r['cohort']=='residual']
 out['summary']={
  'transfer_n':len(transfer_rows),
  'transfer_baseline':sum(r['baseline'] for r in transfer_rows),
  'transfer_final':sum(r['final'] for r in transfer_rows),
  'transfer_gains':[r['id'] for r in transfer_rows if r['final'] and not r['baseline']],
  'transfer_regressions':[r['id'] for r in transfer_rows if r['baseline'] and not r['final']],
  'residual_n':len(residual_rows),
  'residual_baseline':sum(r['baseline'] for r in residual_rows),
  'residual_final':sum(r['final'] for r in residual_rows),
  'residual_gains':[r['id'] for r in residual_rows if r['final'] and not r['baseline']],
  'long_routes':[r['id'] for r in out['records'] if r['long_given'] is not None],
  'exhausted_routes':[r['id'] for r in out['records'] if r['route']=='exhausted_frontier'],
 }
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out['summary'],indent=2,sort_keys=True))
 if out['summary']['transfer_regressions']:raise SystemExit(2)

if __name__=='__main__':main()

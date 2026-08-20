#!/usr/bin/env python3
"""Verifier-gated capability ratchet: preserve baseline, invoke given-clause only after baseline failure."""
import importlib.util,json,sys,time
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
GATE=ROOT/'experiments/mathgraph/run_given_clause_saturation_gate.py'
OUT=ROOT/'experiments/mathgraph/results/given-clause-ratchet-gate.json'
RESIDUALS={'evaluation_normal_0036','evaluation_normal_0040','evaluation_hard_0196','evaluation_order5_0014','evaluation_order5_0042'}
CONFIGS=['evaluation_normal','evaluation_hard','evaluation_extra_hard','evaluation_order5']
INDICES=[0,11,22,33,44,55,66,77,88,99]
SECONDS=3.0

def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m

def replay(m,eng,recipe):
 if recipe is None:return False
 try:
  rr=eng.inline_recipe(recipe);cc=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+1.0,eng.search.limits);nodes,root=cc.compile(rr)
  return bool(nodes[root].lhs==eng.target[0] and nodes[root].rhs==eng.target[1] and m.replay_dag(eng.source,nodes,root,maximum_term_size=eng.search.limits['maximum_replay_term_size'],maximum_nodes=eng.search.limits['maximum_proof_nodes']))
 except Exception:return False

def engine(m,row):
 src=m.parse_equation(row['equation1']);tgt=m.parse_equation(row['equation2'])
 limits=dict(m.COMPACT_SUPERPOSITION_PROBE);limits.update({'seconds':SECONDS,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':256,'maximum_clauses':6000,'normalization_steps':256,'maximum_proof_nodes':50000})
 return m.TargetGroundedRefutation(src,tgt,time.monotonic()+SECONDS,limits)

def baseline(m,row):
 e=engine(m,row);r=e.search.solve();return replay(m,e,r)

def given(m,gate,row):
 e=engine(m,row);r,s=gate.solve_given(m,e.search);return replay(m,e,r),s

def main():
 m=load(SOLVER,'mg_ratchet');gate=load(GATE,'given_gate_ratchet')
 by_id={}
 for cfg in CONFIGS:
  ds=[dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train')]
  for r in ds:by_id[r['id']]=r
  true=[r for r in ds if bool(r.get('answer')) and r.get('id') not in RESIDUALS]
  for i in INDICES:
   if i<len(true):by_id.setdefault('_transfer_'+true[i]['id'],true[i])
 residual_rows=[by_id[i] for i in sorted(RESIDUALS) if i in by_id]
 transfer_rows=[v for k,v in by_id.items() if k.startswith('_transfer_')]
 records=[]
 for cohort,rows in [('residual',residual_rows),('transfer',transfer_rows)]:
  seen=set()
  for row in rows:
   if row['id'] in seen:continue
   seen.add(row['id']);t0=time.monotonic();b=baseline(m,row)
   if b:
    g=None;ratchet=True;route='baseline';stats={}
   else:
    g,stats=given(m,gate,row);ratchet=g;route='given' if g else 'open'
   rec={'cohort':cohort,'id':row['id'],'baseline':b,'given_after_failure':g,'ratchet':ratchet,'route':route,'seconds':round(time.monotonic()-t0,6),'stats':stats}
   records.append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 summary={
  'transfer_n':sum(r['cohort']=='transfer' for r in records),
  'transfer_baseline':sum(r['cohort']=='transfer' and r['baseline'] for r in records),
  'transfer_ratchet':sum(r['cohort']=='transfer' and r['ratchet'] for r in records),
  'transfer_regressions':[r['id'] for r in records if r['cohort']=='transfer' and r['baseline'] and not r['ratchet']],
  'residual_n':sum(r['cohort']=='residual' for r in records),
  'residual_baseline':sum(r['cohort']=='residual' and r['baseline'] for r in records),
  'residual_ratchet':sum(r['cohort']=='residual' and r['ratchet'] for r in records),
  'residual_gains':[r['id'] for r in records if r['cohort']=='residual' and r['ratchet'] and not r['baseline']],
 }
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps({'schema':'mathgraph.given-clause-ratchet.v1','seconds_per_arm':SECONDS,'records':records,'summary':summary},indent=2,sort_keys=True)+'\n');print(json.dumps(summary,indent=2,sort_keys=True))
 if summary['transfer_regressions']:raise SystemExit(2)

if __name__=='__main__':main()

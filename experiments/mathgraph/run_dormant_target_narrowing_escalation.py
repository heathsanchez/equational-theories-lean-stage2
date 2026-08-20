#!/usr/bin/env python3
"""Prospective residual-driven escalation into the dormant generic target-narrowing representation.

The target-narrowing operator predates this residual experiment and was disabled from production
because prior untouched holdout added zero. This gate asks only whether the now-frozen four-case
frontier justifies reactivating that representation after saturation-language exhaustion.
No Vampire proof bodies or theorem-specific rules are used.
"""
import importlib.util,json,subprocess,sys,tempfile,time
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'experiments/mathgraph/results/dormant-target-narrowing-escalation.json'
IDS=['evaluation_normal_0036','evaluation_normal_0040','evaluation_order5_0014','evaluation_order5_0042']
CONFIGS=['evaluation_normal','evaluation_order5']
HIST='origin/mathgraph/superposition-selector-tournament-20260820'

def load_historical():
 text=subprocess.check_output(['git','show',f'{HIST}:submissions/mathgraph/solver.py'],text=True)
 p=Path(tempfile.gettempdir())/'mathgraph_historical_contextual_solver.py';p.write_text(text)
 spec=importlib.util.spec_from_file_location('mg_contextual_hist',p);m=importlib.util.module_from_spec(spec);sys.modules[spec.name]=m;spec.loader.exec_module(m);return m

def run_one(m,row,seconds=8.0):
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 cfg=m.CONTEXTUAL_PORTFOLIO[0]
 limits=dict(cfg['limits']);deadline=time.monotonic()+seconds
 search=m.ContextualSearch(source,target,deadline,limits)
 t=time.monotonic();found=search.solve_target_narrowing(cfg['maximum_depth'],cfg['branching'],cfg['maximum_terms'],cfg['maximum_context_depth']);elapsed=time.monotonic()-t
 replay=False;nodes=0;constructor=None;cert_bytes=None
 if found is not None:
  ns,root=found;nodes=len(ns);replay=bool(m.replay_dag(source,ns,root));
  if replay:
   code=m.make_true_code(source,target,ns,root) if hasattr(m,'make_true_code') else None
   cert_bytes=len(code.encode()) if isinstance(code,str) else None
   constructor='target-narrowing'
 return {'id':row['id'],'closure':bool(found is not None and replay),'seconds':round(elapsed,6),'nodes':nodes,'certificate_bytes':cert_bytes,'narrowing_successors':search.narrowing_successors,'missing_target_introduced':search.missing_target_introduced,'components_joined':search.components_joined,'graph_edges':search.graph_edges,'exhaustion':search.exhaustion,'constructor':constructor}

def main():
 m=load_historical();rows={}
 for cfg in CONFIGS:
  for raw in load_dataset('SAIRfoundation/equational-theories-selected-problems',cfg,split='train'):
   r=dict(raw)
   if r['id'] in IDS:rows[r['id']]=r
 recs=[]
 for rid in IDS:
  rec=run_one(m,rows[rid]);recs.append(rec);print(json.dumps(rec,sort_keys=True),flush=True)
 out={'schema':'mathgraph.dormant-target-narrowing-escalation.v1','historical_ref':HIST,'records':recs,'gains':[r['id'] for r in recs if r['closure']]}
 OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'gains':out['gains']},indent=2))
if __name__=='__main__':main()

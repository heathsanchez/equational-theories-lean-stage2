#!/usr/bin/env python3
import json
from pathlib import Path
from datasets import load_dataset
from judge.verify import verify_answer

RID='evaluation_hard_0196'
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'experiments/mathgraph/results/hard0196-compilation-probe.json'
row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_hard',split='train') if r.get('id')==RID)

bodies={
 'simp_only_h':'''import JudgeProblem\ndef submission : Goal := by\n  intro G _ h\n  intro x y z\n  simp only [h]\n''',
 'simpa_only_h':'''import JudgeProblem\ndef submission : Goal := by\n  intro G _ h\n  intro x y z\n  simpa only [h]\n''',
 'simp_h':'''import JudgeProblem\ndef submission : Goal := by\n  intro G _ h\n  intro x y z\n  simp [h]\n''',
 'aesop_h':'''import JudgeProblem\ndef submission : Goal := by\n  intro G _ h\n  intro x y z\n  aesop\n''',
}
results={}
for name,code in bodies.items():
 r=verify_answer(row,json.dumps({'verdict':'true','code':code}))
 results[name]={'bytes':len(code.encode()),'status':r.get('status'),'error_code':r.get('error_code'),'message':r.get('message'),'direct_declarations':r.get('direct_declarations',[]),'axioms':r.get('axioms',[])}
 print(name,json.dumps(results[name],sort_keys=True),flush=True)
OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps({'id':RID,'results':results},indent=2,sort_keys=True)+'\n')

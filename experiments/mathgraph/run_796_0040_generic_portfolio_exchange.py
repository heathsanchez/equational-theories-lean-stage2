#!/usr/bin/env python3
"""Registered-workflow launcher for the frozen final-three 796 residual test.

The registered workflow invokes this historical path.  This launcher preserves
that CLI but delegates inference to run_796_blind_transfer_any_split.py with one
frozen configuration for all three residuals.  No proof IDs, target-specific
lemmas, hidden derivations, or per-row heuristics are used.
"""
import argparse, json, subprocess, sys, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RUNNER = ROOT / 'experiments/mathgraph/run_796_blind_transfer_any_split.py'
CASES = (
    ('evaluation_normal_0036', 'evaluation_normal'),
    ('evaluation_order5_0014', 'evaluation_order5'),
    ('evaluation_order5_0042', 'evaluation_order5'),
)
BASE = 'https://huggingface.co/datasets/SAIRfoundation/equational-theories-selected-problems/resolve/main/data'


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--input',required=True)
    ap.add_argument('--output',required=True)
    # Historical registered-workflow arguments retained for CLI compatibility.
    ap.add_argument('--frontier-seconds',type=float,default=30)
    ap.add_argument('--given-seconds',type=float,default=10)
    ap.add_argument('--frontier-rounds',type=int,default=3)
    ap.add_argument('--given-steps',type=int,default=16)
    ap.add_argument('--cross-keep',type=int,default=192)
    a=ap.parse_args()

    normal=Path(a.input)
    order5=Path('/tmp/sair_eval/evaluation_order5.jsonl')
    order5.parent.mkdir(parents=True,exist_ok=True)
    if not order5.exists():
        urllib.request.urlretrieve(f'{BASE}/evaluation_order5.jsonl', order5)
    datasets={'evaluation_normal':normal,'evaluation_order5':order5}

    # Freeze to the already-tested matched-transfer budget.  The workflow's
    # historical 30/10 values are deliberately not used to grant extra search.
    frozen={
        'frontier-seconds':'12','given-seconds':'5','frontier-rounds':'3',
        'given-steps':'16','candidate-budget':'512','behavioural-keep':'512',
        'probe-partners':'64','closure-rounds':'2','closure-new-per-round':'128',
        'tail-novelty-max':'80',
    }
    outdir=ROOT/'experiments/mathgraph/results/final-three'
    outdir.mkdir(parents=True,exist_ok=True)
    rows=[]
    for rid,split in CASES:
        dst=outdir/f'{rid}.json'
        cmd=[sys.executable,str(RUNNER),'--id',rid,'--input',str(datasets[split]),'--output',str(dst)]
        for k,v in frozen.items(): cmd += [f'--{k}',v]
        print('FINAL_THREE_START',rid,flush=True)
        rc=subprocess.call(cmd,cwd=ROOT)
        rec={'id':rid,'returncode':rc}
        if dst.exists():
            try: rec['result']=json.loads(dst.read_text())
            except Exception as exc: rec['result_read_error']=f'{type(exc).__name__}: {exc}'
        rows.append(rec)
        print('FINAL_THREE_DONE',json.dumps(rec,sort_keys=True),flush=True)

    summary={
        'schema':'mathgraph.796-final-three-blind.v1',
        'baseline_frontier':'796/800',
        'mechanism':'frozen-0040-derived-blind-transfer',
        'budget':frozen,
        'cases':rows,
    }
    dst=Path(a.output); dst.parent.mkdir(parents=True,exist_ok=True)
    dst.write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print('FINAL_THREE_SUMMARY',json.dumps(summary,sort_keys=True),flush=True)
    if any(r['returncode'] != 0 for r in rows): raise SystemExit(1)

if __name__=='__main__': main()

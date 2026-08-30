#!/usr/bin/env python3
"""Registered-workflow carrier for the frozen MSI context/type portal census.

The registered alpha workflow supplies the historical CLI. This launcher uses
that carrier only to test whether the already-frozen depth-3-stable 0042
collision classes split under structural context/type-valued continuation
identity. Search depth and budgets are unchanged. No proof IDs, hidden traces,
named intermediates, or row-specific lemmas are used.
"""
import argparse, json, subprocess, sys, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RUNNER = ROOT / 'experiments/mathgraph/run_802_msi_context_type_portal.py'
BASE = 'https://huggingface.co/datasets/SAIRfoundation/equational-theories-selected-problems/resolve/main/data'
RID = 'evaluation_order5_0042'

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--input', required=True)
    ap.add_argument('--output', required=True)
    ap.add_argument('--seconds', type=float, default=30.0)
    ap.add_argument('--partners', type=int, default=12)
    ap.add_argument('--max-collisions', type=int, default=200)
    a = ap.parse_args()

    order5 = Path('/tmp/sair_eval/evaluation_order5.jsonl')
    order5.parent.mkdir(parents=True, exist_ok=True)
    if not order5.exists():
        urllib.request.urlretrieve(f'{BASE}/evaluation_order5.jsonl', order5)

    raw = ROOT / 'experiments/mathgraph/results/802-evaluation_order5_0042-msi-context-type-portal.json'
    raw.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        sys.executable, str(RUNNER), '--id', RID,
        '--input', str(order5), '--output', str(raw),
        '--frontier-seconds', '12', '--given-seconds', '5',
        '--frontier-rounds', '3', '--given-steps', '16',
        '--candidate-budget', '256', '--probe-partners', '16',
        '--collision-members', '4', '--child-width', '8',
        '--depth3-members', '3', '--depth3-child-width', '4',
        '--effect-keep', '32',
    ]
    print('MSI_CONTEXT_TYPE_START', RID, flush=True)
    rc = subprocess.call(cmd, cwd=ROOT)
    rec = {'schema':'mathgraph.msi-context-type-portal-carrier.v1','id':RID,'returncode':rc,
           'carrier_only':True,'candidate_budget':256,'probe_partners':16,
           'collision_members':4,'child_width':8,'depth3_members':3,'depth3_child_width':4,
           'experiment':'frozen-context-type-portal'}
    if raw.exists():
        try: rec['result'] = json.loads(raw.read_text())
        except Exception as exc: rec['result_read_error'] = f'{type(exc).__name__}: {exc}'
    dst = Path(a.output)
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(json.dumps(rec, indent=2, sort_keys=True)+'\n')
    print('MSI_CONTEXT_TYPE_DONE', json.dumps(rec, sort_keys=True), flush=True)
    raise SystemExit(rc)

if __name__ == '__main__':
    main()

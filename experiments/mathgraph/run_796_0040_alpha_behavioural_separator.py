#!/usr/bin/env python3
"""Registered-workflow launcher for the frozen 796 endgame transfer.

This file is invoked by an already-registered GitHub Actions workflow on the
796 research branch.  It changes orchestration only: the inference mechanism
is experiments/mathgraph/run_796_endgame_transfer.py and remains frozen.
"""
import argparse, json, subprocess, sys, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RUNNER = ROOT / 'experiments/mathgraph/run_796_endgame_transfer.py'
CASES = (
    ('evaluation_normal_0036', 'evaluation_normal'),
    ('evaluation_order5_0014', 'evaluation_order5'),
    ('evaluation_order5_0042', 'evaluation_order5'),
)
BASE = 'https://huggingface.co/datasets/SAIRfoundation/equational-theories-selected-problems/resolve/main/data'


def main():
    ap = argparse.ArgumentParser()
    # Keep the registered workflow CLI stable. partners/max-collisions are
    # accepted but intentionally unused by the frozen endgame mechanism.
    ap.add_argument('--input', required=True)
    ap.add_argument('--output', required=True)
    ap.add_argument('--seconds', type=float, default=30.0)
    ap.add_argument('--partners', type=int, default=12)
    ap.add_argument('--max-collisions', type=int, default=200)
    a = ap.parse_args()

    normal = Path(a.input)
    order5 = Path('/tmp/sair_eval/evaluation_order5.jsonl')
    order5.parent.mkdir(parents=True, exist_ok=True)
    if not order5.exists():
        urllib.request.urlretrieve(f'{BASE}/evaluation_order5.jsonl', order5)

    datasets = {'evaluation_normal': normal, 'evaluation_order5': order5}
    result_dir = ROOT / 'experiments/mathgraph/results/endgame'
    result_dir.mkdir(parents=True, exist_ok=True)
    rows = []
    for rid, dataset in CASES:
        out = result_dir / f'{rid}.json'
        cmd = [
            sys.executable, str(RUNNER), '--id', rid,
            '--input', str(datasets[dataset]), '--output', str(out),
            '--frontier-seconds', str(a.seconds), '--given-seconds', '10',
            '--frontier-rounds', '3', '--given-steps', '16',
            '--candidate-budget', '512', '--behavioural-keep', '512',
            '--probe-partners', '64', '--closure-rounds', '2',
            '--closure-new-per-round', '128', '--tail-novelty-max', '80',
        ]
        print('ENDGAME_START', rid, flush=True)
        rc = subprocess.call(cmd, cwd=ROOT)
        rec = {'id': rid, 'returncode': rc}
        if out.exists():
            try:
                rec['result'] = json.loads(out.read_text())
            except Exception as exc:
                rec['result_read_error'] = f'{type(exc).__name__}: {exc}'
        rows.append(rec)
        print('ENDGAME_DONE', json.dumps(rec, sort_keys=True), flush=True)

    summary = {
        'schema': 'mathgraph.796-endgame-registered-launch.v1',
        'mechanism_changed': False,
        'cases': rows,
    }
    dst = Path(a.output)
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print('ENDGAME_SUMMARY', json.dumps(summary, sort_keys=True), flush=True)
    if any(r['returncode'] != 0 for r in rows):
        raise SystemExit(1)


if __name__ == '__main__':
    main()

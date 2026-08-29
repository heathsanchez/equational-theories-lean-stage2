#!/usr/bin/env python3
"""Decisive MSI probe: separate *retention budget* from *protected-future testing*.

The previous behavioural exchange stopped testing candidates once enough generally
novel clauses had been retained.  That confounds two questions:
  1. is a candidate novel under generic one-step behaviour?
  2. does a protected future actually expose it as causally necessary?

This wrapper keeps the exact same unguided portfolio generation, cross-portfolio
candidate set, and protected probe basis, but continues testing every candidate
in the bounded candidate set even after the general novelty-retention budget is
full.  No Vampire intermediate IDs are introduced.
"""
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'experiments/mathgraph/run_796_0040_behavioural_separator_exchange.py'

ap = argparse.ArgumentParser()
ap.add_argument('--input', required=True)
ap.add_argument('--output', required=True)
ap.add_argument('--frontier-seconds', type=float, default=30)
ap.add_argument('--given-seconds', type=float, default=10)
ap.add_argument('--frontier-rounds', type=int, default=3)
ap.add_argument('--given-steps', type=int, default=16)
ap.add_argument('--candidate-budget', type=int, default=512)
ap.add_argument('--behavioural-keep', type=int, default=64)
ap.add_argument('--probe-partners', type=int, default=64)
a = ap.parse_args()

s = SRC.read_text()
old = """            retained.append(q); novelty_sizes.append(len(novelty)); current.update(fp)\n            if child is not None:\n                target_recipe=child; target_origin='behavioural-future'; break\n            if len(retained)>=a.behavioural_keep:break\n"""
new = """            # General behavioural novelty is a retention decision, not a reason\n            # to stop asking protected-future questions of later candidates.\n            if len(retained) < a.behavioural_keep:\n                retained.append(q); novelty_sizes.append(len(novelty)); current.update(fp)\n            if child is not None:\n                target_recipe=child; target_origin='protected-future-scan'; break\n"""
if old not in s:
    raise SystemExit('expected behavioural retention block not found')
s = s.replace(old, new, 1)

# Give the output a distinct marker without changing semantics.
s = s.replace("print('BEHAVIOURAL_SEPARATOR_EXCHANGE'", "print('PROTECTED_FUTURE_SCAN'", 1)

with tempfile.NamedTemporaryFile(mode='w', suffix='_protected_future_runtime.py', prefix='_msi_', dir=SRC.parent, delete=False) as fh:
    fh.write(s)
    patched = Path(fh.name)
try:
    cmd = [
        sys.executable, str(patched), '--input', a.input, '--output', a.output,
        '--frontier-seconds', str(a.frontier_seconds), '--given-seconds', str(a.given_seconds),
        '--frontier-rounds', str(a.frontier_rounds), '--given-steps', str(a.given_steps),
        '--candidate-budget', str(a.candidate_budget), '--behavioural-keep', str(a.behavioural_keep),
        '--probe-partners', str(a.probe_partners),
    ]
    raise SystemExit(subprocess.call(cmd, cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)

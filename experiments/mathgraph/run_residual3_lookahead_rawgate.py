#!/usr/bin/env python3
"""Re-run the one-step lookahead census on the exact frozen 8-vs-5 residual.

The previous lookahead accidentally re-applied the full three-part structural
separator and therefore removed all five negatives before lookahead. This
wrapper changes only the admission boundary back to the earlier normalized
size residual: raw_size(child) <= size(rescued_parent) + 1. All lookahead
measurement code and Vampire labels remain otherwise unchanged.
"""
from pathlib import Path
import run_residual3_lookahead_separator as base

ROOT = Path(__file__).resolve().parents[2]
base.OUT = ROOT / 'experiments/mathgraph/results/residual3-lookahead-rawgate.json'


def raw_residual_gate(qraw, qred, parent):
    return base.size(qraw) <= base.size(parent) + 1


# Exact frozen residual boundary: do not reapply the later structural separator.
# base.census_one and base.child_stats resolve gate dynamically.
base.gate = raw_residual_gate

if __name__ == '__main__':
    base.main()

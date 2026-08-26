#!/usr/bin/env python3
"""Run the 0040 corridor with target-grounded rigid names expanded before overlap.

This is diagnostic only: it rewrites the experiment driver at runtime, not solver.py.
Every critical_pair receives replayable parent recipes after TargetGroundedRefutation.inline_recipe,
so named rigid target subterms are structural trees during overlap rather than atomic @L/@R names.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'experiments/mathgraph/run_796_0040_materialize_overlap_continue.py'
source = BASE.read_text()
needle = 'q=engine.search.critical_pair(left,right,0,1,path)'
replacement = 'q=engine.search.critical_pair(engine.inline_recipe(left),engine.inline_recipe(right),0,1,path)'
count = source.count(needle)
if count < 2:
    raise SystemExit(f'expected at least two critical_pair sites, found {count}')
source = source.replace(needle, replacement)
code = compile(source, str(BASE) + ':inline-parent', 'exec')
exec(code, {'__name__': '__main__', '__file__': str(BASE)})

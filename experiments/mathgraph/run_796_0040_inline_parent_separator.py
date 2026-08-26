#!/usr/bin/env python3
"""Run the verified 0040 corridor, expanding rigid parent names only at f217.

Diagnostic only. The established f81->...->f196 derivation is unchanged. At the
f217 rematerialization retry, both replayable parent recipes are expanded with
TargetGroundedRefutation.inline_recipe before derive_pair enumerates overlap paths.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'experiments/mathgraph/run_796_0040_materialize_overlap_continue.py'
source = BASE.read_text()
needle = "q,details=derive_pair(mats.get('f19'),f196mat,'f217',('f19-f196-remat','f196-remat-f19'))"
replacement = "q,details=derive_pair(engine.inline_recipe(mats.get('f19')),engine.inline_recipe(f196mat),'f217',('f19-inline-f196-inline-remat','f196-inline-remat-f19-inline'))"
count = source.count(needle)
if count != 1:
    raise SystemExit(f'expected one f217 rematerialized derive site, found {count}')
source = source.replace(needle, replacement)
code = compile(source, str(BASE) + ':inline-parent-f217', 'exec')
exec(code, {'__name__': '__main__', '__file__': str(BASE)})

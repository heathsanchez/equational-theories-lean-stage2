#!/usr/bin/env python3
"""Compatibility launcher for the fast f278 census.

Escapes literal braces in the post-hoc code fragment before the existing census
wrapper injects it into the recursive wrapper's f-string. This changes only code
generation mechanics, not the autonomous search policy or hidden-trace timing.
"""
import subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'experiments/mathgraph/run_796_0040_fast_f278_census.py'
s = SRC.read_text()
needle = 'new = posthoc + "\'\'\'\\n"'
replacement = 'posthoc = posthoc.replace("{", "{{").replace("}", "}}")\nnew = posthoc + "\'\'\'\\n"'
if needle not in s:
    raise SystemExit('posthoc assembly marker not found')
s = s.replace(needle, replacement, 1)
with tempfile.NamedTemporaryFile(mode='w', suffix='_compat.py', prefix='_mg_', dir=SRC.parent, delete=False) as fh:
    fh.write(s)
    patched = Path(fh.name)
try:
    raise SystemExit(subprocess.call([sys.executable, str(patched), *sys.argv[1:]], cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)

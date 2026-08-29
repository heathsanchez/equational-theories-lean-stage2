#!/usr/bin/env python3
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'experiments/mathgraph/run_796_0040_cross_portfolio_bridge.py'

ap = argparse.ArgumentParser()
ap.add_argument('--input', required=True)
ap.add_argument('--output', required=True)
ap.add_argument('--frontier-seconds', type=float, default=120)
ap.add_argument('--given-seconds', type=float, default=10)
a = ap.parse_args()

s = SRC.read_text()
old = """                    if stop:break\n                if stop:break\n            if f217 is not None or sf.expired():break\n        # Independent given-clause search, stop as soon as f258 is retained.\n"""
new = """                    if stop:break\n                if stop:break\n            # Preserve a partial proposal batch at the end of each completed\n            # frontier pass. This keeps the frontier continuation faithful to\n            # the successful streaming search instead of silently discarding\n            # the residual batch.\n            if not stop and props:\n                props.sort(key=lambda x:x[0]); added=0\n                for _,q in props:\n                    before=len(sf.clauses)\n                    if sf.add_clause(q):\n                        sf.superpositions+=1; added+=1\n                        for c in sf.clauses[before:]:\n                            if matchf(c,'f217') and f217 is None:f217=c\n                        if f217 is not None or added>=64:break\n                props=[]\n            if f217 is not None or sf.expired():break\n        # Independent given-clause search, stop as soon as f258 is retained.\n"""
if old not in s:
    raise SystemExit('expected frontier tail not found; refusing silent patch')
s = s.replace(old, new, 1)

# Keep the patched runtime under experiments/mathgraph so its own __file__-based
# ROOT calculation still resolves to the checked-out repository.  A previous
# tempfile under /tmp made ROOT become '/', turning the test into a harness
# failure before either search continuation ran.
with tempfile.NamedTemporaryFile(
    mode='w', suffix='_cross_fixed_runtime.py',
    prefix='_msi_', dir=SRC.parent, delete=False
) as fh:
    fh.write(s)
    patched = Path(fh.name)
try:
    cmd = [
        sys.executable, str(patched),
        '--input', a.input,
        '--output', a.output,
        '--frontier-seconds', str(a.frontier_seconds),
        '--given-seconds', str(a.given_seconds),
    ]
    raise SystemExit(subprocess.call(cmd, cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)

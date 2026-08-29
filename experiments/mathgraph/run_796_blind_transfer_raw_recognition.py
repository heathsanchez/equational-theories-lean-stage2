#!/usr/bin/env python3
"""Ablate the 0040 semantic-recognition repair during blind transfer.

Everything else is frozen.  Target recognition compares the generated recipe's
raw sides rather than the inlined semantic form.  No proof IDs or problem-
specific intermediates are used.
"""
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BEHAV = ROOT / 'experiments/mathgraph/run_796_0040_behavioural_separator_exchange.py'
RECUR = ROOT / 'experiments/mathgraph/run_796_0040_recursive_closure_diagnostic.py'

ap = argparse.ArgumentParser()
ap.add_argument('--id', required=True)
a, rest = ap.parse_known_args()
if not a.id.startswith('evaluation_normal_'):
    raise SystemExit('blind transfer only accepts evaluation_normal_* ids')

bs = BEHAV.read_text()
old_rid = "RID='evaluation_normal_0040'"
if old_rid not in bs:
    raise SystemExit('RID marker not found')
bs = bs.replace(old_rid, f"RID={a.id!r}", 1)
old_load = "h=load(hp,'mg_behavioural_exchange_helper'); row=h.load_row(a.input); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])"
new_load = "h=load(hp,'mg_behavioural_exchange_helper'); rows=[json.loads(line) for line in Path(a.input).read_text().splitlines() if line.strip()]; row=next((r for r in rows if r.get('id')==RID),None); assert row is not None, RID; source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])"
if old_load not in bs:
    raise SystemExit('row-loader marker not found')
bs = bs.replace(old_load, new_load, 1)
old_exact = "        def exact_target(eng,r):\n            rr=eng.inline_recipe(r)\n            return (rr.lhs,rr.rhs)==target[:2] or (rr.rhs,rr.lhs)==target[:2]\n"
new_exact = "        def exact_target(eng,r):\n            return (r.lhs,r.rhs)==target[:2] or (r.rhs,r.lhs)==target[:2]\n"
if old_exact not in bs:
    raise SystemExit('normalized target matcher not found')
bs = bs.replace(old_exact, new_exact, 1)

with tempfile.NamedTemporaryFile(mode='w', suffix='_raw_blind_behaviour.py', prefix='_mg_', dir=BEHAV.parent, delete=False) as fh:
    fh.write(bs)
    blind_behav = Path(fh.name)
try:
    rs = RECUR.read_text()
    src_line = "SRC = ROOT / 'experiments/mathgraph/run_796_0040_behavioural_separator_exchange.py'"
    if src_line not in rs:
        raise SystemExit('recursive SRC marker not found')
    rs = rs.replace(src_line, f"SRC = Path({str(blind_behav)!r})", 1)
    with tempfile.NamedTemporaryFile(mode='w', suffix='_raw_blind_recursive.py', prefix='_mg_', dir=RECUR.parent, delete=False) as fh:
        fh.write(rs)
        blind_recur = Path(fh.name)
    try:
        raise SystemExit(subprocess.call([sys.executable, str(blind_recur), *rest], cwd=ROOT))
    finally:
        blind_recur.unlink(missing_ok=True)
finally:
    blind_behav.unlink(missing_ok=True)

#!/usr/bin/env python3
"""Run the frozen 0040 developmental mechanism on the three 796 endgame residuals.

Only the selected row id / dataset file changes. No proof IDs, hidden derivations,
problem-specific lemmas, target intermediates, or per-row inference heuristics are injected.
"""
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BEHAV = ROOT / 'experiments/mathgraph/run_796_0040_behavioural_separator_exchange.py'
RECUR = ROOT / 'experiments/mathgraph/run_796_0040_recursive_closure_diagnostic.py'
ALLOWED = {
    'evaluation_normal_0036',
    'evaluation_order5_0014',
    'evaluation_order5_0042',
}

ap = argparse.ArgumentParser()
ap.add_argument('--id', required=True)
a, rest = ap.parse_known_args()
if a.id not in ALLOWED:
    raise SystemExit(f'endgame transfer accepts only frozen residual ids: {sorted(ALLOWED)}')

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

with tempfile.NamedTemporaryFile(mode='w', suffix='_endgame_behaviour.py', prefix='_mg_', dir=BEHAV.parent, delete=False) as fh:
    fh.write(bs)
    endgame_behav = Path(fh.name)
try:
    rs = RECUR.read_text()
    src_line = "SRC = ROOT / 'experiments/mathgraph/run_796_0040_behavioural_separator_exchange.py'"
    if src_line not in rs:
        raise SystemExit('recursive SRC marker not found')
    rs = rs.replace(src_line, f"SRC = Path({str(endgame_behav)!r})", 1)
    with tempfile.NamedTemporaryFile(mode='w', suffix='_endgame_recursive.py', prefix='_mg_', dir=RECUR.parent, delete=False) as fh:
        fh.write(rs)
        endgame_recur = Path(fh.name)
    try:
        raise SystemExit(subprocess.call([sys.executable, str(endgame_recur), *rest], cwd=ROOT))
    finally:
        endgame_recur.unlink(missing_ok=True)
finally:
    endgame_behav.unlink(missing_ok=True)

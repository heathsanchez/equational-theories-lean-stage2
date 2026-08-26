#!/usr/bin/env python3
"""Trace the known winning f217 overlap on actual replayable parents."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'experiments/mathgraph/run_796_0040_materialize_overlap_continue.py'
source = BASE.read_text()
needle = "q,details=derive_pair(mats.get('f19'),f196mat,'f217',('f19-f196-remat','f196-remat-f19'))"
replacement = "f19e=engine.inline_recipe(mats.get('f19')); f196e=engine.inline_recipe(f196mat); out['forced_parent_trace']={'f19_internal':[m.render_term(mats.get('f19').lhs),m.render_term(mats.get('f19').rhs)],'f19_expanded':[m.render_term(f19e.lhs),m.render_term(f19e.rhs)],'f196_internal':[m.render_term(f196mat.lhs),m.render_term(f196mat.rhs)],'f196_expanded':[m.render_term(f196e.lhs),m.render_term(f196e.rhs)]}; forced=engine.search.critical_pair(orient(f19e,True),orient(f196e,True),0,1,('L',)); out['forced_parent_trace']['forced_none']=forced is None; out['forced_parent_trace']['forced_clause']=None if forced is None else [m.render_term(engine.inline_recipe(forced).lhs),m.render_term(engine.inline_recipe(forced).rhs)]; out['forced_parent_trace']['forced_alpha']=False if forced is None else alpha_sig(rigid,engine.inline_recipe(forced).lhs,engine.inline_recipe(forced).rhs)==alpha_sig(rigid,wanted['f217'][0],wanted['f217'][1]); q,details=derive_pair(f19e,f196e,'f217',('f19-inline-f196-inline-remat','f196-inline-remat-f19-inline'))"
count = source.count(needle)
if count != 1:
    raise SystemExit(f'expected one f217 rematerialized derive site, found {count}')
source = source.replace(needle, replacement)
code = compile(source, str(BASE) + ':forced-f217-trace', 'exec')
exec(code, {'__name__': '__main__', '__file__': str(BASE)})

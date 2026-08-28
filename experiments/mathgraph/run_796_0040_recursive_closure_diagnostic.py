#!/usr/bin/env python3
"""Bounded recursive-closure diagnostic for 0040.

This wrapper changes only the generic downstream closure policy. Candidate
generation, behavioural admission, and retention are untouched. Instead of a
single separator/partner pass, newly generated consequences are admitted into
a bounded frontier for subsequent closure rounds. Hidden proof IDs are not
loaded or used for steering.
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
ap.add_argument('--behavioural-keep', type=int, default=512)
ap.add_argument('--probe-partners', type=int, default=64)
ap.add_argument('--closure-rounds', type=int, default=3)
ap.add_argument('--closure-new-per-round', type=int, default=128)
a = ap.parse_args()

s = SRC.read_text()
old = '''        # If no target appeared during the signature probe, give retained separators one shared closure pass.\n        closure_enum=0\n        if target_recipe is None:\n            partners=pool+retained\n            for ni,N in enumerate(retained):\n                for pi,P in enumerate(partners):\n                    for A,B,label in ((N,P,'separator-partner'),(P,N,'partner-separator')):\n                        for ar in (False,True):\n                            aa=orient(A,ar)\n                            for br in (False,True):\n                                bb=orient(B,br)\n                                for path in m.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):\n                                    z=origf(aa,bb,ni,pi,path)\n                                    if z is None:continue\n                                    closure_enum+=1\n                                    if exact_target(z):target_recipe=z; target_origin=label; break\n                                if target_recipe:break\n                            if target_recipe:break\n                        if target_recipe:break\n                    if target_recipe:break\n                if target_recipe:break\n'''
new = f'''        # If no target appeared during the signature probe, recursively close the\n        # retained interface for a small bounded number of rounds. Newly generated\n        # consequences become the next frontier; the base partner set remains fixed.\n        closure_enum=0; closure_rounds_completed=0; closure_generated=[]\n        if target_recipe is None:\n            partners=pool+retained\n            frontier=list(retained)\n            closure_seen=set((sf.alpha_signature(q.lhs,q.rhs),q.lhs,q.rhs) for q in partners)\n            for closure_round in range({a.closure_rounds}):\n                proposals=[]\n                for ni,N in enumerate(frontier):\n                    for pi,P in enumerate(partners):\n                        for A,B,label in ((N,P,'recursive-frontier-partner'),(P,N,'recursive-partner-frontier')):\n                            for ar in (False,True):\n                                aa=orient(A,ar)\n                                for br in (False,True):\n                                    bb=orient(B,br)\n                                    for path in m.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):\n                                        z=origf(aa,bb,ni,pi,path)\n                                        if z is None:continue\n                                        closure_enum+=1\n                                        if exact_target(z):\n                                            target_recipe=z; target_origin=label+'-round-'+str(closure_round+1); break\n                                        k=(sf.alpha_signature(z.lhs,z.rhs),z.lhs,z.rhs)\n                                        if k not in closure_seen:\n                                            closure_seen.add(k); proposals.append((sf.target_score(z),z))\n                                    if target_recipe:break\n                                if target_recipe:break\n                            if target_recipe:break\n                        if target_recipe:break\n                    if target_recipe:break\n                closure_rounds_completed=closure_round+1\n                if target_recipe:break\n                proposals.sort(key=lambda x:x[0])\n                frontier=[q for _,q in proposals[:{a.closure_new_per_round}]]\n                closure_generated.append(len(frontier))\n                if not frontier:break\n                partners=partners+frontier\n'''
if old not in s:
    raise SystemExit('one-pass closure block not found')
s = s.replace(old, new, 1)
needle = "        out={'id':RID,'frontier_clauses':len(sf.clauses),'frontier_enumerated':enumf,'given_clauses':len(sg.clauses),'given_steps':givens,'given_enumerated':enumg,'cross_enumerated':cross_enum,'candidate_budget':len(candidates),'probe_partners':len(probes),'baseline_future_signatures':len(baseline),'baseline_future_calls':baseline_calls,'behavioural_tests':behavioural_tests,'future_calls':future_calls,'behavioural_retained':len(retained),'novelty_sizes':novelty_sizes,'closure_enumerated':closure_enum,'target_found':target_recipe is not None,'target_origin':target_origin,'judge':judged}\n"
replacement = "        out={'id':RID,'frontier_clauses':len(sf.clauses),'frontier_enumerated':enumf,'given_clauses':len(sg.clauses),'given_steps':givens,'given_enumerated':enumg,'cross_enumerated':cross_enum,'candidate_budget':len(candidates),'probe_partners':len(probes),'baseline_future_signatures':len(baseline),'baseline_future_calls':baseline_calls,'behavioural_tests':behavioural_tests,'future_calls':future_calls,'behavioural_retained':len(retained),'novelty_sizes':novelty_sizes,'closure_enumerated':closure_enum,'closure_rounds_completed':closure_rounds_completed,'closure_generated':closure_generated,'target_found':target_recipe is not None,'target_origin':target_origin,'judge':judged}\n"
if needle not in s:
    raise SystemExit('output block not found')
s = s.replace(needle, replacement, 1)

with tempfile.NamedTemporaryFile(mode='w', suffix='_recursive_runtime.py', prefix='_mg_', dir=SRC.parent, delete=False) as fh:
    fh.write(s)
    patched = Path(fh.name)
try:
    cmd = [sys.executable, str(patched),
           '--input', a.input, '--output', a.output,
           '--frontier-seconds', str(a.frontier_seconds),
           '--given-seconds', str(a.given_seconds),
           '--frontier-rounds', str(a.frontier_rounds),
           '--given-steps', str(a.given_steps),
           '--candidate-budget', str(a.candidate_budget),
           '--behavioural-keep', str(a.behavioural_keep),
           '--probe-partners', str(a.probe_partners)]
    raise SystemExit(subprocess.call(cmd, cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)

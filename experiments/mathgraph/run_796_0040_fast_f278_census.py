#!/usr/bin/env python3
"""Fast 0040 recursive closure with a post-hoc census for the known f278 trace
intermediate. Hidden trace identities are loaded only after autonomous generation,
retention, closure generation, and promotion decisions are complete.
"""
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'experiments/mathgraph/run_796_0040_recursive_closure_diagnostic.py'

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
ap.add_argument('--closure-rounds', type=int, default=2)
ap.add_argument('--closure-new-per-round', type=int, default=64)
ap.add_argument('--tail-novelty-max', type=int, default=80)
a = ap.parse_args()

s = SRC.read_text()

old = "        closure_enum=0; closure_rounds_completed=0; closure_generated=[]\\n"
new = "        closure_enum=0; closure_rounds_completed=0; closure_generated=[]; closure_all=[]; closure_promoted=[]\\n"
if old not in s:
    raise SystemExit('closure counters marker not found')
s = s.replace(old, new, 1)

old = "                                        closure_enum+=1\\n"
new = "                                        closure_enum+=1; closure_all.append((closure_round+1,z))\\n"
if old not in s:
    raise SystemExit('closure enumeration marker not found')
s = s.replace(old, new, 1)

old = "                frontier=[q for _,q in proposals[:{a.closure_new_per_round}]]\\n                closure_generated.append(len(frontier))\\n"
new = "                frontier=[q for _,q in proposals[:{a.closure_new_per_round}]]\\n                closure_promoted.extend((closure_round+1,q) for q in frontier)\\n                closure_generated.append(len(frontier))\\n"
if old not in s:
    raise SystemExit('promotion marker not found')
s = s.replace(old, new, 1)

old = "        judged=finish(ef,sf,target_recipe) if target_recipe is not None else None\\n"
new = r'''        # POST-HOC ONLY. All autonomous closure generation and promotion is finished.
        TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
        trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
        rigid=m.RigidSuperpositionModule(); defs={}; wanted={}
        for block in h.fof_blocks(proof):
            parsed=h.parse_fof(block)
            if not parsed:continue
            fid,kind,formula,_=parsed
            try:eq=h.formula_equality(formula)
            except Exception:eq=None
            if eq is None:continue
            x,y=eq
            if kind=='definition':
                if x[0]=='var' and x[1].startswith('sF'):defs[x[1]]=y
                elif y[0]=='var' and y[1].startswith('sF'):defs[y[1]]=x
            elif fid=='f278':
                wanted[fid]=(h.map_rigids(h.inline_defs(x,defs),target[2]),h.map_rigids(h.inline_defs(y,defs),target[2]))
        def alpha_pair(a0,b0):
            names={}; x0=rigid.alpha_canonical_term(a0,names); y0=rigid.alpha_canonical_term(b0,names); return min((x0,y0),(y0,x0))
        f278_sig=alpha_pair(*wanted['f278']) if 'f278' in wanted else None
        def is_f278(r):
            if f278_sig is None:return False
            try:
                p=(h.inline_engine_names(r.lhs,ef.reverse_constants),h.inline_engine_names(r.rhs,ef.reverse_constants))
                return alpha_pair(*p)==f278_sig
            except Exception:return False
        f278_generated=[{'round':rnd,'index':i+1} for i,(rnd,q) in enumerate(closure_all) if is_f278(q)]
        f278_promoted=[{'round':rnd,'index':i+1} for i,(rnd,q) in enumerate(closure_promoted) if is_f278(q)]
        f278_census={'posthoc_hidden_trace_only':True,'generated_hits':f278_generated,'generated_count':len(f278_generated),'promoted_hits':f278_promoted,'promoted_count':len(f278_promoted)}
        judged=finish(ef,sf,target_recipe) if target_recipe is not None else None
'''
if old not in s:
    raise SystemExit('judge marker not found')
s = s.replace(old, new, 1)

old = "'closure_generated':closure_generated,'target_found':target_recipe is not None"
new = "'closure_generated':closure_generated,'f278_census':f278_census,'target_found':target_recipe is not None"
if old not in s:
    raise SystemExit('output marker not found')
s = s.replace(old, new, 1)

with tempfile.NamedTemporaryFile(mode='w', suffix='_f278_runtime.py', prefix='_mg_', dir=SRC.parent, delete=False) as fh:
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
           '--probe-partners', str(a.probe_partners),
           '--closure-rounds', str(a.closure_rounds),
           '--closure-new-per-round', str(a.closure_new_per_round),
           '--tail-novelty-max', str(a.tail_novelty_max)]
    raise SystemExit(subprocess.call(cmd, cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)

#!/usr/bin/env python3
"""Post-hoc localization for the failed 0040 causal bridge selector.

This is deliberately NOT an autonomy result.  It leaves candidate generation and
causal scoring unchanged, then—only after the generic candidate set has been
constructed and scored—uses the known Vampire proof trace to label f259/f15/f278.
It asks four causal questions:

1. Was an alpha-equivalent of f259 generated at all?
2. If so, where did the generic causal selector rank/retain it?
3. With that bridge force-retained, can the unchanged raw live pool close 0040?
4. If raw closure fails, is the known downstream f15 capability nevertheless
   coverable from the frontier and does materializing only that diagnostic cover
   restore verified closure?

Hidden proof IDs never affect candidate generation or generic scoring.  They are
used only after scoring for diagnosis and forced-ablation controls.
"""
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'experiments/mathgraph/run_796_0040_causal_bridge_selector.py'

ap = argparse.ArgumentParser()
ap.add_argument('--input', required=True)
ap.add_argument('--output', required=True)
ap.add_argument('--frontier-seconds', type=float, default=30)
ap.add_argument('--given-seconds', type=float, default=10)
ap.add_argument('--frontier-rounds', type=int, default=3)
ap.add_argument('--given-steps', type=int, default=16)
ap.add_argument('--candidate-budget', type=int, default=192)
ap.add_argument('--behavioural-keep', type=int, default=32)
ap.add_argument('--probe-partners', type=int, default=10)
a = ap.parse_args()

s = SRC.read_text()

# Inject only after generic candidate generation + mixed-world scoring is complete.
needle = """        scored.sort(key=lambda x:x[0])\n        causal_top=[]\n"""
inject = r"""        scored.sort(key=lambda x:x[0])

        # POST-HOC DIAGNOSTIC ONLY.  Everything above this line is the unchanged
        # generic selector.  The hidden proof trace is loaded only now.
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
            elif fid in {'f15','f259','f278'}:
                wanted[fid]=(h.map_rigids(h.inline_defs(x,defs),target[2]),h.map_rigids(h.inline_defs(y,defs),target[2]))
        def alpha_pair(a,b):
            names={}; x=rigid.alpha_canonical_term(a,names); y=rigid.alpha_canonical_term(b,names); return min((x,y),(y,x))
        wsig={fid:alpha_pair(*eq) for fid,eq in wanted.items()}
        def inline_pair(r):return (h.inline_engine_names(r.lhs,ef.reverse_constants),h.inline_engine_names(r.rhs,ef.reverse_constants))
        def diag_match(r,fid):return fid in wsig and alpha_pair(*inline_pair(r))==wsig[fid]

        generated_bridge=None; generated_bridge_candidate_rank=None
        for rank,(_,q) in enumerate(candidates,1):
            if diag_match(q,'f259'):
                generated_bridge=q; generated_bridge_candidate_rank=rank; break
        scored_bridge_rank=None; scored_bridge_key=None
        for rank,item in enumerate(scored,1):
            if diag_match(item[1],'f259'):
                scored_bridge_rank=rank; scored_bridge_key=item[0]; break

        # Is f15 already explicitly live, or only latent/coverable in the frontier?
        raw_f15_frontier=next((expf(c) for c in sf.clauses if diag_match(expf(c),'f15')),None)
        f15_cover=None
        if 'f15' in wanted:
            goal=wanted['f15']
            for c0 in sf.clauses:
                c=expf(c0); x,y=inline_pair(c)
                for rev,(u,v) in enumerate(((x,y),(y,x))):
                    sub={}
                    if rigid.match_term(u,goal[0],sub) and rigid.match_term(v,goal[1],sub):
                        basec=c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,))
                        f15_cover=sf.instantiate(basec,sub); break
                if f15_cover is not None:break

        def close_with_partners(bridge,partners):
            if bridge is None:return None,0
            enumerated=0
            for pi,P in enumerate(partners):
                for A,B in ((bridge,P),(P,bridge)):
                    for ar in (False,True):
                        aa=orient(A,ar)
                        for br in (False,True):
                            bb=orient(B,br)
                            for path in m.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):
                                z=origf(aa,bb,0,pi,path)
                                if z is None:continue
                                enumerated+=1
                                if exact_target(z):return z,enumerated
            return None,enumerated

        # Forced bridge + unchanged raw live pool: sharp selector-vs-scaffolding test.
        forced_raw_target,forced_raw_enumerated=close_with_partners(generated_bridge,pool)
        forced_raw_judge=finish(ef,sf,forced_raw_target) if forced_raw_target is not None else None

        # Diagnostic materialization control.  This is intentionally guided and
        # cannot support an autonomy claim; it tests whether the missing issue is
        # that a necessary continuation exists only latently as an instantiable
        # frontier capability rather than as a raw pool clause.
        forced_materialized_target=None; forced_materialized_enumerated=0; forced_materialized_judge=None
        if generated_bridge is not None and f15_cover is not None:
            forced_materialized_target,forced_materialized_enumerated=close_with_partners(generated_bridge,[f15_cover])
            forced_materialized_judge=finish(ef,sf,forced_materialized_target) if forced_materialized_target is not None else None

        diagnostic={
            'posthoc_hidden_trace_only':True,
            'generated_f259':generated_bridge is not None,
            'f259_candidate_rank':generated_bridge_candidate_rank,
            'f259_causal_scored_rank':scored_bridge_rank,
            'f259_causal_score':scored_bridge_key,
            'raw_f15_frontier':raw_f15_frontier is not None,
            'f15_coverable_from_frontier':f15_cover is not None,
            'forced_bridge_raw_pool_target_found':forced_raw_target is not None,
            'forced_bridge_raw_pool_enumerated':forced_raw_enumerated,
            'forced_bridge_raw_pool_judge':forced_raw_judge,
            'forced_bridge_materialized_f15_target_found':forced_materialized_target is not None,
            'forced_bridge_materialized_f15_enumerated':forced_materialized_enumerated,
            'forced_bridge_materialized_f15_judge':forced_materialized_judge,
        }
        causal_top=[]
"""
if needle not in s:
    raise SystemExit('causal scored marker not found')
s=s.replace(needle,inject,1)

# After generic retention, record whether the diagnostically known bridge survived.
needle2 = """            if target_recipe is None and child is not None:\n                target_recipe=child; target_origin='mixed-protected-future'\n\n"""
inject2 = """            if target_recipe is None and child is not None:\n                target_recipe=child; target_origin='mixed-protected-future'\n        diagnostic['f259_retained_rank']=next((i for i,q in enumerate(retained,1) if diag_match(q,'f259')),None)\n\n"""
if needle2 not in s:
    raise SystemExit('causal retention marker not found')
s=s.replace(needle2,inject2,1)

# Persist the diagnostic alongside the unchanged causal-selector metrics.
needle3 = """new_out = \"\"\"'behavioural_retained':len(retained),'novelty_sizes':novelty_sizes,'causal_top':causal_top[:12],'closure_enumerated':closure_enum\"\"\"\n"""
replace3 = """new_out = \"\"\"'behavioural_retained':len(retained),'novelty_sizes':novelty_sizes,'causal_top':causal_top[:12],'diagnostic':diagnostic,'closure_enumerated':closure_enum\"\"\"\n"""
if needle3 not in s:
    raise SystemExit('causal output marker not found')
s=s.replace(needle3,replace3,1)

with tempfile.NamedTemporaryFile(mode='w', suffix='_causal_bridge_diagnostic_runtime.py', prefix='_mg_', dir=SRC.parent, delete=False) as fh:
    fh.write(s); patched=Path(fh.name)
try:
    cmd=[sys.executable,str(patched),
         '--input',a.input,'--output',a.output,
         '--frontier-seconds',str(a.frontier_seconds),
         '--given-seconds',str(a.given_seconds),
         '--frontier-rounds',str(a.frontier_rounds),
         '--given-steps',str(a.given_steps),
         '--candidate-budget',str(a.candidate_budget),
         '--behavioural-keep',str(a.behavioural_keep),
         '--probe-partners',str(a.probe_partners)]
    raise SystemExit(subprocess.call(cmd,cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)

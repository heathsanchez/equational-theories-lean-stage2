#!/usr/bin/env python3
"""Causal cross-world selector for evaluation_normal_0040.

This is deliberately a wrapper around the existing generic behavioural-exchange
experiment.  It changes only the retention interface.  Candidates are still
created by unguided cross-portfolio superposition and no Vampire intermediate
IDs are available to the selector.

Instead of rewarding raw one-step novelty, a candidate is tested as a mediator
between the independently developed frontier and given-clause worlds:

    candidate + F -> child -> child + G
    candidate + G -> child -> child + F

The protected future is therefore a genuinely mixed continuation.  We rank by
best generic target-residual contraction, then by the number of improving mixed
futures, then by mixed behavioural diversity.  The theorem target is public to
the solver; no hidden proof trace or named intermediate is used.
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
ap.add_argument('--candidate-budget', type=int, default=256)
ap.add_argument('--behavioural-keep', type=int, default=48)
ap.add_argument('--probe-partners', type=int, default=16)
a = ap.parse_args()

s = SRC.read_text()

old_pool = """        pool=[expf(c) for c in sf.clauses]+[expf(expg(c)) for c in sg.clauses]\n        probes=sorted(pool,key=sf.target_score)[:a.probe_partners]\n"""
new_pool = """        fpool=[expf(c) for c in sf.clauses]\n        gpool=[expf(expg(c)) for c in sg.clauses]\n        pool=fpool+gpool\n        # Keep the two independently developed worlds visible.  A combined top-k\n        # probe pool would erase exactly the provenance distinction being tested.\n        fprobes=sorted(fpool,key=sf.target_score)[:a.probe_partners]\n        gprobes=sorted(gpool,key=sf.target_score)[:a.probe_partners]\n        probes=fprobes+gprobes\n"""
if old_pool not in s:
    raise SystemExit('expected pool block not found')
s = s.replace(old_pool, new_pool, 1)

old_select = """        retained=[]; behavioural_tests=0; future_calls=0; novelty_sizes=[]; target_recipe=None; target_origin=None\n        current=set(baseline)\n        for _,q in candidates:\n            fp,child,n=future_signature(q); behavioural_tests+=1; future_calls+=n\n            novelty=fp-current\n            if not novelty:continue\n            retained.append(q); novelty_sizes.append(len(novelty)); current.update(fp)\n            if child is not None:\n                target_recipe=child; target_origin='behavioural-future'; break\n            if len(retained)>=a.behavioural_keep:break\n\n"""
new_select = r"""        # Higher-order protected future: candidate must mediate between the two
        # independently developed proof worlds.  This measures relational utility,
        # not a unary novelty property of a clause.
        def first_children(rule, partners, cap=40):
            out=[]; seen_child=set(); calls=0
            for pi,p in enumerate(partners):
                for A,B in ((rule,p),(p,rule)):
                    for ar in (False,True):
                        aa=orient(A,ar)
                        for br in (False,True):
                            bb=orient(B,br)
                            for path in m.nonvariable_positions(aa.lhs,maximum_depth=5,include_root=True):
                                z=origf(aa,bb,0,pi,path)
                                if z is None:continue
                                calls+=1
                                k=(sf.alpha_signature(z.lhs,z.rhs),z.lhs,z.rhs)
                                if k in seen_child:continue
                                seen_child.add(k); out.append(z)
                                if len(out)>=cap:return out,calls
            return out,calls
        def mixed_future(rule):
            sigs=set(); target_child=None; calls=0; improving=0; best=float('inf')
            base_score=sf.target_score(rule)
            for first_world,second_world in ((fprobes,gprobes),(gprobes,fprobes)):
                first,n=first_children(rule,first_world); calls+=n
                for ci,ch in enumerate(first):
                    for pi,p in enumerate(second_world):
                        for A,B in ((ch,p),(p,ch)):
                            for ar in (False,True):
                                aa=orient(A,ar)
                                for br in (False,True):
                                    bb=orient(B,br)
                                    for path in m.nonvariable_positions(aa.lhs,maximum_depth=5,include_root=True):
                                        z=origf(aa,bb,ci,pi,path)
                                        if z is None:continue
                                        calls+=1; sigs.add(sig_of(z))
                                        zs=sf.target_score(z)
                                        if zs < best:best=zs
                                        if zs < base_score:improving+=1
                                        if exact_target(z):target_child=z
            return sigs,target_child,calls,best,improving

        retained=[]; behavioural_tests=0; future_calls=0; novelty_sizes=[]; target_recipe=None; target_origin=None
        scored=[]
        for raw_score,q in candidates:
            fp,child,n,best,improving=mixed_future(q); behavioural_tests+=1; future_calls+=n
            if not fp:continue
            # Lower best score is better; the other terms reward causal contraction
            # and behavioural breadth only after a protected mixed future exists.
            scored.append(((best,-improving,-len(fp),raw_score),q,len(fp),improving,best,child))
        scored.sort(key=lambda x:x[0])
        causal_top=[]
        for rank,item in enumerate(scored[:a.behavioural_keep],1):
            key,q,width,improving,best,child=item
            retained.append(q); novelty_sizes.append(width)
            causal_top.append({'rank':rank,'best_future_score':best,'improving_mixed_futures':improving,'mixed_signatures':width,'raw_target_score':key[3]})
            if target_recipe is None and child is not None:
                target_recipe=child; target_origin='mixed-protected-future'

"""
if old_select not in s:
    raise SystemExit('expected selection block not found')
s = s.replace(old_select, new_select, 1)

# Add causal ranking diagnostics to the existing JSON without changing the
# generic closure or official-judge path.
old_out = """'behavioural_retained':len(retained),'novelty_sizes':novelty_sizes,'closure_enumerated':closure_enum"""
new_out = """'behavioural_retained':len(retained),'novelty_sizes':novelty_sizes,'causal_top':causal_top[:12],'closure_enumerated':closure_enum"""
if old_out not in s:
    raise SystemExit('expected output fragment not found')
s = s.replace(old_out, new_out, 1)
s = s.replace("print('BEHAVIOURAL_SEPARATOR_EXCHANGE'", "print('CAUSAL_BRIDGE_SELECTOR'", 1)

with tempfile.NamedTemporaryFile(mode='w', suffix='_causal_bridge_runtime.py', prefix='_mg_', dir=SRC.parent, delete=False) as fh:
    fh.write(s)
    patched=Path(fh.name)
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

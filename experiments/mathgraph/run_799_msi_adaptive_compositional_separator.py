#!/usr/bin/env python3
"""Adaptive MSI compositional-separator probe.

Refine the indexed one-step behavioural quotient only where it is unstable:
inspect collision classes, search bounded depth-2 composed continuations for
fresh separators, and promote only representatives exposed by an actual split.
No proof IDs, hidden traces, named intermediates, or row-specific lemmas.
"""
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SRC=ROOT/'experiments/mathgraph/run_796_0040_behavioural_separator_exchange.py'

ap=argparse.ArgumentParser()
ap.add_argument('--id',required=True)
ap.add_argument('--input',required=True)
ap.add_argument('--output',required=True)
ap.add_argument('--frontier-seconds',type=float,default=12)
ap.add_argument('--given-seconds',type=float,default=5)
ap.add_argument('--frontier-rounds',type=int,default=3)
ap.add_argument('--given-steps',type=int,default=16)
ap.add_argument('--candidate-budget',type=int,default=256)
ap.add_argument('--probe-partners',type=int,default=16)
ap.add_argument('--collision-members',type=int,default=4)
ap.add_argument('--child-width',type=int,default=8)
ap.add_argument('--effect-keep',type=int,default=32)
a=ap.parse_args()
if not a.id.startswith('evaluation_'): raise SystemExit('requires evaluation_* id')

s=SRC.read_text()
s=s.replace("RID='evaluation_normal_0040'",f"RID={a.id!r}",1)
old_load="h=load(hp,'mg_behavioural_exchange_helper'); row=h.load_row(a.input); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])"
new_load="h=load(hp,'mg_behavioural_exchange_helper'); rows=[json.loads(line) for line in Path(a.input).read_text().splitlines() if line.strip()]; row=next((r for r in rows if r.get('id')==RID),None); assert row is not None,RID; source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])"
if old_load not in s: raise SystemExit('row-loader marker not found')
s=s.replace(old_load,new_load,1)
# Pointwise/indexed one-step observations.
s=s.replace("calls+=1; out.add(sig_of(z))","calls+=1; out.add((pi,sig_of(z)))",1)
start=s.index("        retained=[]; behavioural_tests=0; future_calls=0; novelty_sizes=[]; target_recipe=None; target_origin=None")
end=s.index("        judged=finish(ef,sf,target_recipe) if target_recipe is not None else None",start)
replacement=f'''        # Build the one-step indexed quotient first.
        behavioural_tests=0; future_calls=0; target_recipe=None; target_origin=None
        one_step={{}}; probe_hits={{}}
        for score,q in candidates:
            fp,child,n=future_signature(q); behavioural_tests+=1; future_calls+=n
            for obs in fp:
                probe_hits[obs[0]]=probe_hits.get(obs[0],0)+1
            if child is not None:
                target_recipe=child; target_origin='adaptive-one-step-evaluation'; break
            ek=tuple(sorted(fp))
            one_step.setdefault(ek,[]).append((score,q))
        one_step_class_count=len(one_step)
        collision_classes=[v for v in one_step.values() if len(v)>1]
        still_merged_collision_count=len(collision_classes)

        depth2_classes_tested=0; depth2_classes_split=0; fresh_separators=[]; split_mult=[]
        compose_calls=0
        # Choose the depth-2 basis only from probe coordinates that actually
        # participated in one-step observations. This is target-independent and
        # avoids a vacuous "depth-2 stable" result caused by inactive probes.
        selected_probe_indices=[i for i,_ in sorted(probe_hits.items(),key=lambda kv:(-kv[1],kv[0]))[:min(8,len(probe_hits))]]
        small_probes=[probes[i] for i in selected_probe_indices]
        selected_probe_hits=[probe_hits[i] for i in selected_probe_indices]
        def depth2_signature(rule):
            nonlocal compose_calls,target_recipe,target_origin
            first=[]; seen1=set()
            for local_pi,p in enumerate(small_probes):
                pi=selected_probe_indices[local_pi]
                for order,(A,B) in enumerate(((rule,p),(p,rule))):
                    for ar in (False,True):
                        aa=orient(A,ar)
                        for br in (False,True):
                            bb=orient(B,br)
                            for path in m.nonvariable_positions(aa.lhs,maximum_depth=6,include_root=True):
                                z=origf(aa,bb,0,pi,path)
                                if z is None: continue
                                compose_calls+=1
                                if exact_target(ef,z):
                                    target_recipe=z; target_origin='adaptive-depth1-child'; return (('TARGET',),)
                                k=(sf.alpha_signature(z.lhs,z.rhs),z.lhs,z.rhs)
                                if k not in seen1:
                                    seen1.add(k); first.append((sf.target_score(z),z))
            first.sort(key=lambda x:x[0]); first=first[:{a.child_width}]
            out=set()
            for ci,(_,child) in enumerate(first):
                fp,hit,n=future_signature(child); compose_calls+=n
                if hit is not None:
                    target_recipe=hit; target_origin='adaptive-depth2-evaluation'; return (('TARGET',),)
                for obs in fp: out.add((ci,obs))
            return tuple(sorted(out,key=str))

        if target_recipe is None:
            for cls in collision_classes:
                depth2_classes_tested+=1
                members=sorted(cls,key=lambda x:x[0])[:{a.collision_members}]
                buckets={{}}
                for score,q in members:
                    ds=depth2_signature(q)
                    buckets.setdefault(ds,[]).append((score,q))
                    if target_recipe is not None: break
                if target_recipe is not None: break
                if len(buckets)>1:
                    depth2_classes_split+=1; split_mult.append(len(buckets))
                    for vals in buckets.values(): fresh_separators.append(min(vals,key=lambda x:x[0]))

        # Retain only separators justified by a composition-induced split.
        fresh_separators.sort(key=lambda x:x[0])
        retained=[]; rseen=set()
        for score,q in fresh_separators:
            k=(sf.alpha_signature(q.lhs,q.rhs),q.lhs,q.rhs)
            if k in rseen: continue
            rseen.add(k); retained.append(q)
            if len(retained)>={a.effect_keep}: break

        closure_enum=0; closure_generated=[]
        if target_recipe is None and retained:
            proposals=[]; partners=list(small_probes)+list(retained)
            for ni,N in enumerate(retained):
                for pi,P in enumerate(partners):
                    for A,B,label in ((N,P,'adaptive-separator-partner'),(P,N,'adaptive-partner-separator')):
                        for ar in (False,True):
                            aa=orient(A,ar)
                            for br in (False,True):
                                bb=orient(B,br)
                                for path in m.nonvariable_positions(aa.lhs,maximum_depth=8,include_root=True):
                                    z=origf(aa,bb,ni,pi,path)
                                    if z is None: continue
                                    closure_enum+=1
                                    if exact_target(ef,z): target_recipe=z; target_origin=label; break
                                    proposals.append((sf.target_score(z),z))
                                if target_recipe: break
                            if target_recipe: break
                        if target_recipe: break
                    if target_recipe: break
                if target_recipe: break
            if target_recipe is None:
                proposals.sort(key=lambda x:x[0]); closure_generated=[min(len(proposals),128)]

        first_instability_depth=2 if depth2_classes_split else None
        max_split=max(split_mult) if split_mult else 0
        median_split=(sorted(split_mult)[len(split_mult)//2] if split_mult else 0)
'''
s=s[:start]+replacement+s[end:]
old_out="        out={'id':RID,'frontier_clauses':len(sf.clauses),'frontier_enumerated':enumf,'given_clauses':len(sg.clauses),'given_steps':givens,'given_enumerated':enumg,'cross_enumerated':cross_enum,'candidate_budget':len(candidates),'probe_partners':len(probes),'baseline_future_signatures':len(baseline),'baseline_future_calls':baseline_calls,'behavioural_tests':behavioural_tests,'future_calls':future_calls,'behavioural_retained':len(retained),'novelty_sizes':novelty_sizes,'closure_enumerated':closure_enum,'target_found':target_recipe is not None,'target_origin':target_origin,'judge':judged}\n"
new_out="        out={'id':RID,'mode':'msi-adaptive-compositional-separator','frontier_clauses':len(sf.clauses),'frontier_enumerated':enumf,'given_clauses':len(sg.clauses),'given_steps':givens,'given_enumerated':enumg,'cross_enumerated':cross_enum,'candidate_budget':len(candidates),'probe_partners':len(probes),'baseline_future_signatures':len(baseline),'baseline_future_calls':baseline_calls,'behavioural_tests':behavioural_tests,'future_calls':future_calls,'one_step_class_count':one_step_class_count,'still_merged_collision_count':still_merged_collision_count,'active_probe_count':len(probe_hits),'selected_probe_indices':selected_probe_indices,'selected_probe_hits':selected_probe_hits,'depth2_classes_tested':depth2_classes_tested,'depth2_classes_split':depth2_classes_split,'first_instability_depth':first_instability_depth,'fresh_separators':len(fresh_separators),'max_split_multiplicity':max_split,'median_split_multiplicity':median_split,'representatives_retained':len(retained),'compose_calls':compose_calls,'closure_enumerated':closure_enum,'closure_generated':closure_generated,'target_found':target_recipe is not None,'target_origin':target_origin,'judge':judged}\n"
if old_out not in s: raise SystemExit('output marker not found')
s=s.replace(old_out,new_out,1)
with tempfile.NamedTemporaryFile(mode='w',suffix='_msi_adaptive.py',prefix='_mg_',dir=SRC.parent,delete=False) as fh:
    fh.write(s); patched=Path(fh.name)
try:
    cmd=[sys.executable,str(patched),'--input',a.input,'--output',a.output,'--frontier-seconds',str(a.frontier_seconds),'--given-seconds',str(a.given_seconds),'--frontier-rounds',str(a.frontier_rounds),'--given-steps',str(a.given_steps),'--candidate-budget',str(a.candidate_budget),'--behavioural-keep',str(a.effect_keep),'--probe-partners',str(a.probe_partners)]
    raise SystemExit(subprocess.call(cmd,cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)

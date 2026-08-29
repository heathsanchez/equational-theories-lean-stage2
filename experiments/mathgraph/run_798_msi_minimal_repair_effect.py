#!/usr/bin/env python3
"""MSI-derived endgame probe.

Translate the mechanized Minimal-Sufficient-Interface law into the Stage-2
search boundary: candidates are identified by the behavioural repair effect
(their one-step future observation set), not by equation syntax.  Among strict
repairs, promote representatives with the smallest positive effect first: the
finite analogue of the coarsest justified refinement E ∧ R.

No hidden proof IDs, proof traces, named intermediates, or row-specific lemmas
are used.
"""
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'experiments/mathgraph/run_796_0040_behavioural_separator_exchange.py'

ap = argparse.ArgumentParser()
ap.add_argument('--id', required=True)
ap.add_argument('--input', required=True)
ap.add_argument('--output', required=True)
ap.add_argument('--frontier-seconds', type=float, default=12)
ap.add_argument('--given-seconds', type=float, default=5)
ap.add_argument('--frontier-rounds', type=int, default=3)
ap.add_argument('--given-steps', type=int, default=16)
ap.add_argument('--candidate-budget', type=int, default=512)
ap.add_argument('--probe-partners', type=int, default=64)
ap.add_argument('--effect-keep', type=int, default=32)
ap.add_argument('--closure-rounds', type=int, default=2)
ap.add_argument('--closure-new-per-round', type=int, default=128)
a = ap.parse_args()

if not a.id.startswith('evaluation_'):
    raise SystemExit('requires evaluation_* id')

s = SRC.read_text()
s = s.replace("RID='evaluation_normal_0040'", f"RID={a.id!r}", 1)
old_load = "h=load(hp,'mg_behavioural_exchange_helper'); row=h.load_row(a.input); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])"
new_load = "h=load(hp,'mg_behavioural_exchange_helper'); rows=[json.loads(line) for line in Path(a.input).read_text().splitlines() if line.strip()]; row=next((r for r in rows if r.get('id')==RID),None); assert row is not None, RID; source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])"
if old_load not in s:
    raise SystemExit('row-loader marker not found')
s = s.replace(old_load, new_load, 1)

start = s.index("        retained=[]; behavioural_tests=0; future_calls=0; novelty_sizes=[]; target_recipe=None; target_origin=None")
end = s.index("        judged=finish(ef,sf,target_recipe) if target_recipe is not None else None", start)
replacement = f'''        # MSI repair-effect quotient.  A concrete equation is only a representative;
        # its developmental identity is the future-observation effect it induces.
        behavioural_tests=0; future_calls=0; target_recipe=None; target_origin=None
        effect_classes={{}}
        for score,q in candidates:
            fp,child,n=future_signature(q); behavioural_tests+=1; future_calls+=n
            if child is not None:
                target_recipe=child; target_origin='msi-effect-evaluation'; break
            novelty=fp-baseline
            if not novelty:continue
            # Exact behavioural morphism class: identical induced future effect.
            ek=tuple(sorted(fp))
            old=effect_classes.get(ek)
            item=(len(novelty),score,q)
            if old is None or (item[0],item[1]) < (old[0],old[1]):
                effect_classes[ek]=item

        # Coarsest justified strict repairs first: smallest positive distinction set.
        ranked=sorted(effect_classes.values(), key=lambda x:(x[0],x[1]))
        chosen=ranked[:{a.effect_keep}]
        retained=[q for _,_,q in chosen]
        novelty_sizes=[n for n,_,_ in chosen]
        effect_class_count=len(effect_classes)

        # Compose the selected behavioural morphism classes, preserving their
        # representative only for certificate replay.  Search/ranking below remains generic.
        closure_enum=0; closure_rounds_completed=0; closure_generated=[]
        if target_recipe is None and retained:
            partners=list(probes)+list(retained)
            frontier=list(retained)
            closure_seen=set((sf.alpha_signature(q.lhs,q.rhs),q.lhs,q.rhs) for q in partners)
            for cr in range({a.closure_rounds}):
                proposals=[]
                for ni,N in enumerate(frontier):
                    for pi,P in enumerate(partners):
                        for A,B,label in ((N,P,'msi-class-partner'),(P,N,'msi-partner-class')):
                            for ar in (False,True):
                                aa=orient(A,ar)
                                for br in (False,True):
                                    bb=orient(B,br)
                                    for path in m.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):
                                        z=origf(aa,bb,ni,pi,path)
                                        if z is None:continue
                                        closure_enum+=1
                                        if exact_target(ef,z):
                                            target_recipe=z; target_origin=label+'-round-'+str(cr+1); break
                                        k=(sf.alpha_signature(z.lhs,z.rhs),z.lhs,z.rhs)
                                        if k not in closure_seen:
                                            closure_seen.add(k); proposals.append((sf.target_score(z),z))
                                    if target_recipe:break
                                if target_recipe:break
                            if target_recipe:break
                        if target_recipe:break
                    if target_recipe:break
                closure_rounds_completed=cr+1
                if target_recipe:break
                proposals.sort(key=lambda x:x[0])
                frontier=[q for _,q in proposals[:{a.closure_new_per_round}]]
                closure_generated.append(len(frontier))
                if not frontier:break
                partners=partners+frontier
'''
s = s[:start] + replacement + s[end:]
old_out = "        out={'id':RID,'frontier_clauses':len(sf.clauses),'frontier_enumerated':enumf,'given_clauses':len(sg.clauses),'given_steps':givens,'given_enumerated':enumg,'cross_enumerated':cross_enum,'candidate_budget':len(candidates),'probe_partners':len(probes),'baseline_future_signatures':len(baseline),'baseline_future_calls':baseline_calls,'behavioural_tests':behavioural_tests,'future_calls':future_calls,'behavioural_retained':len(retained),'novelty_sizes':novelty_sizes,'closure_enumerated':closure_enum,'target_found':target_recipe is not None,'target_origin':target_origin,'judge':judged}\n"
new_out = "        out={'id':RID,'mode':'msi-minimal-repair-effect-class','frontier_clauses':len(sf.clauses),'frontier_enumerated':enumf,'given_clauses':len(sg.clauses),'given_steps':givens,'given_enumerated':enumg,'cross_enumerated':cross_enum,'candidate_budget':len(candidates),'probe_partners':len(probes),'baseline_future_signatures':len(baseline),'baseline_future_calls':baseline_calls,'behavioural_tests':behavioural_tests,'future_calls':future_calls,'effect_class_count':effect_class_count,'effect_keep':len(retained),'novelty_sizes':novelty_sizes,'closure_enumerated':closure_enum,'closure_rounds_completed':closure_rounds_completed,'closure_generated':closure_generated,'target_found':target_recipe is not None,'target_origin':target_origin,'judge':judged}\n"
if old_out not in s:
    raise SystemExit('output marker not found')
s=s.replace(old_out,new_out,1)

with tempfile.NamedTemporaryFile(mode='w', suffix='_msi_effect.py', prefix='_mg_', dir=SRC.parent, delete=False) as fh:
    fh.write(s); patched=Path(fh.name)
try:
    cmd=[sys.executable,str(patched),'--input',a.input,'--output',a.output,
         '--frontier-seconds',str(a.frontier_seconds),'--given-seconds',str(a.given_seconds),
         '--frontier-rounds',str(a.frontier_rounds),'--given-steps',str(a.given_steps),
         '--candidate-budget',str(a.candidate_budget),'--behavioural-keep',str(a.effect_keep),
         '--probe-partners',str(a.probe_partners)]
    raise SystemExit(subprocess.call(cmd,cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)

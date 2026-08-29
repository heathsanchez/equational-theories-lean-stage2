#!/usr/bin/env python3
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SRC=ROOT/'experiments/mathgraph/run_796_0040_behavioural_separator_exchange.py'

ap=argparse.ArgumentParser()
ap.add_argument('--input',required=True)
ap.add_argument('--output',required=True)
ap.add_argument('--frontier-seconds',type=float,default=30)
ap.add_argument('--given-seconds',type=float,default=10)
ap.add_argument('--frontier-rounds',type=int,default=3)
ap.add_argument('--given-steps',type=int,default=16)
a=ap.parse_args()

s=SRC.read_text()
marker='        # Candidate generation is broad, but retention is behavioural: a candidate must add\n'
if marker not in s:
    raise SystemExit('candidate marker not found')
prefix=s.split(marker,1)[0]

tail=r'''        # Residual-directed cross scan.  No target_score preselection and no
        # named intermediates: enumerate every unique cross consequence, then ask
        # whether composing it with the frozen union of both portfolios can close
        # the actual target equation in one verified inference.
        pool=[expf(c) for c in sf.clauses]+[expf(expg(c)) for c in sg.clauses]
        raw=[]; cross_enum=0; seen=set()
        for ai,A0 in enumerate(sf.clauses):
            A=expf(A0)
            for bi,B0 in enumerate(sg.clauses):
                B=expf(expg(B0))
                for ar in (False,True):
                    aa=orient(A,ar)
                    for br in (False,True):
                        bb=orient(B,br)
                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):
                            q=origf(aa,bb,ai,bi,path)
                            if q is None: continue
                            cross_enum+=1
                            k=(sf.alpha_signature(q.lhs,q.rhs),q.lhs,q.rhs)
                            if k in seen: continue
                            seen.add(k); raw.append(q)

        target_recipe=None; target_origin=None; closure_enum=0; scanned=0
        # Probe the full unique cross pool in generation order.  Each consequence
        # gets the same bounded continuation family; no syntactic rank truncates it.
        for qi,q in enumerate(raw):
            scanned+=1
            if exact_target(ef,q):
                target_recipe=q; target_origin='cross-direct'; break
            for pi,p in enumerate(pool):
                for A,B,label in ((q,p,'cross-partner'),(p,q,'partner-cross')):
                    for ar in (False,True):
                        aa=orient(A,ar)
                        for br in (False,True):
                            bb=orient(B,br)
                            for path in m.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):
                                z=origf(aa,bb,qi,pi,path)
                                if z is None: continue
                                closure_enum+=1
                                if exact_target(ef,z):
                                    target_recipe=z; target_origin=label; break
                            if target_recipe: break
                        if target_recipe: break
                    if target_recipe: break
                if target_recipe: break
            if target_recipe: break

        judged=finish(ef,sf,target_recipe) if target_recipe is not None else None
        out={'id':RID,'frontier_clauses':len(sf.clauses),'frontier_enumerated':enumf,
             'given_clauses':len(sg.clauses),'given_steps':givens,'given_enumerated':enumg,
             'cross_enumerated':cross_enum,'unique_cross':len(raw),'cross_scanned':scanned,
             'closure_enumerated':closure_enum,'target_found':target_recipe is not None,
             'target_origin':target_origin,'judge':judged}
        Path(a.output).parent.mkdir(parents=True,exist_ok=True)
        Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
        print('RESIDUAL_DIRECTED_CROSS_SCAN',json.dumps(out,sort_keys=True),flush=True)
    finally:
        hp.unlink(missing_ok=True)
if __name__=='__main__':main()
'''

patched_text=prefix+tail
with tempfile.NamedTemporaryFile(mode='w',suffix='_residual_directed_runtime.py',prefix='_mg_',dir=SRC.parent,delete=False) as fh:
    fh.write(patched_text); patched=Path(fh.name)
try:
    cmd=[sys.executable,str(patched),'--input',a.input,'--output',a.output,
         '--frontier-seconds',str(a.frontier_seconds),'--given-seconds',str(a.given_seconds),
         '--frontier-rounds',str(a.frontier_rounds),'--given-steps',str(a.given_steps)]
    raise SystemExit(subprocess.call(cmd,cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)

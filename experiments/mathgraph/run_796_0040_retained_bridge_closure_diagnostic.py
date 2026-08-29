#!/usr/bin/env python3
"""Post-hoc diagnostic: once autonomous 0040 selection is complete, locate the
known f259 bridge and f15 partner and test the existing closure operator on them.
Hidden trace identities are diagnostics only; they never steer generation,
ranking, retention, or the autonomy path.
"""
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SRC=ROOT/'experiments/mathgraph/run_796_0040_behavioural_separator_exchange.py'

ap=argparse.ArgumentParser()
ap.add_argument('--input',required=True); ap.add_argument('--output',required=True)
ap.add_argument('--frontier-seconds',type=float,default=30); ap.add_argument('--given-seconds',type=float,default=10)
ap.add_argument('--frontier-rounds',type=int,default=3); ap.add_argument('--given-steps',type=int,default=16)
ap.add_argument('--candidate-budget',type=int,default=512); ap.add_argument('--behavioural-keep',type=int,default=512)
ap.add_argument('--probe-partners',type=int,default=64); a=ap.parse_args()

s=SRC.read_text()
needle="""        # If no target appeared during the signature probe, give retained separators one shared closure pass.\n"""
inject=r"""        # POST-HOC ONLY: autonomous candidate generation, ranking and retention
        # are complete before hidden trace identities are loaded.
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
        def inline_pair(r,eng):return (h.inline_engine_names(r.lhs,eng.reverse_constants),h.inline_engine_names(r.rhs,eng.reverse_constants))
        def diag_match(r,fid,eng=ef):
            if fid not in wsig:return False
            try:return alpha_pair(*inline_pair(r,eng))==wsig[fid]
            except Exception:return False

        f259_retained=[i for i,r in enumerate(retained,1) if diag_match(r,'f259',ef)]
        f15_pool=[i for i,r in enumerate(pool,1) if diag_match(r,'f15',ef) or diag_match(r,'f15',eg)]
        pair_probe={'enumerated':0,'f278':False,'target':False,'hits':[]}
        if f259_retained and f15_pool:
            N=retained[f259_retained[0]-1]; P=pool[f15_pool[0]-1]
            for order,(A,B) in enumerate(((N,P),(P,N))):
                for ar in (False,True):
                    aa=orient(A,ar)
                    for br in (False,True):
                        bb=orient(B,br)
                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):
                            z=origf(aa,bb,9900+order,9950+order,path)
                            if z is None:continue
                            pair_probe['enumerated']+=1
                            is278=diag_match(z,'f278',ef); ist=exact_target(z)
                            if is278:pair_probe['f278']=True
                            if ist:pair_probe['target']=True
                            if is278 or ist:
                                pair_probe['hits'].append({'order':order,'ar':ar,'br':br,'path':list(path),'f278':is278,'target':ist})
        diag={'posthoc_hidden_trace_only':True,'candidate_budget':len(candidates),'behavioural_tests':behavioural_tests,'behavioural_retained':len(retained),'f259_retained_indices':f259_retained,'f15_pool_indices':f15_pool[:16],'retained_bridge_f15_probe':pair_probe}
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(diag,indent=2,sort_keys=True)+'\n')
        print('RETAINED_BRIDGE_CLOSURE_DIAGNOSTIC',json.dumps(diag,sort_keys=True),flush=True)
        return

        # If no target appeared during the signature probe, give retained separators one shared closure pass.
"""
if needle not in s: raise SystemExit('closure marker not found')
s=s.replace(needle,inject,1)
with tempfile.NamedTemporaryFile(mode='w',suffix='_retained_bridge_runtime.py',prefix='_mg_',dir=SRC.parent,delete=False) as fh:
    fh.write(s); patched=Path(fh.name)
try:
    cmd=[sys.executable,str(patched),'--input',a.input,'--output',a.output,'--frontier-seconds',str(a.frontier_seconds),'--given-seconds',str(a.given_seconds),'--frontier-rounds',str(a.frontier_rounds),'--given-steps',str(a.given_steps),'--candidate-budget',str(a.candidate_budget),'--behavioural-keep',str(a.behavioural_keep),'--probe-partners',str(a.probe_partners)]
    raise SystemExit(subprocess.call(cmd,cwd=ROOT))
finally:
    patched.unlink(missing_ok=True)

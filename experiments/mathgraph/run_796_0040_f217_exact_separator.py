#!/usr/bin/env python3
import argparse, importlib.util, json, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / 'submissions/mathgraph/solver.py'
HELPER_URL = 'https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/normal0040-alpha-self-overlap-20260826/experiments/mathgraph/run_normal0040_materialized_self_overlap.py'
TRACE_URL = 'https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path); mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod

def alpha_sig(rigid,a,b):
    n={}; x=rigid.alpha_canonical_term(a,n); y=rigid.alpha_canonical_term(b,n); return min((x,y),(y,x))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
    m=load(SOLVER,'mg796f217'); rigid=m.RigidSuperpositionModule()
    hp=ROOT/'experiments/mathgraph/_runtime_old_0040_helper.py'; hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h=load(hp,'mgoldf217'); row=h.load_row(a.input); target=m.parse_equation(row['equation2'])
        trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
        defs={}; wanted={}
        for block in h.fof_blocks(proof):
            q=h.parse_fof(block)
            if not q: continue
            fid,kind,formula,tail=q
            try: eq=h.formula_equality(formula)
            except Exception: eq=None
            if eq is None: continue
            x,y=eq
            if kind=='definition':
                if x[0]=='var' and x[1].startswith('sF'): defs[x[1]]=y
                elif y[0]=='var' and y[1].startswith('sF'): defs[y[1]]=x
            elif fid in ('f19','f196','f217'):
                wanted[fid]=(h.map_rigids(h.inline_defs(x,defs),target[2]),h.map_rigids(h.inline_defs(y,defs),target[2]))
        # Fake recipes are used only for structural critical-pair enumeration.
        def rec(fid,rev=False):
            x,y=wanted[fid]
            if rev: x,y=y,x
            return m.Recipe(x,y,'separator',())
        target_sig=alpha_sig(rigid,*wanted['f217'])
        raw=[]; hits=[]
        for order,(lf,rf) in enumerate((('f19','f196'),('f196','f19'))):
            for lr in (False,True):
                left=rec(lf,lr)
                for rr in (False,True):
                    right=rec(rf,rr)
                    for path in rigid.nonvariable_positions(left.lhs,maximum_depth=12,include_root=True):
                        try: q=m.CompactSuperpositionSearch.critical_pair
                        except AttributeError: q=None
                        # Use a tiny real search object solely to call its implementation.
                        if q is None:
                            continue
        # Instantiate the actual class via a minimal target-grounded engine so we use production critical_pair.
        source=m.parse_equation(row['equation1'])
        limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':5.0,'maximum_depth':12,'maximum_term_size':260})
        eng=m.TargetGroundedRefutation(source,target,__import__('time').monotonic()+5.0,limits)
        for label,(lf,rf) in (('f19-f196',('f19','f196')),('f196-f19',('f196','f19'))):
            for lr in (False,True):
                left=rec(lf,lr)
                for rr in (False,True):
                    right=rec(rf,rr)
                    for path in rigid.nonvariable_positions(left.lhs,maximum_depth=12,include_root=True):
                        try: child=eng.search.critical_pair(left,right,0,1,path)
                        except Exception as e:
                            raw.append({'order':label,'left_rev':lr,'right_rev':rr,'path':list(path),'error':type(e).__name__}); continue
                        if child is None: continue
                        sig=alpha_sig(rigid,child.lhs,child.rhs)
                        item={'order':label,'left_rev':lr,'right_rev':rr,'path':list(path),'lhs':m.render_term(child.lhs),'rhs':m.render_term(child.rhs),'alpha_hit':sig==target_sig}
                        raw.append(item)
                        if item['alpha_hit']: hits.append(item)
        out={'id':RID,'exact_parent_structural_hits':hits,'raw_candidate_count':len(raw),'raw_candidates':raw[:80],
             'wanted':{k:[m.render_term(x),m.render_term(y)] for k,(x,y) in wanted.items()}}
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
        print('F217_EXACT_SEPARATOR',json.dumps({'hits':len(hits),'raw':len(raw),'first':raw[:8]},sort_keys=True),flush=True)
    finally:
        hp.unlink(missing_ok=True)
if __name__=='__main__': main()

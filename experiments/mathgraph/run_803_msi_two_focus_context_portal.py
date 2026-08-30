#!/usr/bin/env python3
"""Frozen two-focus context grammar census on the 0042 residual.

Strict extension of the one-hole context portal: inspect only the 53 classes
that survive the existing depth-2 refinement, but represent a continuation by
the relation between TWO non-overlapping structural sites in the rewritten
parent. No proof-search depth, candidate budget, probe basis, ranking, closure,
or judge budget is increased.
"""
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SRC=ROOT/'experiments/mathgraph/run_799_msi_adaptive_compositional_separator.py'


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--id',required=True); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True)
    ap.add_argument('--frontier-seconds',type=float,default=12); ap.add_argument('--given-seconds',type=float,default=5)
    ap.add_argument('--frontier-rounds',type=int,default=3); ap.add_argument('--given-steps',type=int,default=16)
    ap.add_argument('--candidate-budget',type=int,default=256); ap.add_argument('--probe-partners',type=int,default=16)
    ap.add_argument('--collision-members',type=int,default=4); ap.add_argument('--child-width',type=int,default=8)
    ap.add_argument('--depth3-members',type=int,default=3); ap.add_argument('--depth3-child-width',type=int,default=4)
    ap.add_argument('--effect-keep',type=int,default=32)
    a=ap.parse_args()

    s=SRC.read_text()
    marker="        def depth3_signature(rule):\n"
    if marker not in s: raise SystemExit('depth3 marker not found')
    block=r'''        # Two-focus relational context grammar. Measurement only.
        two_focus_modes=('full','minus_order','minus_partner','relation_only','one_focus_control','endpoint_shape')
        two_focus_split_classes={{k:0 for k in two_focus_modes}}
        two_focus_domain_split_classes={{k:0 for k in two_focus_modes}}
        two_focus_split_indices={{k:[] for k in two_focus_modes}}
        two_focus_attempts=0; two_focus_successes=0; two_focus_future_calls=0
        _tf_future_cache={{}}

        def tf_shape(t):
            if t[0]=='var': return ('V',)
            return ('O',tf_shape(t[1]),tf_shape(t[2]))

        def tf_prefix(a,b): return len(a)<=len(b) and tuple(a)==tuple(b[:len(a)])

        def tf_two_context(t,p1,p2,prefix=()):
            if tuple(prefix)==tuple(p1): return ('H1',)
            if tuple(prefix)==tuple(p2): return ('H2',)
            if t[0]=='var': return ('V',)
            return ('O',tf_two_context(t[1],p1,p2,prefix+('L',)),tf_two_context(t[2],p1,p2,prefix+('R',)))

        def tf_one_context(t,path):
            if not path: return ('H',)
            d=path[0]
            if t[0]!='op': return ('BAD',tuple(path))
            if d=='L': return ('O',tf_one_context(t[1],path[1:]),tf_shape(t[2]))
            return ('O',tf_shape(t[1]),tf_one_context(t[2],path[1:]))

        def tf_partner(r):
            return tuple(sorted((tf_shape(r.lhs),tf_shape(r.rhs)),key=str))

        def tf_project(base,mode):
            order,relation,f1,f2,one,partner,endpoint=base
            if mode=='full': return (order,relation,f1,f2,partner)
            if mode=='minus_order': return (relation,f1,f2,partner)
            if mode=='minus_partner': return (order,relation,f1,f2)
            if mode=='relation_only': return (relation,f1,f2)
            if mode=='one_focus_control': return (one,f1,partner)
            if mode=='endpoint_shape': return (endpoint,)
            raise ValueError(mode)

        def tf_endpoint(z): return (sf.alpha_signature(z.lhs,z.rhs),z.lhs,z.rhs)
        def tf_future(z):
            nonlocal two_focus_future_calls
            k=tf_endpoint(z)
            if k not in _tf_future_cache:
                fp,_,n=future_signature(z); two_focus_future_calls+=n
                _tf_future_cache[k]=tuple(sorted(fp,key=str))
            return _tf_future_cache[k]

        def tf_records(rule):
            nonlocal two_focus_attempts,two_focus_successes
            out=[]
            for local_pi,p in enumerate(small_probes):
                pi=selected_probe_indices[local_pi]
                for order,(A,B) in enumerate(((rule,p),(p,rule))):
                    for ar in (False,True):
                        aa=orient(A,ar)
                        for br in (False,True):
                            bb=orient(B,br)
                            poss=list(m.nonvariable_positions(aa.lhs,maximum_depth=6,include_root=True))
                            for p1 in poss:
                                others=[p2 for p2 in poss if p2!=p1 and not tf_prefix(p1,p2) and not tf_prefix(p2,p1)]
                                if not others: continue
                                one=tf_one_context(aa.lhs,p1); f1=tf_shape(m.get_subterm(aa.lhs,p1)); partner=tf_partner(bb)
                                z=origf(aa,bb,0,pi,p1)
                                for p2 in others[:4]:
                                    relation=tf_two_context(aa.lhs,p1,p2); f2=tf_shape(m.get_subterm(aa.lhs,p2))
                                    two_focus_attempts+=1
                                    if z is None: endpoint=('UNDEFINED',)
                                    else:
                                        two_focus_successes+=1
                                        endpoint=tuple(sorted((tf_shape(z.lhs),tf_shape(z.rhs)),key=str))
                                    out.append(((order,relation,f1,f2,one,partner,endpoint),z))
            return out

        def tf_signature(records,universe,mode,outputs):
            by={{}}
            for base,z in records:
                pk=tf_project(base,mode); ent=by.setdefault(pk,[])
                if z is not None: ent.append(z)
            domain=tuple(sorted(((pk,bool(by.get(pk))) for pk in universe),key=str))
            if not outputs: return domain
            obs=[]
            for pk in sorted(universe,key=str):
                zs=by.get(pk,[])
                if not zs: obs.append((pk,('UNDEFINED',))); continue
                vals=set()
                seen=set()
                for z in zs:
                    ek=tf_endpoint(z)
                    if ek in seen: continue
                    seen.add(ek); vals.add(tf_future(z))
                    if len(seen)>={a.child_width}: break
                obs.append((pk,tuple(sorted(vals,key=str))))
            return tuple(obs)

        for stable_i,members0 in enumerate(depth2_remaining):
            members=members0[:{a.depth3_members}]
            recs=[tf_records(q) for _,q in members]
            for mode in two_focus_modes:
                universe=set()
                for rec in recs:
                    for base,_ in rec: universe.add(tf_project(base,mode))
                dom=[tf_signature(rec,universe,mode,False) for rec in recs]
                beh=[tf_signature(rec,universe,mode,True) for rec in recs]
                if len(set(map(str,dom)))>1: two_focus_domain_split_classes[mode]+=1
                if len(set(map(str,beh)))>1:
                    two_focus_split_classes[mode]+=1; two_focus_split_indices[mode].append(stable_i)

        def depth3_signature(rule):
'''
    s=s.replace(marker,block,1)
    seam="'compose_calls':compose_calls,"
    injected=("'compose_calls':compose_calls,"
              "'two_focus_modes':list(two_focus_modes),"
              "'two_focus_split_classes':two_focus_split_classes,"
              "'two_focus_domain_split_classes':two_focus_domain_split_classes,"
              "'two_focus_split_indices':two_focus_split_indices,"
              "'two_focus_attempts':two_focus_attempts,"
              "'two_focus_successes':two_focus_successes,"
              "'two_focus_future_calls':two_focus_future_calls,")
    if seam not in s: raise SystemExit('adaptive output compose seam not found')
    s=s.replace(seam,injected,1)
    s=s.replace("'mode':'msi-adaptive-compositional-separator'","'mode':'msi-two-focus-context-portal'",1)
    with tempfile.NamedTemporaryFile(mode='w',suffix='_msi_two_focus.py',prefix='_mg_',dir=SRC.parent,delete=False) as fh:
        fh.write(s); patched=Path(fh.name)
    try:
        cmd=[sys.executable,str(patched),'--id',a.id,'--input',a.input,'--output',a.output,
             '--frontier-seconds',str(a.frontier_seconds),'--given-seconds',str(a.given_seconds),
             '--frontier-rounds',str(a.frontier_rounds),'--given-steps',str(a.given_steps),
             '--candidate-budget',str(a.candidate_budget),'--probe-partners',str(a.probe_partners),
             '--collision-members',str(a.collision_members),'--child-width',str(a.child_width),
             '--depth3-members',str(a.depth3_members),'--depth3-child-width',str(a.depth3_child_width),
             '--effect-keep',str(a.effect_keep)]
        raise SystemExit(subprocess.call(cmd,cwd=ROOT))
    finally: patched.unlink(missing_ok=True)

if __name__=='__main__': main()

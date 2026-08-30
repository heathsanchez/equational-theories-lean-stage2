#!/usr/bin/env python3
"""Frozen context/type-valued identity census on the 0042 depth-3-stable residual.

This wraps the already-frozen adaptive compositional separator. It does not
increase search depth, candidate budget, probe count, collision width, closure,
or judge budget. Only the 53 classes that survive the existing depth-2 split
are inspected.

The intervention replaces literal derivation provenance by theorem-independent
structural continuation coordinates built from:
  * context-with-hole shape in the rewritten parent;
  * focused-subterm shape;
  * partner equation shape;
  * optional parent/partner order.
Variables are erased to one symbol, so this is a structural type/context test,
not an instance lookup. Applicability/domain and behavioural observations are
reported separately. No proof IDs, hidden traces, named intermediates, or
row-specific lemmas are used.
"""
import argparse, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'experiments/mathgraph/run_799_msi_adaptive_compositional_separator.py'


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

    block=r'''        # Context/type-valued identity portal. This is a census on
        # depth2_remaining only; it does not generate/promote proof-search states.
        context_type_modes=('full','minus_order','minus_partner','context_only','partner_only','endpoint_shape')
        context_type_split_classes={{k:0 for k in context_type_modes}}
        context_type_domain_split_classes={{k:0 for k in context_type_modes}}
        context_type_split_indices={{k:[] for k in context_type_modes}}
        context_type_attempts=0; context_type_successes=0; context_type_future_calls=0
        _ct_future_cache={{}}

        def ct_term_shape(t):
            if t[0]=='var': return ('V',)
            return ('O',ct_term_shape(t[1]),ct_term_shape(t[2]))

        def ct_context_shape(t,path):
            if not path: return ('H',)
            if t[0]!='op': return ('BAD',tuple(path))
            d=path[0]
            if d=='L': return ('O',ct_context_shape(t[1],path[1:]),ct_term_shape(t[2]))
            if d=='R': return ('O',ct_term_shape(t[1]),ct_context_shape(t[2],path[1:]))
            return ('BAD',tuple(path))

        def ct_partner_shape(r):
            a0=ct_term_shape(r.lhs); b0=ct_term_shape(r.rhs)
            return tuple(sorted((a0,b0),key=str))

        def ct_project(rec,mode):
            order,ctx,focus,partner,endpoint=rec
            if mode=='full': return (order,ctx,focus,partner)
            if mode=='minus_order': return (ctx,focus,partner)
            if mode=='minus_partner': return (order,ctx,focus)
            if mode=='context_only': return (ctx,focus)
            if mode=='partner_only': return (partner,)
            if mode=='endpoint_shape': return (endpoint,)
            raise ValueError(mode)

        def ct_endpoint_key(z): return (sf.alpha_signature(z.lhs,z.rhs),z.lhs,z.rhs)

        def ct_future(z):
            nonlocal context_type_future_calls
            k=ct_endpoint_key(z)
            if k not in _ct_future_cache:
                fp,_,n=future_signature(z); context_type_future_calls+=n
                _ct_future_cache[k]=tuple(sorted(fp,key=str))
            return _ct_future_cache[k]

        def ct_records(rule):
            nonlocal context_type_attempts,context_type_successes
            out=[]
            for local_pi,p in enumerate(small_probes):
                pi=selected_probe_indices[local_pi]
                for order,(A,B) in enumerate(((rule,p),(p,rule))):
                    for ar in (False,True):
                        aa=orient(A,ar)
                        for br in (False,True):
                            bb=orient(B,br)
                            for path in m.nonvariable_positions(aa.lhs,maximum_depth=6,include_root=True):
                                ctx=ct_context_shape(aa.lhs,path)
                                focus=ct_term_shape(m.get_subterm(aa.lhs,path))
                                partner=ct_partner_shape(bb)
                                z=origf(aa,bb,0,pi,path); context_type_attempts+=1
                                if z is None:
                                    endpoint=('UNDEFINED',)
                                else:
                                    context_type_successes+=1
                                    endpoint=tuple(sorted((ct_term_shape(z.lhs),ct_term_shape(z.rhs)),key=str))
                                out.append(((order,ctx,focus,partner,endpoint),z))
            return out

        def ct_signature(records,universe,mode,outputs):
            by={{}}
            for base,z in records:
                pk=ct_project(base,mode)
                ent=by.setdefault(pk,[])
                if z is not None: ent.append(z)
            domain=tuple(sorted(((pk,bool(by.get(pk))) for pk in universe),key=str))
            if not outputs: return domain
            obs=[]
            for pk in sorted(universe,key=str):
                zs=by.get(pk,[])
                if not zs:
                    obs.append((pk,('UNDEFINED',))); continue
                vals=set()
                for z in zs[:{a.child_width}]: vals.add(ct_future(z))
                obs.append((pk,tuple(sorted(vals,key=str))))
            return tuple(obs)

        for stable_i,members0 in enumerate(depth2_remaining):
            members=members0[:{a.depth3_members}]
            recs=[ct_records(q) for _,q in members]
            for mode in context_type_modes:
                universe=set()
                for rec in recs:
                    for base,_ in rec: universe.add(ct_project(base,mode))
                dom=[ct_signature(rec,universe,mode,False) for rec in recs]
                beh=[ct_signature(rec,universe,mode,True) for rec in recs]
                if len(set(map(str,dom)))>1:
                    context_type_domain_split_classes[mode]+=1
                if len(set(map(str,beh)))>1:
                    context_type_split_classes[mode]+=1
                    context_type_split_indices[mode].append(stable_i)

        def depth3_signature(rule):
'''
    s=s.replace(marker,block,1)

    seam="'compose_calls':compose_calls,"
    injected=(
        "'compose_calls':compose_calls,"
        "'context_type_modes':list(context_type_modes),"
        "'context_type_split_classes':context_type_split_classes,"
        "'context_type_domain_split_classes':context_type_domain_split_classes,"
        "'context_type_split_indices':context_type_split_indices,"
        "'context_type_attempts':context_type_attempts,"
        "'context_type_successes':context_type_successes,"
        "'context_type_future_calls':context_type_future_calls,"
    )
    if seam not in s: raise SystemExit('adaptive output compose seam not found')
    s=s.replace(seam,injected,1)
    s=s.replace("'mode':'msi-adaptive-compositional-separator'","'mode':'msi-context-type-portal'",1)

    with tempfile.NamedTemporaryFile(mode='w',suffix='_msi_context_type.py',prefix='_mg_',dir=SRC.parent,delete=False) as fh:
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
    finally:
        patched.unlink(missing_ok=True)

if __name__=='__main__': main()

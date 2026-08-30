#!/usr/bin/env python3
"""Frozen-budget provenance-bearing continuation-edge ablation for order-5 residuals.

This wraps the already-frozen adaptive compositional separator. It does not
increase search depth, frontier time, candidate budget, probe count, collision
width, or closure budget. It instruments the exact depth-2 continuation
boundary that previously discarded provenance and asks whether merged classes
split when continuation identity / applicability is retained.

A primitive continuation coordinate is
  (order, rule_orientation, partner_orientation, probe_index, rewrite_path).
For each one-step collision class we replay the same local depth-2 continuation
basis and compare six representations:
  full provenance; erase order; erase path; erase orientations; erase partner;
  endpoint-only.
Applicability (including undefined coordinates) is recorded separately from
successful-output behaviour. No proof IDs, hidden traces, named intermediates,
or target-specific lemmas are used.
"""
import subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'experiments/mathgraph/run_799_msi_adaptive_compositional_separator.py'


def main():
    s = SRC.read_text()

    marker = "        selected_probe_hits=[probe_hits[i] for i in selected_probe_indices]\n\n        def first_children(rule,width,maximum_depth=6):\n"
    if marker not in s:
        raise SystemExit('active-probe marker not found')

    # This block is inserted inside the adaptive runner's f-string template.
    # Literal runtime braces are doubled so they survive that generation layer.
    block = r'''        selected_probe_hits=[probe_hits[i] for i in selected_probe_indices]

        # Provenance-edge ablation. Search depth/basis are frozen; only the
        # representation of an already-enumerated continuation changes.
        provenance_modes=('full','minus_order','minus_path','minus_orientations','minus_partner','endpoint_only')
        provenance_split_classes={{k:0 for k in provenance_modes}}
        provenance_domain_split_classes={{k:0 for k in provenance_modes}}
        provenance_examples=[]
        provenance_attempts=0; provenance_successes=0
        provenance_same_endpoint_multi_maps=0; provenance_same_endpoint_max_maps=0
        provenance_future_calls=0
        _prov_future_cache={{}}

        def prov_project(prov,mode):
            order,ar,br,pi,path=prov
            if mode=='full': return prov
            if mode=='minus_order': return (ar,br,pi,path)
            if mode=='minus_path': return (order,ar,br,pi)
            if mode=='minus_orientations': return (order,pi,path)
            if mode=='minus_partner': return (order,ar,br,path)
            if mode=='endpoint_only': return ('endpoint',)
            raise ValueError(mode)

        def prov_endpoint_key(z):
            return (sf.alpha_signature(z.lhs,z.rhs),z.lhs,z.rhs)

        def enumerate_provenance_edges(rule):
            nonlocal provenance_attempts,provenance_successes
            rec=[]
            for local_pi,p in enumerate(small_probes):
                pi=selected_probe_indices[local_pi]
                for order,(A,B) in enumerate(((rule,p),(p,rule))):
                    for ar in (False,True):
                        aa=orient(A,ar)
                        for br in (False,True):
                            bb=orient(B,br)
                            paths=list(m.nonvariable_positions(aa.lhs,maximum_depth=6,include_root=True))
                            for path0 in paths:
                                path=tuple(path0)
                                prov=(order,ar,br,pi,path)
                                z=origf(aa,bb,0,pi,path0)
                                provenance_attempts+=1
                                if z is not None: provenance_successes+=1
                                rec.append((prov,z))
            return rec

        def cached_future(z):
            nonlocal provenance_future_calls
            k=prov_endpoint_key(z)
            if k not in _prov_future_cache:
                fp,_,n=future_signature(z)
                _prov_future_cache[k]=(tuple(sorted(fp,key=str)),n)
                provenance_future_calls+=n
            return _prov_future_cache[k][0]

        def member_signature(records,universe,mode,with_outputs=True):
            # A projected coordinate is applicable if any full coordinate that
            # maps to it succeeds. Coordinates absent from this member but
            # present elsewhere in the class are explicitly UNDEFINED.
            app={{}}
            success=[]
            for prov,z in records:
                pk=prov_project(prov,mode)
                ok=z is not None
                app[pk]=app.get(pk,False) or ok
                if ok: success.append((sf.target_score(z),prov,z))
            domain=tuple(sorted(((pk, bool(app.get(pk,False))) for pk in universe),key=str))
            if not with_outputs: return domain
            success.sort(key=lambda x:x[0])
            chosen=[]; seen=set()
            for score,prov,z in success:
                pk=prov_project(prov,mode); ek=prov_endpoint_key(z)
                dk=ek if mode=='endpoint_only' else (pk,ek)
                if dk in seen: continue
                seen.add(dk); chosen.append((pk,ek,z))
                if len(chosen)>={a.child_width}: break
            obs=[]
            for pk,ek,z in chosen:
                fp=cached_future(z)
                if mode=='endpoint_only': obs.append((str(ek[0]),fp))
                else: obs.append((pk,str(ek[0]),fp))
            return (domain,tuple(sorted(obs,key=str)))

        # Replay only the already-defined one-step collision classes. This is
        # a representation census, not another proof-search expansion.
        for cls_i,cls in enumerate(collision_classes):
            members=sorted(cls,key=lambda x:x[0])[:{a.collision_members}]
            edge_sets=[]
            for _,q in members:
                rec=enumerate_provenance_edges(q); edge_sets.append(rec)
                by_endpoint={{}}
                for prov,z in rec:
                    if z is None: continue
                    by_endpoint.setdefault(prov_endpoint_key(z),set()).add(prov)
                for ps in by_endpoint.values():
                    if len(ps)>1:
                        provenance_same_endpoint_multi_maps+=1
                        provenance_same_endpoint_max_maps=max(provenance_same_endpoint_max_maps,len(ps))
            for mode in provenance_modes:
                universe=set()
                for rec in edge_sets:
                    for prov,_ in rec: universe.add(prov_project(prov,mode))
                dom_sigs=[member_signature(rec,universe,mode,False) for rec in edge_sets]
                full_sigs=[member_signature(rec,universe,mode,True) for rec in edge_sets]
                if len(set(map(str,dom_sigs)))>1:
                    provenance_domain_split_classes[mode]+=1
                if len(set(map(str,full_sigs)))>1:
                    provenance_split_classes[mode]+=1
                    if mode=='full' and len(provenance_examples)<8:
                        differing=[]
                        for pk in sorted(universe,key=str):
                            vals=[]
                            for rec in edge_sets:
                                ok=False
                                for prov,z in rec:
                                    if prov_project(prov,mode)==pk and z is not None:
                                        ok=True; break
                                vals.append(ok)
                            if len(set(vals))>1:
                                differing.append({{'continuation':repr(pk),'applicable':vals}})
                                if len(differing)>=3: break
                        provenance_examples.append({{'collision_class_index':cls_i,'member_count':len(members),'domain_witnesses':differing}})

        def first_children(rule,width,maximum_depth=6):
'''
    s = s.replace(marker, block, 1)

    # Patch only the stable field seam rather than matching the entire output
    # record; the latter changed as the adaptive experiment accumulated metrics.
    seam = "'compose_calls':compose_calls,"
    injected = (
        "'compose_calls':compose_calls,"
        "'provenance_modes':list(provenance_modes),"
        "'provenance_split_classes':provenance_split_classes,"
        "'provenance_domain_split_classes':provenance_domain_split_classes,"
        "'provenance_attempts':provenance_attempts,"
        "'provenance_successes':provenance_successes,"
        "'provenance_same_endpoint_multi_maps':provenance_same_endpoint_multi_maps,"
        "'provenance_same_endpoint_max_maps':provenance_same_endpoint_max_maps,"
        "'provenance_future_calls':provenance_future_calls,"
        "'provenance_examples':provenance_examples,"
    )
    if seam not in s:
        raise SystemExit('adaptive output compose seam not found')
    s = s.replace(seam, injected, 1)
    s = s.replace("'mode':'msi-adaptive-compositional-separator'",
                  "'mode':'msi-provenance-edge-ablation'", 1)

    with tempfile.NamedTemporaryFile(mode='w', suffix='_msi_provenance.py',
                                     prefix='_mg_', dir=SRC.parent, delete=False) as fh:
        fh.write(s)
        patched = Path(fh.name)
    try:
        raise SystemExit(subprocess.call([sys.executable, str(patched), *sys.argv[1:]], cwd=ROOT))
    finally:
        patched.unlink(missing_ok=True)


if __name__ == '__main__':
    main()

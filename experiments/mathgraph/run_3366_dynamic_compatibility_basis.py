import importlib.util
import json
import sys
import time
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('sep18_helper_3366_compat', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)

MAX_NODES = 50000
MAX_TERM_SIZE = 180
FRONTIER_CAP = 160
ROUNDS = 8
BASIS_CAP = 6


def main():
    eqs = h.load_equations(); m = h.load_solver()
    source = m.parse_equation(eqs[3366]); target = m.parse_equation(eqs[41])
    tl, tr = target[:2]
    target_terms = set(m.walk_subterms(tl)) | set(m.walk_subterms(tr))

    baseline = m.EqualitySearch(source, target, time.monotonic() + 8.0)
    baseline_result = baseline.solve()
    baseline_found = isinstance(baseline_result, tuple) and len(baseline_result) == 2
    baseline_replayed = False
    if baseline_found:
        bn, br = baseline_result
        try:
            baseline_replayed = bool(m.replay_dag(source, bn, br))
        except TypeError:
            baseline_replayed = bool(m.replay_dag(source, bn, br,
                maximum_term_size=getattr(baseline, 'max_term_size', 256),
                maximum_nodes=getattr(baseline, 'max_derivation_nodes', 50000)))

    seed_limits = {
        'max_term_size': MAX_TERM_SIZE,
        'max_pool_terms': 80,
        'max_core_terms': 18,
        'max_source_attempts': 120000,
        'max_source_edges': 4000,
        'max_derivation_nodes': 6000,
        'max_graph_edges': 5000,
        'max_congruence_rounds': 0,
    }
    seed = m.EqualitySearch(source, target, time.monotonic() + 12.0, seed_limits)
    seed_pool = seed.make_pool(); seed.initial_pool = tuple(seed_pool); seed.instantiate_sources(seed_pool)
    raw_candidates = [n for n in seed.nodes if n.kind in ('source instance', 'source reentry')]

    # Deduplicate source instances extensionally. Both orientations remain selectable.
    candidate_records = []
    seen = set()
    for n in raw_candidates:
        key = (n.lhs, n.rhs, tuple(n.substitution), bool(getattr(n, 'orientation', False)))
        if key in seen: continue
        seen.add(key)
        candidate_records.append(n)

    nodes=[]; depth=[]; best={}; source_cache={}
    def add(node,d):
        if len(nodes) >= MAX_NODES: return None
        key=(node.lhs,node.rhs); old=best.get(key)
        if old is not None and depth[old] <= d: return old
        nodes.append(node); depth.append(d); idx=len(nodes)-1; best[key]=idx; return idx
    def M(a,b): return ('op',a,b)
    def R(t): return add(m.EqualityNode(t,t,'reflexivity',constructor='dynamic-compatibility-basis'),0)
    def S(i,d):
        p=nodes[i]; return add(m.EqualityNode(p.rhs,p.lhs,'symmetry',parents=(i,),constructor='dynamic-compatibility-basis'),d)
    def T(i,j,d):
        a,b=nodes[i],nodes[j]
        if a.rhs != b.lhs: return None
        return add(m.EqualityNode(a.lhs,b.rhs,'transitivity',parents=(i,j),constructor='dynamic-compatibility-basis'),d)
    def C(i,j,d):
        a,b=nodes[i],nodes[j]
        lhs=M(a.lhs,b.lhs); rhs=M(a.rhs,b.rhs)
        if m.term_size(lhs)>MAX_TERM_SIZE or m.term_size(rhs)>MAX_TERM_SIZE: return None
        i1=add(m.EqualityNode(M(a.lhs,b.lhs),M(a.rhs,b.lhs),'congruence on left child',parents=(i,),context=('left',b.lhs),constructor='dynamic-compatibility-basis'),d)
        if i1 is None: return None
        i2=add(m.EqualityNode(M(a.rhs,b.lhs),M(a.rhs,b.rhs),'congruence on right child',parents=(j,),context=('right',a.rhs),constructor='dynamic-compatibility-basis'),d)
        if i2 is None: return None
        return T(i1,i2,d)

    def ensure_source(n, reverse=False):
        key=(n.lhs,n.rhs,tuple(n.substitution),bool(getattr(n,'orientation',False)),reverse)
        if key in source_cache: return source_cache[key]
        copied=m.EqualityNode(n.lhs,n.rhs,'source instance',substitution=n.substitution,
            orientation=getattr(n,'orientation',False),constructor='dynamic-compatibility-basis')
        i=add(copied,0)
        if i is None: return None
        if reverse:
            i=S(i,0)
        source_cache[key]=i
        return i

    visible=set(target_terms)
    for n in candidate_records:
        for t in m.walk_subterms(n.lhs):
            if m.term_size(t) <= 9: visible.add(t)
        for t in m.walk_subterms(n.rhs):
            if m.term_size(t) <= 9: visible.add(t)
    reflexive_ids={t:R(t) for t in sorted(visible,key=lambda q:(m.term_size(q),m.render_term(q)))}
    compact_reflexives=[rid for t,rid in sorted(reflexive_ids.items(),key=lambda kv:(m.term_size(kv[0]),m.render_term(kv[0]))) if m.term_size(t)<=9]

    def endpoint_target_exposure(lhs,rhs):
        return int(lhs in target_terms) + int(rhs in target_terms)

    def source_side_match(term):
        hits=0
        for pattern in source[:2]:
            subst={}
            if m.match_term(pattern,term,subst): hits += 1
        return hits

    def candidate_score(n, frontier_ids):
        orientations=((n.lhs,n.rhs,False),(n.rhs,n.lhs,True))
        best_score=None
        for lhs,rhs,rev in orientations:
            exact_chain=0; context_chain=0
            for i in frontier_ids[:FRONTIER_CAP]:
                f=nodes[i]
                exact_chain += int(f.rhs==lhs) + int(rhs==f.lhs)
                # Stronger than visual similarity: endpoint can serve as an exact
                # child/context term already exposed by the current state.
                fterms=set(m.walk_subterms(f.lhs))|set(m.walk_subterms(f.rhs))
                context_chain += int(lhs in fterms) + int(rhs in fterms)
            exposure=endpoint_target_exposure(lhs,rhs)
            unification=source_side_match(lhs)+source_side_match(rhs)
            target_subterm_overlap=sum(t in target_terms for t in m.walk_subterms(lhs))+sum(t in target_terms for t in m.walk_subterms(rhs))
            distance=min(
                m.structural_distance(lhs,tl)+m.structural_distance(rhs,tr),
                m.structural_distance(lhs,tr)+m.structural_distance(rhs,tl),
            )
            # Lexicographic: actionable now > exposes target structure > resemblance.
            score=(-exact_chain,-context_chain,-exposure,-target_subterm_overlap,-unification,
                   distance,m.term_size(lhs)+m.term_size(rhs),m.render_term(lhs),m.render_term(rhs),rev)
            if best_score is None or score < best_score: best_score=score
        return best_score

    selected_history=[]
    def select_basis(frontier_ids):
        ranked=sorted(candidate_records,key=lambda n:candidate_score(n,frontier_ids))[:BASIS_CAP]
        ids=[]; rows=[]
        for n in ranked:
            # Preserve both orientations persistently once selected.
            a=ensure_source(n,False); b=ensure_source(n,True)
            if a is not None: ids.append(a)
            if b is not None: ids.append(b)
            rows.append({'lhs':m.render_term(n.lhs),'rhs':m.render_term(n.rhs),'score':candidate_score(n,frontier_ids)[:-1]})
        return list(dict.fromkeys(ids)),rows

    # Initial basis is selected using target actionability only; after each productive
    # round it is re-selected against the new verified frontier.
    basis,rows=select_basis([]); selected_history.append({'round':0,'basis':rows})
    frontier=[]
    for i in basis:
        for j in compact_reflexives[:40]:
            k=C(i,j,1)
            if k is not None and depth[k]==1: frontier.append(k)
            k=C(j,i,1)
            if k is not None and depth[k]==1: frontier.append(k)
            if len(nodes)>=MAX_NODES: break
        if len(nodes)>=MAX_NODES: break
    frontier=list(dict.fromkeys(frontier)); found=best.get((tl,tr)); snapshots=[]

    def frontier_score(i):
        n=nodes[i]
        exact=int(n.lhs==tl)+int(n.rhs==tr)+int(n.lhs==tr)+int(n.rhs==tl)
        exposure=sum(t in target_terms for t in m.walk_subterms(n.lhs))+sum(t in target_terms for t in m.walk_subterms(n.rhs))
        distance=min(m.structural_distance(n.lhs,tl)+m.structural_distance(n.rhs,tr),m.structural_distance(n.lhs,tr)+m.structural_distance(n.rhs,tl))
        return (-exact,-exposure,distance,depth[i],m.term_size(n.lhs)+m.term_size(n.rhs),i)

    for r in range(2,ROUNDS+1):
        if found is not None or not frontier or len(nodes)>=MAX_NODES: break
        active=sorted(set(frontier),key=frontier_score)[:FRONTIER_CAP]
        basis,rows=select_basis(active); selected_history.append({'round':r,'basis':rows})
        new=[]

        # Exact chaining with currently actionable basis goes first.
        for i in active:
            for j in basis:
                k=T(i,j,r)
                if k is not None and depth[k]==r: new.append(k)
                k=T(j,i,r)
                if k is not None and depth[k]==r: new.append(k)

        # Then bounded contextual continuation; contexts are target/candidate-derived,
        # but only a small compact prefix is admitted.
        seeds=list(dict.fromkeys(new))+active
        for i in seeds[:FRONTIER_CAP]:
            for j in compact_reflexives[:24]:
                k=C(i,j,r)
                if k is not None and depth[k]==r: new.append(k)
                k=C(j,i,r)
                if k is not None and depth[k]==r: new.append(k)
                if len(nodes)>=MAX_NODES: break
            if len(nodes)>=MAX_NODES: break

        for i in list(dict.fromkeys(new))[:FRONTIER_CAP]:
            s=S(i,r)
            if s is not None and depth[s]==r: new.append(s)

        # Exact endpoint composition among the newly developed states only.
        unique=list(dict.fromkeys(new))[:FRONTIER_CAP]
        by_lhs={}; by_rhs={}
        for j in list(best.values()):
            by_lhs.setdefault(nodes[j].lhs,[]).append(j); by_rhs.setdefault(nodes[j].rhs,[]).append(j)
        for i in unique:
            for j in by_lhs.get(nodes[i].rhs,())[:8]:
                k=T(i,j,r)
                if k is not None and depth[k]==r: new.append(k)
            for j in by_rhs.get(nodes[i].lhs,())[:8]:
                k=T(j,i,r)
                if k is not None and depth[k]==r: new.append(k)
            if len(nodes)>=MAX_NODES: break

        frontier=list(dict.fromkeys(new)); found=best.get((tl,tr))
        snap={'round':r,'nodes':len(nodes),'frontier':len(frontier),'basis_oriented':len(basis),'found':found is not None}
        snapshots.append(snap); print(json.dumps(snap,sort_keys=True),flush=True)

    replayed=False; replay_error=None
    if found is not None:
        try:
            replayed=bool(m.replay_dag(source,nodes,found,maximum_term_size=MAX_TERM_SIZE,maximum_nodes=MAX_NODES))
        except Exception as e:
            replay_error=type(e).__name__+': '+str(e)

    out={
        'schema':'mathgraph.3366-dynamic-compatibility-basis.v1','edge':'3366->41','teacher_information_used':False,
        'mechanism':'dynamic compatibility basis + role-aware continuation','candidate_source_instances':len(candidate_records),
        'basis_cap':BASIS_CAP,'baseline':{'found':baseline_found,'replayed':baseline_replayed,'exhaustion':getattr(baseline,'exhaustion',None),'nodes':len(getattr(baseline,'nodes',()))},
        'transfer':{'found':found is not None,'replayed':replayed,'replay_error':replay_error,'nodes':len(nodes),'snapshots':snapshots},
        'selected_history':selected_history,'promotion_gate':{'passed':bool(replayed and not baseline_replayed)}
    }
    p=Path('experiments/mathgraph/results/3366-dynamic-compatibility-basis.json'); p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('SUMMARY',json.dumps({'baseline_replayed':baseline_replayed,'transfer_found':found is not None,'transfer_replayed':replayed,'nodes':len(nodes),'promotion_gate':out['promotion_gate']},sort_keys=True),flush=True)

if __name__=='__main__': main()

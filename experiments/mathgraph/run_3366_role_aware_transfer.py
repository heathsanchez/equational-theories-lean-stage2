import importlib.util
import json
import sys
import time
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('sep18_helper_3366_transfer', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)

MAX_NODES = 50000
MAX_TERM_SIZE = 180
FRONTIER_CAP = 400
ROUNDS = 8
BASIS_CAP = 24


def main():
    eqs = h.load_equations(); m = h.load_solver()
    source = m.parse_equation(eqs[3366]); target = m.parse_equation(eqs[41])
    tl, tr = target[:2]

    # Frozen comparator: same solver, 30-second strong baseline used by the gap audit.
    baseline_start = time.monotonic()
    baseline = m.EqualitySearch(source, target, time.monotonic() + 30.0)
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

    # Held-out basis construction: no teacher proof information. Build the ordinary
    # target/source term pool, instantiate sources once, then freeze a compact basis
    # ranked only by target distance and term size.
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
    pool = seed.make_pool()
    seed.initial_pool = tuple(pool)
    seed.instantiate_sources(pool)
    candidates = [n for n in seed.nodes if n.kind in ('source instance', 'source reentry')]

    def node_rank(n):
        direct = m.structural_distance(n.lhs, tl) + m.structural_distance(n.rhs, tr)
        reverse = m.structural_distance(n.rhs, tl) + m.structural_distance(n.lhs, tr)
        return (min(direct, reverse), m.term_size(n.lhs) + m.term_size(n.rhs),
                m.render_term(n.lhs), m.render_term(n.rhs))

    candidates.sort(key=node_rank)
    frozen = candidates[:BASIS_CAP]

    nodes=[]; depth=[]; best={}
    def add(node,d):
        if len(nodes) >= MAX_NODES: return None
        key=(node.lhs,node.rhs); old=best.get(key)
        if old is not None and depth[old] <= d: return old
        nodes.append(node); depth.append(d); idx=len(nodes)-1; best[key]=idx; return idx
    def M(a,b): return ('op',a,b)
    def R(t): return add(m.EqualityNode(t,t,'reflexivity',constructor='role-aware-transfer'),0)
    def S(i,d):
        p=nodes[i]
        return add(m.EqualityNode(p.rhs,p.lhs,'symmetry',parents=(i,),constructor='role-aware-transfer'),d)
    def T(i,j,d):
        a,b=nodes[i],nodes[j]
        if a.rhs != b.lhs: return None
        return add(m.EqualityNode(a.lhs,b.rhs,'transitivity',parents=(i,j),constructor='role-aware-transfer'),d)
    def C(i,j,d):
        a,b=nodes[i],nodes[j]
        lhs=M(a.lhs,b.lhs); rhs=M(a.rhs,b.rhs)
        if m.term_size(lhs)>MAX_TERM_SIZE or m.term_size(rhs)>MAX_TERM_SIZE: return None
        i1=add(m.EqualityNode(M(a.lhs,b.lhs),M(a.rhs,b.lhs),'congruence on left child',parents=(i,),context=('left',b.lhs),constructor='role-aware-transfer'),d)
        if i1 is None: return None
        i2=add(m.EqualityNode(M(a.rhs,b.lhs),M(a.rhs,b.rhs),'congruence on right child',parents=(j,),context=('right',a.rhs),constructor='role-aware-transfer'),d)
        if i2 is None: return None
        return T(i1,i2,d)

    basis=[]
    for n in frozen:
        copied = m.EqualityNode(n.lhs,n.rhs,'source instance',substitution=n.substitution,
                                orientation=getattr(n,'orientation',False),constructor='role-aware-transfer')
        i=add(copied,0)
        if i is not None:
            basis.append(i)
            s=S(i,0)
            if s is not None: basis.append(s)
    basis=list(dict.fromkeys(basis))

    visible=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))
    for i in basis:
        visible.update(m.walk_subterms(nodes[i].lhs)); visible.update(m.walk_subterms(nodes[i].rhs))
    reflexives={t:R(t) for t in sorted(visible,key=lambda q:(m.term_size(q),m.render_term(q)))}
    compact_reflexives=[rid for t,rid in sorted(reflexives.items(),key=lambda kv:(m.term_size(kv[0]),m.render_term(kv[0]))) if m.term_size(t)<=9]

    target_terms=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))
    def score(i):
        n=nodes[i]
        direct=m.structural_distance(n.lhs,tl)+m.structural_distance(n.rhs,tr)
        rev=m.structural_distance(n.rhs,tl)+m.structural_distance(n.lhs,tr)
        overlap=-sum(t in target_terms for t in m.walk_subterms(n.lhs))-sum(t in target_terms for t in m.walk_subterms(n.rhs))
        return (min(direct,rev),overlap,depth[i],m.term_size(n.lhs)+m.term_size(n.rhs),i)

    # Generic round-1 program states: compact congruence constructions from the
    # persistent basis and reflexive contexts. No target-specific intermediate is injected.
    frontier=[]
    for i in basis[:FRONTIER_CAP]:
        for j in compact_reflexives:
            k=C(i,j,1)
            if k is not None and depth[k]==1: frontier.append(k)
            k=C(j,i,1)
            if k is not None and depth[k]==1: frontier.append(k)
            if len(nodes)>=MAX_NODES: break
        if len(nodes)>=MAX_NODES: break
    frontier=list(dict.fromkeys(frontier))
    found=best.get((tl,tr)); snapshots=[]

    for r in range(2,ROUNDS+1):
        if found is not None or not frontier or len(nodes)>=MAX_NODES: break
        new=[]; active=sorted(set(frontier),key=score)[:FRONTIER_CAP]

        # Same role-aware continuation as the promoted 2666 arm.
        for i in active:
            for j in compact_reflexives:
                k=C(i,j,r)
                if k is not None and depth[k]==r: new.append(k)
                k=C(j,i,r)
                if k is not None and depth[k]==r: new.append(k)
                if len(nodes)>=MAX_NODES: break
            if len(nodes)>=MAX_NODES: break

        seed_new=list(dict.fromkeys(new))
        for i in seed_new[:FRONTIER_CAP]:
            for j in basis:
                k=T(i,j,r)
                if k is not None and depth[k]==r: new.append(k)
                k=T(j,i,r)
                if k is not None and depth[k]==r: new.append(k)
            if len(nodes)>=MAX_NODES: break

        for i in list(dict.fromkeys(new))[:FRONTIER_CAP]:
            s=S(i,r)
            if s is not None and depth[s]==r: new.append(s)

        pool_ids=list(best.values()); by_lhs={}; by_rhs={}
        for j in pool_ids:
            by_lhs.setdefault(nodes[j].lhs,[]).append(j); by_rhs.setdefault(nodes[j].rhs,[]).append(j)
        for i in list(dict.fromkeys(new))[:FRONTIER_CAP]:
            for j in by_lhs.get(nodes[i].rhs,())[:20]:
                k=T(i,j,r)
                if k is not None and depth[k]==r: new.append(k)
            for j in by_rhs.get(nodes[i].lhs,())[:20]:
                k=T(j,i,r)
                if k is not None and depth[k]==r: new.append(k)
            if len(nodes)>=MAX_NODES: break

        frontier=list(dict.fromkeys(new)); found=best.get((tl,tr))
        snapshots.append({'round':r,'nodes':len(nodes),'frontier':len(frontier),'found':found is not None})
        print(json.dumps(snapshots[-1],sort_keys=True),flush=True)

    replayed=False; replay_error=None
    if found is not None:
        try:
            replayed=bool(m.replay_dag(source,nodes,found,maximum_term_size=MAX_TERM_SIZE,maximum_nodes=MAX_NODES))
        except Exception as e:
            replay_error=type(e).__name__+': '+str(e)

    out={
        'schema':'mathgraph.3366-role-aware-transfer.v1',
        'edge':'3366->41',
        'teacher_information_used':False,
        'mechanism':'persistent-oriented-basis + role-aware continuation',
        'baseline':{'found':baseline_found,'replayed':baseline_replayed,'seconds':time.monotonic()-baseline_start,
                    'exhaustion':getattr(baseline,'exhaustion',None),'nodes':len(getattr(baseline,'nodes',()))},
        'basis':{'candidate_source_instances':len(candidates),'selected':len(frozen),'oriented':len(basis)},
        'transfer':{'found':found is not None,'replayed':replayed,'replay_error':replay_error,
                    'nodes':len(nodes),'rounds':snapshots,'max_nodes':MAX_NODES,'max_term_size':MAX_TERM_SIZE,
                    'frontier_cap':FRONTIER_CAP},
        'promotion_gate':{'passed':bool(replayed and not baseline_replayed)}
    }
    p=Path('experiments/mathgraph/results/3366-role-aware-transfer.json'); p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('SUMMARY',json.dumps({'baseline_replayed':baseline_replayed,'transfer_found':found is not None,
        'transfer_replayed':replayed,'nodes':len(nodes),'basis':len(basis),'promotion_gate':out['promotion_gate']},sort_keys=True),flush=True)

if __name__=='__main__': main()

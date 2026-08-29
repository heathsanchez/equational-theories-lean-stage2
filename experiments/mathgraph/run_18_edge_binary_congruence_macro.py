import importlib.util
import json
import sys
import time
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('sep18_helper_bincong', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)

GAPS = [(2666,2860),(2860,2062),(3366,41),(1367,678),(2920,1151)]

LIMITS = {
    'max_term_size': 31,
    'max_pool_terms': 64,
    'max_core_terms': 16,
    'max_source_attempts': 250000,
    'max_source_edges': 6000,
    'max_graph_edges': 30000,
    'max_derivation_nodes': 40000,
    'max_congruence_rounds': 2,
}


def proof_ids(nodes, root):
    seen=set(); stack=[root]
    while stack:
        i=stack.pop()
        if i in seen: continue
        seen.add(i); stack.extend(getattr(nodes[i],'parents',()))
    return seen


def binary_macro_round(m, search, candidate_ids, max_pairs=12000, max_added=5000):
    target_terms = set(m.walk_subterms(search.target[0])) | set(m.walk_subterms(search.target[1]))
    target_left, target_right = search.target[:2]

    def score_node(i):
        n=search.nodes[i]
        d=min(
            m.structural_distance(n.lhs,target_left), m.structural_distance(n.lhs,target_right),
            m.structural_distance(n.rhs,target_left), m.structural_distance(n.rhs,target_right)
        )
        hit=0 if (n.lhs in target_terms or n.rhs in target_terms) else 1
        return (hit,d,m.term_size(n.lhs)+m.term_size(n.rhs),i)

    ids=sorted(candidate_ids,key=score_node)[:180]
    pairs=[]
    for li in ids:
        l=search.nodes[li]
        for ri in ids:
            r=search.nodes[ri]
            lhs=('op',l.lhs,r.lhs); rhs=('op',l.rhs,r.rhs)
            if m.term_size(lhs)>search.max_term_size or m.term_size(rhs)>search.max_term_size:
                continue
            d=min(
                m.structural_distance(lhs,target_left),m.structural_distance(lhs,target_right),
                m.structural_distance(rhs,target_left),m.structural_distance(rhs,target_right)
            )
            hit=0 if (lhs in target_terms or rhs in target_terms) else 1
            pairs.append(((hit,d,m.term_size(lhs)+m.term_size(rhs),li,ri),li,ri))
            if len(pairs)>=max_pairs: break
        if len(pairs)>=max_pairs: break
    pairs.sort()
    added=0
    for _,li,ri in pairs:
        if search.expired() or added>=max_added: break
        l=search.nodes[li]; r=search.nodes[ri]
        # Compile C(l,r) using the existing replayable unary congruence nodes.
        n1=m.EqualityNode(
            ('op',l.lhs,r.lhs),('op',l.rhs,r.lhs),
            'congruence on left child',parents=(li,),context=('left',r.lhs),
            constructor='binary-congruence-macro')
        i1=search.add_node(n1)
        if i1 is None: continue
        n2=m.EqualityNode(
            ('op',l.rhs,r.lhs),('op',l.rhs,r.rhs),
            'congruence on right child',parents=(ri,),context=('right',l.rhs),
            constructor='binary-congruence-macro')
        i2=search.add_node(n2)
        if i2 is None: continue
        n3=m.EqualityNode(
            ('op',l.lhs,r.lhs),('op',l.rhs,r.rhs),
            'transitivity',parents=(i1,i2),constructor='binary-congruence-macro')
        i3=search.add_node(n3)
        if i3 is not None: added+=1
    return added


def run_edge(m, source, target):
    search=m.EqualitySearch(source,target,time.monotonic()+35.0,limits=dict(LIMITS))
    pool=search.make_pool(); search.initial_pool=tuple(pool)
    search.instantiate_sources(pool)
    root=search.shortest_path()
    if root is not None:
        return finish(m,source,search,root,'initial')

    # Existing unary congruence first, then explicit binary composition.
    frontier=list(range(len(search.nodes)))
    for depth in range(1,5):
        before=len(search.nodes)
        search.add_congruence_round(pool[:16],0 if depth==1 else max(0,before-6000))
        root=search.shortest_path()
        if root is not None:
            return finish(m,source,search,root,f'unary-{depth}')
        candidate_ids=list(range(max(0,len(search.nodes)-10000),len(search.nodes)))
        added=binary_macro_round(m,search,candidate_ids)
        root=search.shortest_path()
        if root is not None:
            result=finish(m,source,search,root,f'binary-{depth}')
            result['binary_added_last_round']=added
            return result
        if added==0 or search.expired(): break
    return {'found':False,'replayed':False,'nodes':len(search.nodes),'graph_edges':search.graph_edges,
            'exhaustion':search.exhaustion,'seconds_budget':35.0}


def finish(m,source,search,root,stage):
    try:
        replay=bool(m.replay_dag(source,search.nodes,root,maximum_term_size=search.max_term_size,maximum_nodes=search.max_derivation_nodes))
        err=None
    except Exception as e:
        replay=False; err=type(e).__name__+': '+str(e)
    ids=proof_ids(search.nodes,root)
    return {'found':True,'replayed':replay,'replay_error':err,'stage':stage,
            'proof_nodes':len(ids),'proof_kinds':sorted({search.nodes[i].kind for i in ids}),
            'proof_constructors':sorted({str(getattr(search.nodes[i],'constructor',None)) for i in ids}),
            'nodes':len(search.nodes),'graph_edges':search.graph_edges,'exhaustion':search.exhaustion}


def main():
    eqs=h.load_equations(); m=h.load_solver()
    out={'schema':'mathgraph.18-edge-binary-congruence-macro.v1','limits':LIMITS,'rows':[]}
    for s,t in GAPS:
        source=m.parse_equation(eqs[s]); target=m.parse_equation(eqs[t])
        try: res=run_edge(m,source,target)
        except Exception as e: res={'found':False,'replayed':False,'error':type(e).__name__+': '+str(e)}
        out['rows'].append({'source_id':s,'target_id':t,'result':res})
        print(json.dumps({'edge':f'{s}->{t}',**res},sort_keys=True),flush=True)
    out['replayed_count']=sum(bool(r['result'].get('replayed')) for r in out['rows'])
    out['gaps']=[[r['source_id'],r['target_id']] for r in out['rows'] if not r['result'].get('replayed')]
    p=Path('experiments/mathgraph/results/18-edge-binary-congruence-macro.json'); p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('SUMMARY',json.dumps({'replayed':out['replayed_count'],'gaps':out['gaps']},sort_keys=True))

if __name__=='__main__': main()

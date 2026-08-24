import importlib.util
import json
import sys
import time
from pathlib import Path

HELPER=Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec=importlib.util.spec_from_file_location('sep18_teacher',HELPER)
h=importlib.util.module_from_spec(spec); sys.modules[spec.name]=h; spec.loader.exec_module(h)


def main():
    equations=h.load_equations(); m=h.load_solver()
    source=m.parse_equation(equations[2666]); target=m.parse_equation(equations[2860])
    search=m.EqualitySearch(source,target,time.monotonic()+30.0,limits={
        'max_term_size':80,'max_pool_terms':8,'max_core_terms':3,'max_source_edges':100,
        'max_graph_edges':50000,'max_derivation_nodes':55000,'max_congruence_rounds':0,
    })
    # Exact source-law instantiations appearing in the upstream MagmaEgg proof
    # Equation2666_implies_Equation2860. No derived theorem is injected: only
    # the argument tuples supplied to h are teacher-forced.
    x=('var','x'); y=('var','y'); z=('var','z')
    M=lambda a,b:('op',a,b)
    v0=M(x,y); v1=M(x,v0); v2=M(v1,z); v3=M(v2,z); v6=M(v3,v0)
    instances=[
        (v3,v0,v0),
        (v2,z,z),
        (x,v0,y),
        (v1,z,z),
        (M(v3,v3),z,z),
        (M(v6,v6),v0,v0),
    ]
    added=[]
    for values in instances:
        node=search.add_source_substitution(values,generation=1,origins=(('teacher','Equation2666_implies_Equation2860'),))
        added.append(node)
    root=search.shortest_path()
    proof=None
    # Existing proof language only: repeated congruence + symmetry/transitivity path.
    siblings=[]
    for term in [x,y,z,v0,v1,v2,v3,v6,M(v3,v3),M(v6,v6)]:
        for sub in m.walk_subterms(term):
            if sub not in siblings: siblings.append(sub)
    first=0
    rounds=[]
    for r in range(8):
        if root is not None: break
        before=len(search.nodes)
        search.add_congruence_round(siblings,first)
        root=search.shortest_path()
        rounds.append({'round':r+1,'before':before,'after':len(search.nodes),'edges':search.graph_edges,'found':root is not None})
        first=before
        if len(search.nodes)==before: break
    if root is not None:
        try: replayed=m.replay_dag(source,search.nodes,root)
        except TypeError: replayed=m.replay_dag(source,search.nodes,root,maximum_term_size=80,maximum_nodes=55000)
        proof=h.proof_summary(search.nodes,root)
    else:
        replayed=False
    out={
        'schema':'mathgraph.teacher-forced-2666-2860.v1',
        'edge':[2666,2860],
        'teacher_source_instances':len(instances),
        'added_nodes':[n for n in added if n is not None],
        'rounds':rounds,
        'found':root is not None,
        'replayed':bool(replayed),
        'proof':proof,
        'graph_edges':search.graph_edges,
        'nodes':len(search.nodes),
        'exhaustion':search.exhaustion,
    }
    p=Path('experiments/mathgraph/results/2666-2860-teacher-forced.json'); p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('SUMMARY',json.dumps(out,sort_keys=True,default=str))

if __name__=='__main__': main()

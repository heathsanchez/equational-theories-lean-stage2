import importlib.util
import itertools
import json
import sys
import time
from pathlib import Path

HELPER=Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec=importlib.util.spec_from_file_location('sep18_bind_helper',HELPER)
h=importlib.util.module_from_spec(spec); sys.modules[spec.name]=h; spec.loader.exec_module(h)
GAPS=[(2666,2860),(2860,2062),(3366,41),(1367,678),(2920,1151)]


def run(m,source,target):
    search=m.EqualitySearch(source,target,time.monotonic()+20.0,limits={
        'max_term_size':35,'max_pool_terms':120,'max_core_terms':120,
        'max_source_attempts':200000,'max_source_edges':50000,
        'max_graph_edges':60000,'max_derivation_nodes':65000,
        'max_congruence_rounds':5,
    })
    target_terms=set()
    for side in target[:2]: target_terms.update(m.walk_subterms(side))
    # Include source subterms expressible in target variables, but do not invent
    # any new logical operation or teacher-specific term.
    allowed=set(target[2])
    for side in source[:2]:
        for term in m.walk_subterms(side):
            if m.term_variables(term)<=allowed: target_terms.add(term)
    pool=sorted(target_terms,key=search.term_key)
    search.initial_pool=tuple(pool)
    vars_=source[2]
    attempts=0
    for values in itertools.product(pool,repeat=len(vars_)):
        search.add_source_substitution(values)
        attempts+=1
        if attempts>=search.max_source_attempts or search.expired(): break
    root=search.shortest_path()
    first=0
    rounds=0
    while root is None and rounds<5 and not search.expired():
        before=len(search.nodes)
        search.add_congruence_round(pool,first)
        root=search.shortest_path(); first=before; rounds+=1
        if len(search.nodes)==before: break
    result={'attempts':attempts,'pool_size':len(pool),'graph_edges':search.graph_edges,
            'nodes':len(search.nodes),'rounds':rounds,'found':root is not None,'exhaustion':search.exhaustion}
    if root is not None:
        try: replayed=m.replay_dag(source,search.nodes,root)
        except TypeError: replayed=m.replay_dag(source,search.nodes,root,maximum_term_size=35,maximum_nodes=65000)
        result['replayed']=bool(replayed); result['proof']=h.proof_summary(search.nodes,root)
    else: result['replayed']=False
    return result


def main():
    equations=h.load_equations(); m=h.load_solver(); out={'schema':'mathgraph.18-edge-full-target-binding-separator.v1','rows':[]}
    for s,t in GAPS:
        source=m.parse_equation(equations[s]); target=m.parse_equation(equations[t])
        try: result=run(m,source,target)
        except Exception as e: result={'found':False,'replayed':False,'error':type(e).__name__+': '+str(e)}
        out['rows'].append({'source_id':s,'target_id':t,'result':result})
        print(json.dumps({'edge':f'{s}->{t}',**result},sort_keys=True,default=str),flush=True)
    out['replayed_count']=sum(bool(r['result'].get('replayed')) for r in out['rows'])
    out['gaps']=[[r['source_id'],r['target_id']] for r in out['rows'] if not r['result'].get('replayed')]
    p=Path('experiments/mathgraph/results/18-edge-full-target-binding-separator.json'); p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('SUMMARY',json.dumps({'replayed':out['replayed_count'],'gaps':out['gaps']},sort_keys=True))
if __name__=='__main__': main()

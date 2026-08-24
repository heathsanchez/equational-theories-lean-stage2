import importlib.util
import json
import sys
import time
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('sep18_helper_reentry', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)

GAPS = [(2666,2860),(2860,2062),(3366,41),(1367,678),(2920,1151)]

INITIAL_LIMITS = {
    'max_term_size': 15,
    'max_pool_terms': 56,
    'max_core_terms': 10,
    'max_source_edges': 3000,
    'max_graph_edges': 7000,
    'max_derivation_nodes': 8000,
    'max_congruence_rounds': 3,
}
REENTRY = {
    'generations': 3,
    'new_terms': 64,
    'instances': 5000,
    'reentry_term_size': 25,
    'reentry_nodes': 30000,
    'reentry_edges': 28000,
}


def run(m, source, target):
    search = m.EqualitySearch(source, target, time.monotonic()+20.0, limits=dict(INITIAL_LIMITS))
    initial = search.solve()
    if initial is not None:
        nodes, root = initial
        return {'stage':'initial','found':True,'replayed':bool(m.replay_dag(source,nodes,root)),
                'proof':h.proof_summary(nodes,root),'generations':search.generations_completed,
                'graph_edges':search.graph_edges,'nodes':len(search.nodes),'exhaustion':search.exhaustion}
    search.max_term_size = REENTRY['reentry_term_size']
    search.max_derivation_nodes = REENTRY['reentry_nodes']
    search.max_graph_edges = REENTRY['reentry_edges']
    search.exhaustion = None
    start=time.monotonic()
    found = search.solve_reentry(REENTRY['generations'],REENTRY['new_terms'],REENTRY['instances'],targeted=False)
    elapsed=time.monotonic()-start
    result={'stage':'reentry','found':bool(found),'seconds':elapsed,'generations':search.generations_completed,
            'source_instances_by_generation':search.source_instances_by_generation,
            'graph_edges':search.graph_edges,'nodes':len(search.nodes),'exhaustion':search.exhaustion,
            'reentry_terms_used':len(search.reentry_terms_used)}
    if isinstance(found,tuple) and len(found)==2:
        nodes,root=found
        try: replayed=m.replay_dag(source,nodes,root)
        except TypeError: replayed=m.replay_dag(source,nodes,root,maximum_term_size=REENTRY['reentry_term_size'],maximum_nodes=REENTRY['reentry_nodes'])
        result['replayed']=bool(replayed)
        result['proof']=h.proof_summary(nodes,root)
    else:
        result['replayed']=False
    return result


def main():
    equations=h.load_equations(); m=h.load_solver()
    out={'schema':'mathgraph.18-edge-reentry-separator.v1','gaps':GAPS,'initial_limits':INITIAL_LIMITS,'reentry':REENTRY,'rows':[]}
    for s,t in GAPS:
        source=m.parse_equation(equations[s]); target=m.parse_equation(equations[t])
        try: result=run(m,source,target)
        except Exception as e: result={'found':False,'replayed':False,'error':type(e).__name__+': '+str(e)}
        row={'source_id':s,'target_id':t,'source_equation':equations[s],'target_equation':equations[t],'result':result}
        out['rows'].append(row)
        print(json.dumps({'edge':f'{s}->{t}',**result},sort_keys=True,default=str),flush=True)
    out['replayed_count']=sum(bool(r['result'].get('replayed')) for r in out['rows'])
    out['gaps_after_reentry']=[[r['source_id'],r['target_id']] for r in out['rows'] if not r['result'].get('replayed')]
    p=Path('experiments/mathgraph/results/18-edge-reentry-separator.json'); p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('SUMMARY',json.dumps({'replayed':out['replayed_count'],'gaps':out['gaps_after_reentry']},sort_keys=True))

if __name__=='__main__': main()

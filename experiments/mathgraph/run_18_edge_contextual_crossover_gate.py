import json
from pathlib import Path

TRANSFER = Path('experiments/mathgraph/run_18_edge_contextual_contraction_transfer.py')
BASE_TEMPLATE = Path('experiments/mathgraph/run_3366_round8_interface_attribution.py')
SRC_TEMPLATE = Path('experiments/mathgraph/run_3366_iterated_contextual_contraction.py')
OUT = Path('experiments/mathgraph/results/18-edge-contextual-crossover-gate.json')

EDGES = [
    (2666, 2860), (2860, 2062), (3366, 41), (41, 3390),
    (1367, 678), (678, 1696), (1696, 979), (979, 2945),
    (2938, 2922), (2920, 1151), (1151, 689), (688, 2), (41, 3602),
]

INJECT = r'''
    # Production-crossover gate: after exactly two replayable contextual
    # contraction generations, feed the retained states back through two
    # bounded rounds of the existing transitivity/congruence/symmetry machinery.
    crossover_front = list(current)
    crossover_rows = []
    crossover_target = None
    for cr in range(1, 3):
        d = 10 + cr
        active2 = sorted(set(crossover_front), key=fscore)[:FRONTIER_CAP]
        b2 = basis(active2)
        new2 = []
        for i in active2:
            for j in b2:
                for k in (T(i,j,d), T(j,i,d)):
                    if k is not None and depth[k] == d:
                        new2.append(k)
        seeds2 = list(dict.fromkeys(new2)) + active2
        for i in seeds2[:FRONTIER_CAP]:
            for j in compact[:24]:
                for k in (C(i,j,d), C(j,i,d)):
                    if k is not None and depth[k] == d:
                        new2.append(k)
        for i in list(dict.fromkeys(new2))[:FRONTIER_CAP]:
            k = S(i,d)
            if k is not None and depth[k] == d:
                new2.append(k)
        unique2 = list(dict.fromkeys(new2))
        for i in unique2:
            n = nodes[i]
            if (n.lhs,n.rhs) in ((tl,tr),(tr,tl)):
                rr = i if (n.lhs,n.rhs)==(tl,tr) else S(i,d)
                if rr is not None and m.replay_dag(source,nodes,rr,maximum_term_size=MAX_TERM_SIZE,maximum_nodes=MAX_NODES):
                    crossover_target = rr
                    break
        bestd = min((pair_distance(nodes[i].lhs,nodes[i].rhs) for i in unique2), default=None)
        crossover_rows.append({'round':cr,'generated':len(unique2),'best_distance':bestd,'target_replayed':crossover_target is not None})
        if crossover_target is not None:
            break
        crossover_front = sorted(unique2, key=fscore)[:FRONTIER_CAP]
        if not crossover_front:
            break
    attribution['production_crossover'] = {
        'rows': crossover_rows,
        'target_replayed': crossover_target is not None,
        'target_root': crossover_target,
    }
'''


def patch_base(source_id, target_id, base_result):
    s = BASE_TEMPLATE.read_text()
    s = s.replace('eqs[3366]', f'eqs[{source_id}]', 1)
    s = s.replace('eqs[41]', f'eqs[{target_id}]', 1)
    s = s.replace("'edge':'3366->41'", f"'edge':'{source_id}->{target_id}'", 1)
    s = s.replace("Path('experiments/mathgraph/results/3366-round8-interface-attribution.json')", f"Path({str(base_result)!r})", 1)
    return s


def patch_src(base_file, base_result, out_file):
    s = SRC_TEMPLATE.read_text()
    s = s.replace("BASE = Path('experiments/mathgraph/run_3366_round8_interface_attribution.py')", f"BASE = Path({str(base_file)!r})", 1)
    s = s.replace("BASE_RESULT = Path('experiments/mathgraph/results/3366-round8-interface-attribution.json')", f"BASE_RESULT = Path({str(base_result)!r})", 1)
    s = s.replace("OUT = Path('experiments/mathgraph/results/3366-iterated-contextual-contraction.json')", f"OUT = Path({str(out_file)!r})", 1)
    s = s.replace('CONTEXT_GENERATIONS = 3', 'CONTEXT_GENERATIONS = 2', 1)
    marker = "    attribution['iterated_contextual_contraction'] = {"
    if marker not in s:
        raise RuntimeError('crossover injection marker missing')
    s = s.replace(marker, INJECT + '\n' + marker, 1)
    return s


def run_edge(source_id, target_id):
    tmp = Path('experiments/mathgraph/.crossover_tmp'); tmp.mkdir(parents=True, exist_ok=True)
    tag=f'{source_id}_{target_id}'; base_file=tmp/f'base_{tag}.py'; base_result=tmp/f'base_{tag}.json'; out_file=tmp/f'out_{tag}.json'
    base_file.write_text(patch_base(source_id,target_id,base_result))
    src=patch_src(base_file,base_result,out_file)
    ns={'__name__':f'crossover_{tag}'}
    exec(compile(src,f'<crossover-{tag}>','exec'),ns,ns); ns['main']()
    result=json.loads(out_file.read_text())
    c=result['attribution']['iterated_contextual_contraction']; x=result['attribution']['production_crossover']
    return {'edge':f'{source_id}->{target_id}','context_final_distance':c.get('final_best_distance'),'crossover_rows':x['rows'],'target_replayed':x['target_replayed']}


def main():
    rows=[]
    for a,b in EDGES:
        try: row=run_edge(a,b)
        except Exception as exc: row={'edge':f'{a}->{b}','target_replayed':False,'error':type(exc).__name__+': '+str(exc)}
        rows.append(row); print('CROSSOVER_EDGE',json.dumps(row,sort_keys=True),flush=True)
    out={'schema':'mathgraph.18-edge-contextual-crossover-gate.v1','teacher_information_used':False,'rows':rows,'solved_edges':[r['edge'] for r in rows if r.get('target_replayed')],'errors':[r['edge'] for r in rows if r.get('error')]}
    out['promotion_gate']=bool(out['solved_edges']) and not out['errors']
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('CROSSOVER_SUMMARY',json.dumps({'solved_edges':out['solved_edges'],'errors':out['errors'],'promotion_gate':out['promotion_gate']},sort_keys=True),flush=True)

if __name__=='__main__': main()

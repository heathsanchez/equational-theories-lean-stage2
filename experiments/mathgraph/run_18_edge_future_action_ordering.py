import json
from pathlib import Path

BASE_TEMPLATE = Path('experiments/mathgraph/run_3366_round8_interface_attribution.py')
SRC_TEMPLATE = Path('experiments/mathgraph/run_3366_iterated_contextual_contraction.py')
OUT = Path('experiments/mathgraph/results/18-edge-future-action-ordering.json')

EDGES = [
    (2666, 2860), (2860, 2062), (3366, 41), (41, 3390),
    (1367, 678), (678, 1696), (1696, 979), (979, 2945),
    (2938, 2922), (2920, 1151), (1151, 689), (688, 2), (41, 3602),
]

# This test asks a future-relative question.  Starting from the exact same
# two-generation replayed contextual frontier, compare lawful next-action
# families by the best state they make reachable immediately and after ONE
# additional contextual rollout.  The target labels are used only by the
# experiment's frozen evaluator (structural distance / replay), not to tune
# per-edge action definitions.
INJECT = r'''
    action_base = sorted(set(current), key=lambda i: (
        pair_distance(nodes[i].lhs, nodes[i].rhs),
        m.term_size(nodes[i].lhs) + m.term_size(nodes[i].rhs), i
    ))[:CONTEXT_KEEP]
    action_baseline = min(pair_distance(nodes[i].lhs, nodes[i].rhs) for i in action_base)
    frozen_pool = list(dict.fromkeys(list(best.values())))

    def replayable(ids):
        out = []
        for i in ids:
            if i is None or i in out:
                continue
            if m.replay_dag(source, nodes, i, maximum_term_size=MAX_TERM_SIZE, maximum_nodes=MAX_NODES):
                out.append(i)
        return out

    def rank_ids(ids, keep=16):
        ids = replayable(ids)
        return sorted(set(ids), key=lambda i: (
            pair_distance(nodes[i].lhs, nodes[i].rhs),
            m.term_size(nodes[i].lhs) + m.term_size(nodes[i].rhs), i
        ))[:keep]

    def contextual_step(front, d, require_strict=False, reference=None, keep=16):
        ref = action_baseline if reference is None else reference
        recs = {}
        exact = 0
        for outer_id in front:
            outer = nodes[outer_id]
            for outer_side, outer_term in enumerate((outer.lhs, outer.rhs)):
                other = outer.rhs if outer_side == 0 else outer.lhs
                for path in m.nonvariable_positions(outer_term, CONTEXT_DEPTH, include_root=False):
                    before = m.get_subterm(outer_term, path)
                    for inner_id in frozen_pool:
                        inner = nodes[inner_id]
                        for inner_side, expected, after in ((0,inner.lhs,inner.rhs),(1,inner.rhs,inner.lhs)):
                            if before != expected:
                                continue
                            changed = m.replace_subterm(outer_term, path, after)
                            if changed == outer_term or m.term_size(changed) > MAX_TERM_SIZE:
                                continue
                            exact += 1
                            lhs, rhs = other, changed
                            dist = pair_distance(lhs, rhs)
                            if require_strict and dist >= ref:
                                continue
                            key=(lhs,rhs)
                            rec={'outer_id':outer_id,'inner_id':inner_id,'outer_side':outer_side,'inner_side':inner_side,'path_tuple':tuple(path),'distance':dist,'size':m.term_size(lhs)+m.term_size(rhs),'lhs':lhs,'rhs':rhs}
                            rank=(dist,rec['size'],outer_id,inner_id,inner_side,tuple(path))
                            if key not in recs or rank < recs[key][0]: recs[key]=(rank,rec)
        made=[]
        for _,rec in sorted(recs.values(), key=lambda x:x[0]):
            root=materialize(rec,d)
            if root is not None: made.append(root)
            if len(made)>=keep*4: break
        return rank_ids(made,keep), exact

    def action_frontiers():
        acts = {}
        # A: keep doing the newly-discovered contextual operator.
        ids, exact = contextual_step(action_base, 20, require_strict=False, keep=16)
        acts['contextual_overlap']=(ids, {'exact_candidates':exact})

        # B: production-like transitivity against the dynamic compatibility basis.
        ids=[]; b3=basis(action_base)
        for i in action_base:
            for j in b3:
                ids.extend([T(i,j,21),T(j,i,21)])
        acts['basis_transitivity']=(rank_ids(ids), {'basis':len(b3)})

        # C: full-pool exact transitivity, bounded only by exact endpoint match.
        ids=[]
        for i in action_base:
            a=nodes[i]
            for j in frozen_pool:
                b=nodes[j]
                if a.rhs==b.lhs: ids.append(T(i,j,22))
                if b.rhs==a.lhs: ids.append(T(j,i,22))
        acts['full_pool_transitivity']=(rank_ids(ids), {'pool':len(frozen_pool)})

        # D: binary congruence with the same compact reflexive/context terms.
        ids=[]
        for i in action_base:
            for j in compact[:24]:
                ids.extend([C(i,j,23),C(j,i,23)])
        acts['binary_congruence']=(rank_ids(ids), {'compact':min(24,len(compact))})
        return acts

    future_rows=[]
    for name,(front,meta) in action_frontiers().items():
        immediate = min((pair_distance(nodes[i].lhs,nodes[i].rhs) for i in front), default=None)
        # One common continuation after each rival action: contextual rollout.
        rollout, exact2 = contextual_step(front, 24, require_strict=False, keep=16) if front else ([],0)
        future = min((pair_distance(nodes[i].lhs,nodes[i].rhs) for i in rollout), default=None)
        target_now = any((nodes[i].lhs,nodes[i].rhs) in ((tl,tr),(tr,tl)) for i in front)
        target_future = any((nodes[i].lhs,nodes[i].rhs) in ((tl,tr),(tr,tl)) for i in rollout)
        future_rows.append({
            'action':name,'generated_replayable':len(front),'immediate_best_distance':immediate,
            'future_contextual_best_distance':future,'future_exact_candidates':exact2,
            'target_now':target_now,'target_future':target_future, **meta
        })
    def consequence_key(r):
        f = r['future_contextual_best_distance'] if r['future_contextual_best_distance'] is not None else 10**9
        i = r['immediate_best_distance'] if r['immediate_best_distance'] is not None else 10**9
        return (0 if r['target_future'] else 1, f, 0 if r['target_now'] else 1, i, r['action'])
    ordered=sorted(future_rows,key=consequence_key)
    attribution['future_action_ordering']={
        'baseline_distance':action_baseline,
        'rows':future_rows,
        'ordering':[r['action'] for r in ordered],
        'winner':ordered[0]['action'] if ordered else None,
        'winner_future_distance':ordered[0]['future_contextual_best_distance'] if ordered else None,
    }
'''


def patch_base(source_id,target_id,base_result):
    s=BASE_TEMPLATE.read_text()
    s=s.replace('eqs[3366]',f'eqs[{source_id}]',1).replace('eqs[41]',f'eqs[{target_id}]',1)
    s=s.replace("'edge':'3366->41'",f"'edge':'{source_id}->{target_id}'",1)
    s=s.replace("Path('experiments/mathgraph/results/3366-round8-interface-attribution.json')",f"Path({str(base_result)!r})",1)
    return s

def patch_src(base_file,base_result,out_file):
    s=SRC_TEMPLATE.read_text()
    s=s.replace("BASE = Path('experiments/mathgraph/run_3366_round8_interface_attribution.py')",f"BASE = Path({str(base_file)!r})",1)
    s=s.replace("BASE_RESULT = Path('experiments/mathgraph/results/3366-round8-interface-attribution.json')",f"BASE_RESULT = Path({str(base_result)!r})",1)
    s=s.replace("OUT = Path('experiments/mathgraph/results/3366-iterated-contextual-contraction.json')",f"OUT = Path({str(out_file)!r})",1)
    s=s.replace('CONTEXT_GENERATIONS = 3','CONTEXT_GENERATIONS = 2',1)
    marker="    attribution['iterated_contextual_contraction'] = {"
    if marker not in s: raise RuntimeError('future-order injection marker missing')
    return s.replace(marker,INJECT+'\n'+marker,1)

def run_edge(a,b):
    tmp=Path('experiments/mathgraph/.future_order_tmp');tmp.mkdir(parents=True,exist_ok=True)
    tag=f'{a}_{b}';bf=tmp/f'base_{tag}.py';br=tmp/f'base_{tag}.json';of=tmp/f'out_{tag}.json'
    bf.write_text(patch_base(a,b,br))
    ns={'__name__':f'future_order_{tag}'}
    src=patch_src(bf,br,of);exec(compile(src,f'<future-order-{tag}>','exec'),ns,ns);ns['main']()
    r=json.loads(of.read_text());q=r['attribution']['future_action_ordering']
    return {'edge':f'{a}->{b}',**q}

def main():
    rows=[]
    for a,b in EDGES:
        try: row=run_edge(a,b)
        except Exception as exc: row={'edge':f'{a}->{b}','error':type(exc).__name__+': '+str(exc)}
        rows.append(row);print('FUTURE_ORDER_EDGE',json.dumps(row,sort_keys=True),flush=True)
    valid=[r for r in rows if not r.get('error')]
    winners={}
    orderings={}
    for r in valid:
        winners[r['winner']]=winners.get(r['winner'],0)+1
        key=' > '.join(r['ordering']);orderings[key]=orderings.get(key,0)+1
    out={'schema':'mathgraph.18-edge-future-action-ordering.v1','teacher_information_used':False,'rows':rows,'winner_counts':winners,'ordering_counts':orderings,'errors':[r['edge'] for r in rows if r.get('error')]}
    out['shared_winner_gate']=bool(valid) and max(winners.values(),default=0)>=9 and not out['errors']
    OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('FUTURE_ORDER_SUMMARY',json.dumps({'winner_counts':winners,'ordering_counts':orderings,'errors':out['errors'],'shared_winner_gate':out['shared_winner_gate']},sort_keys=True),flush=True)

if __name__=='__main__': main()

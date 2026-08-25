import json
from pathlib import Path

BASE_SCRIPT = Path('experiments/mathgraph/run_18_edge_future_action_ordering.py')
OUT = Path('experiments/mathgraph/results/18-edge-future-controller-gate.json')

# Decisive gate: reuse the frozen future-action experiment exactly, then turn
# its comparative evaluator into a controller.  After the two replay-checked
# contextual contractions, choose the action with the best one-step future
# consequence, execute ONLY that action, recompute the ordering, and repeat
# for at most three decisions.  No per-edge tuning, teacher proof, or relaxed
# replay rule is introduced.
CONTROLLER = r'''
    decision_front = list(action_base)
    decision_rows = []
    controller_target = None
    controller_replay_failures = 0

    for decision in range(1, 4):
        action_base = rank_ids(decision_front, CONTEXT_KEEP)
        if not action_base:
            break
        action_baseline = min(pair_distance(nodes[i].lhs, nodes[i].rhs) for i in action_base)
        acts = action_frontiers()
        evaluated = []
        for name, (front, meta) in acts.items():
            immediate = min((pair_distance(nodes[i].lhs,nodes[i].rhs) for i in front), default=None)
            rollout, exact2 = contextual_step(front, 30 + decision, require_strict=False, keep=16) if front else ([],0)
            future = min((pair_distance(nodes[i].lhs,nodes[i].rhs) for i in rollout), default=None)
            target_now_ids = [i for i in front if (nodes[i].lhs,nodes[i].rhs) in ((tl,tr),(tr,tl))]
            target_future_ids = [i for i in rollout if (nodes[i].lhs,nodes[i].rhs) in ((tl,tr),(tr,tl))]
            evaluated.append({
                'action': name,
                'front': front,
                'rollout': rollout,
                'immediate_best_distance': immediate,
                'future_best_distance': future,
                'target_now_ids': target_now_ids,
                'target_future_ids': target_future_ids,
                'future_exact_candidates': exact2,
                **meta,
            })

        def controller_key(r):
            f = r['future_best_distance'] if r['future_best_distance'] is not None else 10**9
            i = r['immediate_best_distance'] if r['immediate_best_distance'] is not None else 10**9
            return (0 if r['target_future_ids'] else 1, f, 0 if r['target_now_ids'] else 1, i, r['action'])

        ordered = sorted(evaluated, key=controller_key)
        if not ordered:
            break
        winner = ordered[0]
        executed = rank_ids(winner['front'], CONTEXT_KEEP)
        # The chosen action itself must remain replayable; rank_ids enforces it.
        if winner['front'] and not executed:
            controller_replay_failures += 1
            break

        # Only an actually executed target counts as a solve.  A target seen in
        # the scoring rollout is evidence for ranking but is not credited unless
        # the controller reaches it on execution in a later decision.
        target_ids = [i for i in executed if (nodes[i].lhs,nodes[i].rhs) in ((tl,tr),(tr,tl))]
        if target_ids:
            root = target_ids[0]
            if (nodes[root].lhs,nodes[root].rhs) == (tr,tl):
                root = S(root, 40 + decision)
            if root is not None and m.replay_dag(source,nodes,root,maximum_term_size=MAX_TERM_SIZE,maximum_nodes=MAX_NODES):
                controller_target = root

        row = {
            'decision': decision,
            'baseline_distance': action_baseline,
            'ordering': [r['action'] for r in ordered],
            'winner': winner['action'],
            'winner_immediate_distance': winner['immediate_best_distance'],
            'winner_future_distance': winner['future_best_distance'],
            'executed_states': len(executed),
            'executed_best_distance': min((pair_distance(nodes[i].lhs,nodes[i].rhs) for i in executed), default=None),
            'target_in_scoring_rollout': bool(winner['target_future_ids']),
            'target_replayed_on_execution': controller_target is not None,
        }
        decision_rows.append(row)
        print('FUTURE_CONTROLLER_DECISION', json.dumps(row, sort_keys=True), flush=True)
        if controller_target is not None:
            break
        decision_front = executed

    attribution['future_controller'] = {
        'decisions': decision_rows,
        'target_replayed': controller_target is not None,
        'target_root': controller_target,
        'replay_failures': controller_replay_failures,
        'promotion_gate': controller_target is not None and controller_replay_failures == 0,
    }
'''


def main():
    ns = {'__name__': 'future_controller_source'}
    source = BASE_SCRIPT.read_text()
    exec(compile(source, str(BASE_SCRIPT), 'exec'), ns, ns)

    # Reuse the exact edge set, patching helpers, and frozen future-order INJECT.
    base_template = ns['BASE_TEMPLATE']
    src_template = ns['SRC_TEMPLATE']
    edges = ns['EDGES']
    frozen_inject = ns['INJECT']

    def patch_base(a,b,result_path):
        s=base_template.read_text()
        s=s.replace('eqs[3366]',f'eqs[{a}]',1).replace('eqs[41]',f'eqs[{b}]',1)
        s=s.replace("'edge':'3366->41'",f"'edge':'{a}->{b}'",1)
        s=s.replace("Path('experiments/mathgraph/results/3366-round8-interface-attribution.json')",f"Path({str(result_path)!r})",1)
        return s

    def patch_src(base_file,base_result,out_file):
        s=src_template.read_text()
        s=s.replace("BASE = Path('experiments/mathgraph/run_3366_round8_interface_attribution.py')",f"BASE = Path({str(base_file)!r})",1)
        s=s.replace("BASE_RESULT = Path('experiments/mathgraph/results/3366-round8-interface-attribution.json')",f"BASE_RESULT = Path({str(base_result)!r})",1)
        s=s.replace("OUT = Path('experiments/mathgraph/results/3366-iterated-contextual-contraction.json')",f"OUT = Path({str(out_file)!r})",1)
        s=s.replace('CONTEXT_GENERATIONS = 3','CONTEXT_GENERATIONS = 2',1)
        marker="    attribution['iterated_contextual_contraction'] = {"
        if marker not in s:
            raise RuntimeError('controller injection marker missing')
        return s.replace(marker, frozen_inject + '\n' + CONTROLLER + '\n' + marker, 1)

    rows=[]
    tmp=Path('experiments/mathgraph/.future_controller_tmp'); tmp.mkdir(parents=True,exist_ok=True)
    for a,b in edges:
        tag=f'{a}_{b}'; bf=tmp/f'base_{tag}.py'; br=tmp/f'base_{tag}.json'; of=tmp/f'out_{tag}.json'
        try:
            bf.write_text(patch_base(a,b,br))
            src=patch_src(bf,br,of)
            env={'__name__':f'future_controller_{tag}'}
            exec(compile(src,f'<future-controller-{tag}>','exec'),env,env); env['main']()
            result=json.loads(of.read_text())
            c=result['attribution']['future_controller']
            row={'edge':f'{a}->{b}',**c}
        except Exception as exc:
            row={'edge':f'{a}->{b}','target_replayed':False,'replay_failures':None,'error':type(exc).__name__+': '+str(exc)}
        rows.append(row)
        print('FUTURE_CONTROLLER_EDGE',json.dumps(row,sort_keys=True),flush=True)

    out={
        'schema':'mathgraph.18-edge-future-controller-gate.v1',
        'teacher_information_used':False,
        'decision_horizon':3,
        'rows':rows,
        'solved_edges':[r['edge'] for r in rows if r.get('target_replayed')],
        'errors':[r['edge'] for r in rows if r.get('error')],
        'replay_failures_total':sum((r.get('replay_failures') or 0) for r in rows),
    }
    out['promotion_gate']=bool(out['solved_edges']) and not out['errors'] and out['replay_failures_total']==0
    OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('FUTURE_CONTROLLER_SUMMARY',json.dumps({
        'solved_edges':out['solved_edges'],
        'errors':out['errors'],
        'replay_failures_total':out['replay_failures_total'],
        'promotion_gate':out['promotion_gate'],
    },sort_keys=True),flush=True)

if __name__=='__main__': main()

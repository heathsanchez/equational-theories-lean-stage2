import json
from pathlib import Path

BASE = Path('experiments/mathgraph/run_3366_round8_interface_attribution.py')
BASE_RESULT = Path('experiments/mathgraph/results/3366-round8-interface-attribution.json')
OUT = Path('experiments/mathgraph/results/3366-iterated-contextual-contraction.json')

INJECT = r'''
    # Frozen residual intervention: start from the cap-16 round-8 frontier and
    # iterate only the exact contextual-overlap constructor that passed the
    # one-step attribution gate. Keep at most 8 replayable strict contractions
    # per generation for 3 generations. No teacher information is used.
    CONTEXT_GENERATIONS = 3
    CONTEXT_KEEP = 8
    CONTEXT_DEPTH = 10

    def pair_distance(lhs, rhs):
        return min(
            m.structural_distance(lhs, tl) + m.structural_distance(rhs, tr),
            m.structural_distance(lhs, tr) + m.structural_distance(rhs, tl),
        )

    def wrap_exact(inner_id, outer_term, path, d):
        cur = inner_id
        for k in range(len(path) - 1, -1, -1):
            prefix = path[:k]
            parent_term = m.get_subterm(outer_term, prefix)
            direction = path[k]
            p = nodes[cur]
            if direction == 'L':
                sibling = parent_term[2]
                node = m.EqualityNode(
                    ('op', p.lhs, sibling), ('op', p.rhs, sibling),
                    'congruence on left child', parents=(cur,),
                    context=('left', sibling),
                    constructor='iterated-contextual-contraction',
                    derivation_depth=d,
                )
            else:
                sibling = parent_term[1]
                node = m.EqualityNode(
                    ('op', sibling, p.lhs), ('op', sibling, p.rhs),
                    'congruence on right child', parents=(cur,),
                    context=('right', sibling),
                    constructor='iterated-contextual-contraction',
                    derivation_depth=d,
                )
            cur = add(node, d)
            if cur is None:
                return None
        return cur

    def materialize(candidate, d):
        outer_id = candidate['outer_id']
        inner_id = candidate['inner_id']
        outer_side = candidate['outer_side']
        inner_side = candidate['inner_side']
        path = candidate['path_tuple']
        outer = nodes[outer_id]
        inner = nodes[inner_id]
        outer_term = outer.lhs if outer_side == 0 else outer.rhs
        inner_oriented = inner_id if inner_side == 0 else S(inner_id, d)
        if inner_oriented is None:
            return None
        wrapped = wrap_exact(inner_oriented, outer_term, path, d)
        if wrapped is None:
            return None
        outer_oriented = S(outer_id, d) if outer_side == 0 else outer_id
        if outer_oriented is None:
            return None
        left, right = nodes[outer_oriented], nodes[wrapped]
        if left.rhs != right.lhs:
            return None
        root = add(m.EqualityNode(
            left.lhs, right.rhs, 'transitivity',
            parents=(outer_oriented, wrapped),
            constructor='iterated-contextual-contraction',
            derivation_depth=d,
        ), d)
        if root is None:
            root = best.get((left.lhs, right.rhs))
        return root

    current = sorted(set(active), key=fscore)[:FRONTIER_CAP]
    baseline_distance = min(pair_distance(nodes[i].lhs, nodes[i].rhs) for i in current)
    previous_best = baseline_distance
    generation_rows = []
    direct_target = None
    monotonic = True

    for generation in range(1, CONTEXT_GENERATIONS + 1):
        inner_pool = list(dict.fromkeys(list(best.values())))
        candidates = {}
        exact_count = 0
        strict_count = 0
        for outer_id in current:
            outer = nodes[outer_id]
            for outer_side, outer_term in enumerate((outer.lhs, outer.rhs)):
                other = outer.rhs if outer_side == 0 else outer.lhs
                for path in m.nonvariable_positions(
                    outer_term, CONTEXT_DEPTH, include_root=False
                ):
                    before = m.get_subterm(outer_term, path)
                    for inner_id in inner_pool:
                        inner = nodes[inner_id]
                        for inner_side, expected, after in (
                            (0, inner.lhs, inner.rhs),
                            (1, inner.rhs, inner.lhs),
                        ):
                            if before != expected:
                                continue
                            changed = m.replace_subterm(outer_term, path, after)
                            if changed == outer_term or m.term_size(changed) > MAX_TERM_SIZE:
                                continue
                            exact_count += 1
                            lhs, rhs = other, changed
                            dist = pair_distance(lhs, rhs)
                            if dist >= previous_best:
                                continue
                            strict_count += 1
                            key = (lhs, rhs)
                            rec = {
                                'outer_id': outer_id,
                                'inner_id': inner_id,
                                'outer_side': outer_side,
                                'inner_side': inner_side,
                                'path_tuple': tuple(path),
                                'distance': dist,
                                'size': m.term_size(lhs) + m.term_size(rhs),
                                'lhs': lhs,
                                'rhs': rhs,
                            }
                            old = candidates.get(key)
                            rank = (dist, rec['size'], outer_id, inner_id, inner_side, tuple(path))
                            if old is None or rank < old[0]:
                                candidates[key] = (rank, rec)

        ranked = [item[1] for item in sorted(candidates.values(), key=lambda x: x[0])]
        retained = []
        replay_failures = 0
        for rec in ranked:
            root = materialize(rec, 8 + generation)
            if root is None:
                continue
            replayed = bool(m.replay_dag(
                source, nodes, root,
                maximum_term_size=MAX_TERM_SIZE,
                maximum_nodes=MAX_NODES,
            ))
            if not replayed:
                replay_failures += 1
                continue
            retained.append(root)
            if (nodes[root].lhs, nodes[root].rhs) in ((tl, tr), (tr, tl)):
                target_root = root
                if (nodes[root].lhs, nodes[root].rhs) == (tr, tl):
                    target_root = S(root, 8 + generation)
                target_replayed = bool(target_root is not None and m.replay_dag(
                    source, nodes, target_root,
                    maximum_term_size=MAX_TERM_SIZE,
                    maximum_nodes=MAX_NODES,
                ))
                direct_target = {
                    'generation': generation,
                    'root': target_root,
                    'replayed': target_replayed,
                }
                if target_replayed:
                    retained = [target_root]
                    break
            if len(retained) >= CONTEXT_KEEP:
                break

        best_distance = (
            min(pair_distance(nodes[i].lhs, nodes[i].rhs) for i in retained)
            if retained else None
        )
        improved = best_distance is not None and best_distance < previous_best
        monotonic = monotonic and improved
        generation_rows.append({
            'generation': generation,
            'input_frontier': len(current),
            'inner_pool': len(inner_pool),
            'exact_overlap_candidates': exact_count,
            'strict_candidates': strict_count,
            'materialized_replayable': len(retained),
            'replay_failures': replay_failures,
            'previous_best_distance': previous_best,
            'best_distance': best_distance,
            'improved': improved,
            'nodes': len(nodes),
        })
        print('CONTEXT_GENERATION', json.dumps(generation_rows[-1], sort_keys=True), flush=True)

        if direct_target is not None and direct_target.get('replayed'):
            break
        if not retained or not improved:
            break
        current = sorted(set(retained), key=lambda i: (
            pair_distance(nodes[i].lhs, nodes[i].rhs),
            m.term_size(nodes[i].lhs) + m.term_size(nodes[i].rhs),
            i,
        ))[:CONTEXT_KEEP]
        previous_best = best_distance

    attribution['iterated_contextual_contraction'] = {
        'baseline_distance': baseline_distance,
        'generations_requested': CONTEXT_GENERATIONS,
        'keep': CONTEXT_KEEP,
        'rows': generation_rows,
        'direct_target': direct_target,
        'monotonic_all_completed': monotonic and bool(generation_rows),
        'final_best_distance': generation_rows[-1]['best_distance'] if generation_rows else None,
        'promotion_gate': bool(
            (direct_target is not None and direct_target.get('replayed'))
            or (
                len(generation_rows) >= 2
                and all(row['improved'] for row in generation_rows)
            )
        ),
    }
'''


def main():
    source = BASE.read_text()
    marker = "    out={'schema':'mathgraph.3366-round8-interface-attribution.v1'"
    if marker not in source:
        raise RuntimeError('instrumentation marker not found')
    source = source.replace(marker, INJECT + "\n" + marker, 1)
    ns = {'__name__': 'instrumented_3366_iterated_contextual'}
    exec(compile(source, str(BASE), 'exec'), ns, ns)
    ns['main']()
    result = json.loads(BASE_RESULT.read_text())
    result['schema'] = 'mathgraph.3366-iterated-contextual-contraction.v1'
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(
        'ITERATED_CONTEXTUAL_SUMMARY',
        json.dumps(result['attribution']['iterated_contextual_contraction'], sort_keys=True),
        flush=True,
    )


if __name__ == '__main__':
    main()

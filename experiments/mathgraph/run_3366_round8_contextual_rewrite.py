import json
from pathlib import Path

BASE = Path('experiments/mathgraph/run_3366_round8_interface_attribution.py')
BASE_RESULT = Path('experiments/mathgraph/results/3366-round8-interface-attribution.json')
OUT = Path('experiments/mathgraph/results/3366-round8-contextual-rewrite.json')

INJECT = r'''
    # Exact one-step contextual rewrite attribution from the frozen round-8 active set.
    # This deliberately requires exact subterm equality (not the earlier variable-level
    # unification diagnostic), then constructs the ordinary congruence/transitivity DAG
    # and independently replays any direct target hit.
    active_best_distance = min(
        min(
            m.structural_distance(nodes[i].lhs, tl) + m.structural_distance(nodes[i].rhs, tr),
            m.structural_distance(nodes[i].lhs, tr) + m.structural_distance(nodes[i].rhs, tl),
        ) for i in active
    ) if active else None
    overlap_count = 0
    strict_count = 0
    best_overlap = None
    direct = None

    def wrap_exact(inner_id, outer_term, path, d):
        cur = inner_id
        # Lift the exact inner equality from the selected subterm back to the root.
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
                    context=('left', sibling), constructor='round8-contextual-rewrite'
                )
            else:
                sibling = parent_term[1]
                node = m.EqualityNode(
                    ('op', sibling, p.lhs), ('op', sibling, p.rhs),
                    'congruence on right child', parents=(cur,),
                    context=('right', sibling), constructor='round8-contextual-rewrite'
                )
            cur = add(node, d)
            if cur is None:
                return None
        return cur

    # Restrict the outer equation to the 16 retained states, but allow any verified
    # generated/source equality as the inner rewrite law. Bare variable positions are
    # excluded exactly as in ContextualSearch.
    for outer_id in active:
        outer = nodes[outer_id]
        for outer_side, outer_term in enumerate((outer.lhs, outer.rhs)):
            other = outer.rhs if outer_side == 0 else outer.lhs
            for path in m.nonvariable_positions(outer_term, 8, include_root=False):
                before = m.get_subterm(outer_term, path)
                for inner_id in allids:
                    inner = nodes[inner_id]
                    for inner_side, after in ((0, inner.rhs), (1, inner.lhs)):
                        expected = inner.lhs if inner_side == 0 else inner.rhs
                        if before != expected:
                            continue
                        changed = m.replace_subterm(outer_term, path, after)
                        if changed == outer_term or m.term_size(changed) > MAX_TERM_SIZE:
                            continue
                        overlap_count += 1
                        consequence = (other, changed)
                        dist = min(
                            m.structural_distance(other, tl) + m.structural_distance(changed, tr),
                            m.structural_distance(other, tr) + m.structural_distance(changed, tl),
                        )
                        if active_best_distance is not None and dist < active_best_distance:
                            strict_count += 1
                        rec = {
                            'outer_id': outer_id, 'inner_id': inner_id,
                            'outer_side': outer_side, 'inner_side': inner_side,
                            'path': ''.join(path),
                            'before': m.render_term(before), 'after': m.render_term(after),
                            'other': m.render_term(other), 'changed': m.render_term(changed),
                            'distance': dist,
                        }
                        if best_overlap is None or (dist, m.term_size(changed), outer_id, inner_id) < (
                            best_overlap['distance'], best_overlap['changed_size'],
                            best_overlap['outer_id'], best_overlap['inner_id']
                        ):
                            rec['changed_size'] = m.term_size(changed)
                            best_overlap = rec
                        if consequence in ((tl, tr), (tr, tl)) and direct is None:
                            # Build the exact replayable DAG witness.
                            inner_oriented = inner_id if inner_side == 0 else S(inner_id, 9)
                            if inner_oriented is None:
                                continue
                            wrapped = wrap_exact(inner_oriented, outer_term, path, 9)
                            if wrapped is None:
                                continue
                            outer_oriented = S(outer_id, 9) if outer_side == 0 else outer_id
                            if outer_oriented is None:
                                continue
                            left, right = nodes[outer_oriented], nodes[wrapped]
                            if left.rhs != right.lhs:
                                continue
                            root = add(m.EqualityNode(
                                left.lhs, right.rhs, 'transitivity',
                                parents=(outer_oriented, wrapped),
                                constructor='round8-contextual-rewrite'
                            ), 9)
                            if root is None:
                                continue
                            if (nodes[root].lhs, nodes[root].rhs) == (tr, tl):
                                root = S(root, 9)
                            replayed = bool(root is not None and m.replay_dag(
                                source, nodes, root,
                                maximum_term_size=MAX_TERM_SIZE,
                                maximum_nodes=MAX_NODES,
                            ))
                            direct = dict(rec)
                            direct['root'] = root
                            direct['replayed'] = replayed
    attribution['contextual_rewrite'] = {
        'exact_overlap_candidates': overlap_count,
        'active_best_distance': active_best_distance,
        'strict_contractions': strict_count,
        'best': best_overlap,
        'direct_target': direct,
        'promotion_gate': bool(
            (direct is not None and direct.get('replayed')) or strict_count > 0
        ),
    }
'''


def main():
    source = BASE.read_text()
    marker = "    out={'schema':'mathgraph.3366-round8-interface-attribution.v1'"
    if marker not in source:
        raise RuntimeError('instrumentation marker not found')
    source = source.replace(marker, INJECT + "\n" + marker, 1)
    ns = {'__name__': 'instrumented_round8_contextual_rewrite'}
    exec(compile(source, str(BASE), 'exec'), ns, ns)
    ns['main']()
    result = json.loads(BASE_RESULT.read_text())
    result['schema'] = 'mathgraph.3366-round8-contextual-rewrite.v1'
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print('CONTEXTUAL_REWRITE_SUMMARY', json.dumps(result['attribution']['contextual_rewrite'], sort_keys=True), flush=True)


if __name__ == '__main__':
    main()

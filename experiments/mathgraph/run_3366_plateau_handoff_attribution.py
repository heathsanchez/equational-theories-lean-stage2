import json
from pathlib import Path

SRC = Path('experiments/mathgraph/run_3366_iterated_contextual_contraction.py')
BASE_RESULT = Path('experiments/mathgraph/results/3366-round8-interface-attribution.json')
OUT = Path('experiments/mathgraph/results/3366-plateau-handoff-attribution.json')

INJECT = r'''
    # Distance-100 plateau handoff attribution. At this point the contextual
    # contraction loop has completed exactly two strict generations, so
    # `current` is the replayable distance-100 frontier (<=8 states).
    PLATEAU = 100
    handoff = {}
    plateau = list(current)
    allids = list(dict.fromkeys(list(best.values())))

    def replay_ok(root):
        return bool(root is not None and m.replay_dag(
            source, nodes, root,
            maximum_term_size=MAX_TERM_SIZE,
            maximum_nodes=MAX_NODES,
        ))

    def record_best(kind, candidates):
        good = []
        replay_failures = 0
        for root, meta in candidates:
            if root is None:
                continue
            d = pair_distance(nodes[root].lhs, nodes[root].rhs)
            if d >= PLATEAU:
                continue
            if not replay_ok(root):
                replay_failures += 1
                continue
            good.append((d, m.term_size(nodes[root].lhs) + m.term_size(nodes[root].rhs), root, meta))
        good.sort(key=lambda x: (x[0], x[1], x[2]))
        bestrow = None
        if good:
            d, size, root, meta = good[0]
            bestrow = {'distance': d, 'size': size, 'root': root, 'meta': meta}
        handoff[kind] = {
            'strict_replayable': len(good),
            'replay_failures': replay_failures,
            'best': bestrow,
            'promotion': bool(good),
        }

    # 1) Exact transitivity against the full generated pool.
    tcands = []
    exact_pairs = 0
    for i in plateau:
        a = nodes[i]
        for j in allids:
            b = nodes[j]
            if a.rhs == b.lhs:
                exact_pairs += 1
                k = T(i, j, 11)
                if k is not None:
                    tcands.append((k, {'left': i, 'right': j}))
            if b.rhs == a.lhs:
                exact_pairs += 1
                k = T(j, i, 11)
                if k is not None:
                    tcands.append((k, {'left': j, 'right': i}))
    record_best('full_pool_transitivity', tcands)
    handoff['full_pool_transitivity']['exact_pairs'] = exact_pairs

    # 2) Binary congruence using plateau states with a target-ranked slice of
    # the full generated pool. This tests whether a congruence handoff creates
    # a strict contraction without reopening the broad search.
    ranked_pool = sorted(allids, key=lambda i: (
        pair_distance(nodes[i].lhs, nodes[i].rhs),
        m.term_size(nodes[i].lhs) + m.term_size(nodes[i].rhs), i
    ))[:512]
    ccands = []
    attempted_congruence = 0
    for i in plateau:
        for j in ranked_pool:
            for k in (C(i, j, 11), C(j, i, 11)):
                attempted_congruence += 1
                if k is not None:
                    ccands.append((k, {'a': i, 'b': j}))
    record_best('binary_congruence', ccands)
    handoff['binary_congruence']['attempted'] = attempted_congruence

    # 3) Fresh source instantiation from terms exposed by the plateau, followed
    # by one exact chain with a plateau state. This is the bounded source
    # re-entry handoff test; no teacher terms are supplied.
    useful = []
    for i in plateau:
        for side in (nodes[i].lhs, nodes[i].rhs):
            for t in m.walk_subterms(side):
                if m.term_size(t) <= 25 and t not in useful:
                    useful.append(t)
    for t in list(m.walk_subterms(tl)) + list(m.walk_subterms(tr)):
        if t not in useful:
            useful.append(t)
    useful = sorted(useful, key=lambda t: (m.term_size(t), m.render_term(t)))[:32]
    sl, sr, svars = source
    reentry_nodes = []
    mappings_seen = set()
    attempts = 0
    for pattern in (sl, sr):
        for concrete in useful:
            partial = {}
            if not m.match_term(pattern, concrete, partial):
                continue
            missing = [v for v in svars if v not in partial]
            fill = useful[:8]
            import itertools
            for vals in itertools.product(fill, repeat=len(missing)):
                mapping = dict(partial)
                mapping.update(zip(missing, vals))
                if any(v not in mapping for v in svars):
                    continue
                key = tuple((v, mapping[v]) for v in svars)
                if key in mappings_seen:
                    continue
                mappings_seen.add(key)
                lhs = m.substitute(sl, mapping); rhs = m.substitute(sr, mapping)
                attempts += 1
                if m.term_size(lhs) > MAX_TERM_SIZE or m.term_size(rhs) > MAX_TERM_SIZE:
                    continue
                q = add(m.EqualityNode(
                    lhs, rhs, 'source instance', substitution=key,
                    orientation=False, constructor='plateau-source-reentry'
                ), 11)
                if q is not None:
                    reentry_nodes.append(q)
                if attempts >= 5000:
                    break
            if attempts >= 5000:
                break
        if attempts >= 5000:
            break
    rcands = []
    exact_reentry_chains = 0
    for i in plateau:
        for j in reentry_nodes:
            a, b = nodes[i], nodes[j]
            for jj in (j, S(j, 11)):
                if jj is None:
                    continue
                b2 = nodes[jj]
                if a.rhs == b2.lhs:
                    exact_reentry_chains += 1
                    k = T(i, jj, 11)
                    if k is not None:
                        rcands.append((k, {'plateau': i, 'source': jj}))
                if b2.rhs == a.lhs:
                    exact_reentry_chains += 1
                    k = T(jj, i, 11)
                    if k is not None:
                        rcands.append((k, {'source': jj, 'plateau': i}))
    record_best('source_reentry', rcands)
    handoff['source_reentry'].update({
        'source_attempts': attempts,
        'source_nodes': len(reentry_nodes),
        'exact_chains': exact_reentry_chains,
    })

    # 4) Exact contextual overlap from plateau states against the full generated
    # pool. This mirrors the existing contextual-overlap constructor but asks
    # only whether the handoff itself can get below the plateau.
    ocands = []
    overlap_exact = 0
    for outer_id in plateau:
        outer = nodes[outer_id]
        for outer_side, outer_term in enumerate((outer.lhs, outer.rhs)):
            other = outer.rhs if outer_side == 0 else outer.lhs
            for path in m.nonvariable_positions(outer_term, 10, include_root=False):
                before = m.get_subterm(outer_term, path)
                for inner_id in allids:
                    inner = nodes[inner_id]
                    for inner_side, expected, after in (
                        (0, inner.lhs, inner.rhs), (1, inner.rhs, inner.lhs)
                    ):
                        if before != expected:
                            continue
                        changed = m.replace_subterm(outer_term, path, after)
                        if changed == outer_term or m.term_size(changed) > MAX_TERM_SIZE:
                            continue
                        overlap_exact += 1
                        d = pair_distance(other, changed)
                        if d >= PLATEAU:
                            continue
                        rec = {
                            'outer_id': outer_id, 'inner_id': inner_id,
                            'outer_side': outer_side, 'inner_side': inner_side,
                            'path_tuple': tuple(path), 'distance': d,
                            'size': m.term_size(other) + m.term_size(changed),
                            'lhs': other, 'rhs': changed,
                        }
                        root = materialize(rec, 11)
                        if root is not None:
                            ocands.append((root, {
                                'outer': outer_id, 'inner': inner_id,
                                'path': ''.join(path), 'inner_side': inner_side,
                            }))
    record_best('contextual_overlap', ocands)
    handoff['contextual_overlap']['exact_candidates'] = overlap_exact

    direct = None
    for kind, row in handoff.items():
        if isinstance(row, dict) and row.get('best'):
            root = row['best']['root']
            if (nodes[root].lhs, nodes[root].rhs) in ((tl, tr), (tr, tl)):
                rr = root
                if (nodes[root].lhs, nodes[root].rhs) == (tr, tl):
                    rr = S(root, 11)
                if replay_ok(rr):
                    direct = {'operator': kind, 'root': rr, 'replayed': True}
                    break
    attribution['plateau_handoff'] = {
        'plateau_distance': PLATEAU,
        'plateau_states': len(plateau),
        'operators': handoff,
        'direct_target': direct,
        'promotion_gate': bool(direct) or any(
            isinstance(row, dict) and row.get('promotion') for row in handoff.values()
        ),
    }
'''


def main():
    source = SRC.read_text()
    # Reproduce only the two strict contextual generations that reached the
    # distance-100 plateau, then run handoff attribution there.
    source = source.replace('CONTEXT_GENERATIONS = 3', 'CONTEXT_GENERATIONS = 2', 1)
    marker = "    attribution['iterated_contextual_contraction'] = {"
    if marker not in source:
        raise RuntimeError('handoff injection marker not found')
    source = source.replace(marker, INJECT + "\n" + marker, 1)
    source = source.replace(
        "result['schema'] = 'mathgraph.3366-iterated-contextual-contraction.v1'",
        "result['schema'] = 'mathgraph.3366-plateau-handoff-attribution.v1'",
        1,
    )
    ns = {'__name__': 'instrumented_3366_plateau_handoff'}
    exec(compile(source, str(SRC), 'exec'), ns, ns)
    ns['main']()
    result = json.loads(BASE_RESULT.read_text())
    result['schema'] = 'mathgraph.3366-plateau-handoff-attribution.v1'
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print('PLATEAU_HANDOFF_SUMMARY', json.dumps(result['attribution']['plateau_handoff'], sort_keys=True), flush=True)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
import argparse, importlib.util, json, time


def load(path):
    spec = importlib.util.spec_from_file_location('mgsolver', path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--solver', required=True)
    ap.add_argument('--row', required=True)
    a = ap.parse_args()
    m = load(a.solver)
    row = json.load(open(a.row))
    source = m.parse_equation(row['equation1'])
    target = m.parse_equation(row['equation2'])

    base = dict(m.COMPACT_SUPERPOSITION_PROBE)
    base.update({
        'maximum_term_size': 75,
        'maximum_replay_term_size': 320,
        'maximum_depth': 12,
        'maximum_rules': 896,
        'maximum_rounds': 96,
        'new_clauses_per_round': 64,
        'maximum_clauses': 14000,
        'normalization_steps': 256,
        'maximum_proof_nodes': 70000,
    })

    def setup(goal, seconds):
        lim = dict(base)
        lim['seconds'] = seconds
        e = m.TargetGroundedRefutation(source, goal, time.monotonic() + seconds, lim)
        return e, e.search

    def orient(q, rev):
        return q if not rev else m.Recipe(q.rhs, q.lhs, 'symmetry', (q,))

    def exact(engine, q):
        q = engine.inline_recipe(q)
        return (q.lhs, q.rhs) == target[:2] or (q.lhs, q.rhs) == (target[1], target[0])

    def replay_target(engine, search, q):
        q = engine.inline_recipe(q)
        if (q.lhs, q.rhs) == (target[1], target[0]):
            q = m.Recipe(q.rhs, q.lhs, 'symmetry', (q,))
        if (q.lhs, q.rhs) != target[:2]:
            return False, 0
        nodes, root = search.compile(q)
        ok = m.replay_dag(source, nodes, root, maximum_term_size=320, maximum_nodes=70000)
        return ok, len(nodes)

    # Deterministic pre-world: same structural budgets as the clean quotient run.
    engine, search = setup(target, 1200.0)
    pre_trace = []
    for _ in range(3):
        rules = search.rules()
        snap = list(rules)
        props = []
        proposed = 0
        stop = False
        for oi, outer in enumerate(snap):
            if stop:
                break
            for ii, inner in enumerate(snap):
                if stop:
                    break
                for path in m.nonvariable_positions(outer.lhs, maximum_depth=12, include_root=True):
                    c = search.critical_pair(outer, inner, oi, ii, path)
                    if c is None:
                        continue
                    c = search.interreduce(c, rules)
                    props.append((search.target_score(c), c))
                    proposed += 1
                    if proposed >= 512:
                        stop = True
                        break
        props.sort(key=lambda z: z[0])
        added = 0
        for _, q in props:
            if search.add_clause(q):
                search.superpositions += 1
                added += 1
            if added >= 64:
                break
        pre_trace.append({'proposed': proposed, 'added': added, 'clauses': len(search.clauses)})

    rules = search.rules()
    partners = sorted(rules, key=search.target_score)[:24]

    # First-step candidates are generated structurally, not selected by a wall clock.
    seen = set()
    first = []
    for oi, outer in enumerate(rules):
        if len(first) >= 160:
            break
        for ii, inner in enumerate(rules):
            if len(first) >= 160:
                break
            for path in m.nonvariable_positions(outer.lhs, maximum_depth=12, include_root=True):
                c = search.critical_pair(outer, inner, oi, ii, path)
                if c is None:
                    continue
                c = search.interreduce(c, rules)
                if c.lhs == c.rhs:
                    continue
                key = (search.alpha_signature(c.lhs, c.rhs), c.lhs, c.rhs)
                if key in seen:
                    continue
                seen.add(key)
                first.append(c)
                if len(first) >= 160:
                    break

    # MSI continuation closure: pull target relevance backward from legal children.
    scored = []
    exact_child = None
    continuation_calls = 0
    for ci, candidate in enumerate(first):
        best = search.target_score(candidate)
        best_child = None
        for pi, partner in enumerate(partners):
            for a0, b0 in ((candidate, partner), (partner, candidate)):
                for ar in (False, True):
                    aa = orient(a0, ar)
                    for br in (False, True):
                        bb = orient(b0, br)
                        for path in m.nonvariable_positions(aa.lhs, maximum_depth=8, include_root=True):
                            child = search.critical_pair(aa, bb, ci, pi, path)
                            if child is None:
                                continue
                            continuation_calls += 1
                            child = search.interreduce(child, rules)
                            score = search.target_score(child)
                            if score < best:
                                best = score
                                best_child = child
                            if exact(engine, child):
                                exact_child = child
                                break
                        if exact_child is not None:
                            break
                    if exact_child is not None:
                        break
                if exact_child is not None:
                    break
            if exact_child is not None:
                break
        scored.append((best, search.target_score(candidate), candidate, best_child))
        if exact_child is not None:
            break

    result = {
        'id': row['id'],
        'pre_trace': pre_trace,
        'first_candidates': len(first),
        'partners': len(partners),
        'continuation_calls': continuation_calls,
        'exact_child': exact_child is not None,
        'exact_child_replay': False,
        'target': {'found': False, 'replay': False},
    }

    if exact_child is not None:
        ok, nodes = replay_target(engine, search, exact_child)
        result['exact_child_replay'] = ok
        result['exact_child_nodes'] = nodes

    # If no direct two-step target, retain clauses whose *reachable continuation*
    # is best, rather than clauses whose present endpoint is best.
    if exact_child is None:
        scored.sort(key=lambda z: (z[0], z[1]))
        chosen = [q for _, _, q, _ in scored[:16]]
        te, ts = setup(target, 360.0)
        added = [bool(ts.add_clause(q)) for q in chosen]
        tq = ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve()
        out = {
            'found': tq is not None,
            'replay': False,
            'added': sum(added),
            'selected': len(chosen),
            'rounds': ts.rounds,
            'superpositions': ts.superpositions,
            'clauses': len(ts.clauses),
        }
        if tq is not None:
            ok, nodes = replay_target(te, ts, tq)
            out['replay'] = ok
            out['proof_nodes'] = nodes
        result['target'] = out

    print('CONTINUATION_PULLBACK ' + json.dumps(result, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()

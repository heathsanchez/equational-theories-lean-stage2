#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import sys
import time
from pathlib import Path

HELPER = Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec = importlib.util.spec_from_file_location('normal0040_compat_helper', HELPER)
h = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = h
spec.loader.exec_module(h)

ROOT = Path('/tmp/sair_stage1_eval')
OUT = Path('experiments/mathgraph/results/normal0040-compatibility-lift.json')
RID = 'evaluation_normal_0040'
MAX_NODES = 120000
MAX_TERM_SIZE = 45
BEAM = 220
ROUNDS = 7
SECONDS = 40.0


def load_row():
    p = ROOT / 'evaluation_normal.jsonl'
    for line_no, line in enumerate(p.read_text().splitlines(), 1):
        if not line.strip():
            continue
        row = json.loads(line)
        rid = row.get('id') or row.get('problem_id') or row.get('name') or f'evaluation_normal_{line_no-1:04d}'
        if rid == RID:
            return row
    raise RuntimeError('normal0040 not found')


def equation_fields(row):
    def pick(*keys):
        for k in keys:
            if k in row and row[k] is not None:
                return row[k]
        return None
    a = pick('equation1', 'equation_1', 'source', 'hypothesis', 'lhs_equation')
    b = pick('equation2', 'equation_2', 'target', 'conclusion', 'rhs_equation')
    if not isinstance(a, str) or not isinstance(b, str):
        raise RuntimeError('cannot locate equation fields')
    return a, b


def positions(term, path=()):
    yield path, term
    if term[0] == 'op':
        yield from positions(term[1], path + ('L',))
        yield from positions(term[2], path + ('R',))


def main():
    m = h.load_solver()
    row = load_row()
    eq1, eq2 = equation_fields(row)
    source = m.parse_equation(eq1)
    target = m.parse_equation(eq2)
    tl, tr = target[:2]
    sl, sr, sv = source
    deadline = time.monotonic() + SECONDS

    nodes = []
    best = {}
    source_cache = {}
    counters = {
        'source_instances': 0,
        'compatibility_lifts': 0,
        'transitivity_steps': 0,
        'generated_states': 0,
    }

    def add(node):
        if len(nodes) >= MAX_NODES:
            return None
        if m.term_size(node.lhs) > MAX_TERM_SIZE or m.term_size(node.rhs) > MAX_TERM_SIZE:
            return None
        key = (node.lhs, node.rhs)
        old = best.get(key)
        if old is not None:
            return old
        i = len(nodes)
        nodes.append(node)
        best[key] = i
        return i

    def M(a, b):
        return ('op', a, b)

    def R(t):
        return add(m.EqualityNode(t, t, 'reflexivity', constructor='normal0040-compatibility-lift'))

    def S(i):
        if i is None:
            return None
        p = nodes[i]
        return add(m.EqualityNode(p.rhs, p.lhs, 'symmetry', parents=(i,), constructor='normal0040-compatibility-lift'))

    def T(i, j):
        if i is None or j is None:
            return None
        a, b = nodes[i], nodes[j]
        if a.rhs != b.lhs:
            return None
        k = add(m.EqualityNode(a.lhs, b.rhs, 'transitivity', parents=(i, j), constructor='normal0040-compatibility-lift'))
        if k is not None:
            counters['transitivity_steps'] += 1
        return k

    def H(values):
        key = tuple(values)
        if key in source_cache:
            return source_cache[key]
        mp = dict(zip(sv, values))
        lhs, rhs = m.substitute(sl, mp), m.substitute(sr, mp)
        i = add(m.EqualityNode(
            lhs, rhs, 'source instance',
            substitution=tuple((v, mp[v]) for v in sv),
            constructor='normal0040-compatibility-lift',
        ))
        source_cache[key] = i
        if i is not None:
            counters['source_instances'] += 1
        return i

    def lift(eq_id, outer, path):
        if eq_id is None:
            return None
        cur = outer
        frames = []
        for d in path:
            if cur[0] != 'op':
                return None
            if d == 'L':
                frames.append(('L', cur[2]))
                cur = cur[1]
            else:
                frames.append(('R', cur[1]))
                cur = cur[2]
        if cur != nodes[eq_id].lhs:
            return None
        out = eq_id
        for d, sibling in reversed(frames):
            p = nodes[out]
            if d == 'L':
                node = m.EqualityNode(
                    M(p.lhs, sibling), M(p.rhs, sibling),
                    'congruence on left child', parents=(out,),
                    context=('left', sibling), constructor='normal0040-compatibility-lift',
                )
            else:
                node = m.EqualityNode(
                    M(sibling, p.lhs), M(sibling, p.rhs),
                    'congruence on right child', parents=(out,),
                    context=('right', sibling), constructor='normal0040-compatibility-lift',
                )
            out2 = add(node)
            if out2 is None:
                return None
            out = out2
            counters['compatibility_lifts'] += 1
        return out

    target_terms = set(m.walk_subterms(tl)) | set(m.walk_subterms(tr))
    seed_terms = target_terms | {('var', v) for v in set(source[2]) | set(target[2])}
    # Keep substitutions deliberately small and target-conditioned: this is a
    # constructor separator, not a wider saturation run.
    pool = sorted(seed_terms, key=lambda t: (m.term_size(t), m.structural_distance(t, tr), m.render_term(t)))[:14]

    root = R(tl)
    states = {tl: root}
    snapshots = []
    found = states.get(tr)

    def state_score(term):
        overlap = sum(st in target_terms for st in m.walk_subterms(term))
        return (m.structural_distance(term, tr), abs(m.term_size(term) - m.term_size(tr)), -overlap, m.term_size(term), m.render_term(term))

    for round_no in range(1, ROUNDS + 1):
        if found is not None or time.monotonic() >= deadline or len(nodes) >= MAX_NODES:
            break
        ranked_terms = sorted(states, key=state_score)[:BEAM]
        next_states = dict(states)
        for term in ranked_terms:
            if time.monotonic() >= deadline or len(nodes) >= MAX_NODES:
                break
            state_id = states[term]
            for path, subterm in positions(term):
                # Contract any exact source-RHS instance already present at this hole.
                partial = {}
                if m.match_term(sr, subterm, partial) and all(v in partial for v in sv):
                    h_id = H(tuple(partial[v] for v in sv))
                    s_id = S(h_id)
                    l_id = lift(s_id, term, path)
                    n_id = T(state_id, l_id)
                    if n_id is not None:
                        new_term = nodes[n_id].rhs
                        if new_term not in next_states or state_score(new_term) < state_score(nodes[next_states[new_term]].rhs):
                            next_states[new_term] = n_id
                            counters['generated_states'] += 1
                # Expand the selected hole with target-conditioned source instances.
                # For normal0040 the source lhs is a variable, so binding that variable
                # to the exact selected subterm is the compatibility-critical move.
                for yv in pool[:8]:
                    for zv in pool[:8]:
                        if time.monotonic() >= deadline or len(nodes) >= MAX_NODES:
                            break
                        mp = {sv[0]: subterm}
                        if len(sv) > 1:
                            mp[sv[1]] = yv
                        if len(sv) > 2:
                            mp[sv[2]] = zv
                        vals = tuple(mp[v] for v in sv)
                        h_id = H(vals)
                        if h_id is None or nodes[h_id].lhs != subterm:
                            continue
                        l_id = lift(h_id, term, path)
                        n_id = T(state_id, l_id)
                        if n_id is None:
                            continue
                        new_term = nodes[n_id].rhs
                        if new_term not in next_states:
                            next_states[new_term] = n_id
                            counters['generated_states'] += 1
                    if time.monotonic() >= deadline or len(nodes) >= MAX_NODES:
                        break
        states = dict(sorted(next_states.items(), key=lambda kv: state_score(kv[0]))[:BEAM * 3])
        found = states.get(tr)
        best_term = min(states, key=state_score)
        snapshots.append({
            'round': round_no,
            'states': len(states),
            'nodes': len(nodes),
            'best_term': m.render_term(best_term),
            'best_distance': m.structural_distance(best_term, tr),
            'best_size': m.term_size(best_term),
            'found': found is not None,
            **counters,
        })
        print('NORMAL0040_COMPAT_ROUND', json.dumps(snapshots[-1], sort_keys=True), flush=True)

    replayed = False
    replay_error = None
    proof = None
    if found is not None:
        try:
            replayed = bool(m.replay_dag(source, nodes, found, maximum_term_size=MAX_TERM_SIZE, maximum_nodes=MAX_NODES))
        except Exception as exc:
            replay_error = type(exc).__name__ + ': ' + str(exc)
        proof = h.proof_summary(nodes, found)

    best_term = min(states, key=state_score)
    out = {
        'schema': 'mathgraph.normal0040-compatibility-lift.v1',
        'id': RID,
        'equation1': eq1,
        'equation2': eq2,
        'operator': 'single-hole-compatibility-lift',
        'pool': [m.render_term(t) for t in pool],
        'found': found is not None,
        'replayed': replayed,
        'replay_error': replay_error,
        'proof': proof,
        'nodes': len(nodes),
        'states': len(states),
        'best_term': m.render_term(best_term),
        'best_distance': m.structural_distance(best_term, tr),
        'snapshots': snapshots,
        'counters': counters,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + '\n')
    print('NORMAL0040_COMPAT_SUMMARY', json.dumps({k: out[k] for k in ('found','replayed','nodes','states','best_term','best_distance')}, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()

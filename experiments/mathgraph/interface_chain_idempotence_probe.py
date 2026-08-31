#!/usr/bin/env python3
"""Diagnostic: compose two discovered one-variable quotient interfaces.

The prior quotient experiments independently exposed replay-certified laws
  L2: x = x * (x * x)
  L3: x = x * (x * (x * x))
This probe asks whether their *composition* is the missing developmental step.
It reconstructs proofs of both laws from the original source, composes them
proof-theoretically into x = x*x, replay-checks that certificate, and then
retests the untouched 0036 target with only the certified interface laws.

This is a causal diagnostic, not yet a production discovery mechanism.
"""
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
    args = ap.parse_args()
    m = load(args.solver)
    row = json.load(open(args.row))
    source = m.parse_equation(row['equation1'])
    target = m.parse_equation(row['equation2'])

    base = dict(m.COMPACT_SUPERPOSITION_PROBE)
    base.update({
        'maximum_term_size': 80,
        'maximum_replay_term_size': 320,
        'maximum_depth': 14,
        'maximum_rules': 1024,
        'maximum_rounds': 160,
        'new_clauses_per_round': 96,
        'maximum_clauses': 18000,
        'normalization_steps': 320,
        'maximum_proof_nodes': 80000,
    })

    def setup(goal, seconds):
        lim = dict(base)
        lim['seconds'] = seconds
        e = m.TargetGroundedRefutation(source, goal, time.monotonic() + seconds, lim)
        return e, e.search

    def prove(text, seconds):
        goal = m.parse_equation(text)
        e, s = setup(goal, seconds)
        found = s.solve()
        if found is None:
            return goal, None, {'found': False, 'replay': False}
        q = e.inline_recipe(found)
        if (q.lhs, q.rhs) == (goal[1], goal[0]):
            q = m.Recipe(q.rhs, q.lhs, 'symmetry', (q,))
        if (q.lhs, q.rhs) != goal[:2]:
            return goal, None, {'found': True, 'endpoint': False, 'replay': False}
        nodes, root = s.compile(q)
        ok = m.replay_dag(source, nodes, root, maximum_term_size=320, maximum_nodes=80000)
        return goal, q if ok else None, {
            'found': True, 'endpoint': True, 'replay': bool(ok),
            'proof_nodes': len(nodes), 'rounds': s.rounds,
            'superpositions': s.superpositions, 'clauses': len(s.clauses),
        }

    g2, l2, r2 = prove('x = x * (x * x)', 150.0)
    g3, l3, r3 = prove('x = x * (x * (x * x))', 180.0)

    report = {'id': row['id'], 'l2': r2, 'l3': r3,
              'idempotence': {'constructed': False, 'replay': False},
              'target': {'found': False, 'replay': False}}

    if l2 is None or l3 is None:
        print('INTERFACE_CHAIN ' + json.dumps(report, sort_keys=True), flush=True)
        return

    x = ('var', 'x')
    xx = ('op', x, x)
    xxx = ('op', x, xx)                 # x*(x*x)
    xxxx = ('op', x, xxx)               # x*(x*(x*x))

    # Normalize orientation defensively.
    if (l2.lhs, l2.rhs) != (x, xxx) or (l3.lhs, l3.rhs) != (x, xxxx):
        report['idempotence']['endpoint_mismatch'] = True
        print('INTERFACE_CHAIN ' + json.dumps(report, sort_keys=True), flush=True)
        return

    # L2 gives xxx = x by symmetry. Lift it under the context x * [·]:
    # xxxx = xx. Then L3 ; lifted(L2^-1) gives x = xx.
    l2sym = m.Recipe(xxx, x, 'symmetry', (l2,))
    lifted = m.Recipe(
        xxxx, xx, 'congruence', (l2sym,), ('right', x)
    )
    idem = m.Recipe(x, xx, 'transitivity', (l3, lifted))

    ie, isearch = setup(m.parse_equation('x = x * x'), 5.0)
    nodes, root = isearch.compile(idem)
    idem_ok = m.replay_dag(source, nodes, root, maximum_term_size=320, maximum_nodes=80000)
    report['idempotence'] = {
        'constructed': True, 'replay': bool(idem_ok), 'proof_nodes': len(nodes),
        'lhs': m.render_term(idem.lhs), 'rhs': m.render_term(idem.rhs),
    }

    if not idem_ok:
        print('INTERFACE_CHAIN ' + json.dumps(report, sort_keys=True), flush=True)
        return

    # Fresh target world: promote only replay-certified consequences.
    te, ts = setup(target, 240.0)
    added = 0
    for q in (l2, l3, idem):
        if ts.add_clause(q):
            added += 1
    found = ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve()
    tr = {'found': found is not None, 'replay': False, 'added': added,
          'rounds': ts.rounds, 'superpositions': ts.superpositions,
          'clauses': len(ts.clauses)}
    if found is not None:
        q = te.inline_recipe(found)
        if (q.lhs, q.rhs) == (target[1], target[0]):
            q = m.Recipe(q.rhs, q.lhs, 'symmetry', (q,))
        if (q.lhs, q.rhs) == target[:2]:
            ns, rr = ts.compile(q)
            tr['replay'] = m.replay_dag(source, ns, rr, maximum_term_size=320, maximum_nodes=80000)
            tr['proof_nodes'] = len(ns)
    report['target'] = tr
    print('INTERFACE_CHAIN ' + json.dumps(report, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()

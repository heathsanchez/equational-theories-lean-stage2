import importlib.util
import json
import sys
import time
from pathlib import Path

SOLVER = Path('submissions/mathgraph/solver.py')
SPEC = importlib.util.spec_from_file_location('mg_prefix', SOLVER)
m = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = m
SPEC.loader.exec_module(m)


def load_case():
    for path in Path('examples/problems').glob('*.jsonl'):
        for line in path.read_text().splitlines():
            if not line.strip():
                continue
            row = json.loads(line)
            if row.get('id') == 'hard2_0199':
                return row
    raise SystemExit('hard2_0199 not found')


def replay(source, target, search, recipe):
    if recipe is None:
        return False
    try:
        nodes, root = search.compile(recipe)
        return bool(
            (nodes[root].lhs, nodes[root].rhs) == target[:2]
            and m.replay_dag(
                source, nodes, root,
                maximum_term_size=search.limits.get(
                    'maximum_replay_term_size', search.limits['maximum_term_size']
                ),
                maximum_nodes=search.limits['maximum_proof_nodes'],
            )
        )
    except Exception:
        return False


def probe(source, target, label):
    limits = dict(m.COMPACT_SUPERPOSITION_PROBE)
    seconds = limits['seconds']
    started = time.monotonic()
    try:
        s = m.CompactSuperposition(
            m, source, target, time.monotonic() + seconds, limits
        )
        recipe = s.solve()
        closed = replay(source, target, s, recipe)
        row = {
            'label': label, 'closed': closed,
            'seconds': time.monotonic() - started,
            'clauses': len(s.clauses), 'rounds': s.rounds,
            'superpositions': s.superpositions, 'reductions': s.reductions,
            'limits': limits,
        }
    except Exception as exc:
        row = {'label': label, 'closed': False, 'error': type(exc).__name__}
    print('PREFIX_PROBE', json.dumps(row, sort_keys=True), flush=True)
    return row


def run_prefixes(source, target):
    out = [probe(source, target, 'clean')]

    # Prefix 1: production initial equality chain.
    try:
        q = m.EqualitySearch(source, target, time.monotonic() + 2.0)
        q.solve()
    except Exception:
        pass
    out.append(probe(source, target, 'after_initial_chain'))

    # Prefix 2: a first ordinary production compact-superposition invocation.
    try:
        limits = dict(m.COMPACT_SUPERPOSITION_PROBE)
        q = m.CompactSuperposition(
            m, source, target,
            time.monotonic() + limits['seconds'], limits
        )
        q.solve()
    except Exception:
        pass
    out.append(probe(source, target, 'after_first_compact'))

    # Prefix 3: production Fin2 enumeration.
    try:
        q = m.FiniteModelEngine(2, source, target, time.monotonic() + 1.0, 0, 16)
        q.search_complete_enumeration(canonical_only=False)
    except Exception:
        pass
    out.append(probe(source, target, 'after_fin2'))

    # Prefix 4: contextual portfolio.
    try:
        old_judge = m.judge
        m.judge = lambda *args, **kwargs: {'status': 'rejected'}
        m.run_contextual_portfolio(source, target, 100.0)
    except Exception:
        pass
    finally:
        try:
            m.judge = old_judge
        except Exception:
            pass
    out.append(probe(source, target, 'after_contextual'))

    # Prefix 5: each promoted re-entry configuration, preserving production order.
    for i, cfg in enumerate(m.PROMOTED_REENTRY_PORTFOLIO):
        try:
            seconds = min(cfg['seconds'], 5.0)
            q = m.EqualitySearch(source, target, time.monotonic() + seconds, cfg['limits'])
            initial = q.solve()
            if initial is None:
                q.max_term_size = cfg['reentry_term_size']
                q.max_derivation_nodes = cfg['reentry_nodes']
                q.max_graph_edges = cfg['reentry_edges']
                q.exhaustion = None
                q.solve_reentry(
                    cfg['generations'], cfg['new_terms'], cfg['instances'],
                    targeted=cfg['targeted'],
                )
        except Exception:
            pass
        out.append(probe(source, target, f'after_reentry_{i}_{cfg.get("name","unnamed")}'))

    return out


def main():
    row = load_case()
    source = m.parse_equation(row['equation1'])
    target = m.parse_equation(row['equation2'])
    rows = run_prefixes(source, target)
    first_failure = None
    previous = None
    for r in rows:
        if previous is not None and previous.get('closed') and not r.get('closed'):
            first_failure = r['label']
            break
        previous = r
    summary = {
        'schema': 'mathgraph.hard2-0199-prefix-contamination.v1',
        'rows': rows,
        'first_prefix_killing_proof': first_failure,
        'all_closed': all(r.get('closed') for r in rows),
    }
    out = Path('experiments/mathgraph/results/hard2-0199-prefix-contamination.json')
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print('PREFIX_SUMMARY', json.dumps({
        'first_prefix_killing_proof': first_failure,
        'all_closed': summary['all_closed'],
    }, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()

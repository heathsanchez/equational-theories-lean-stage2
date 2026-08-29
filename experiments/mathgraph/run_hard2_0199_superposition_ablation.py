import importlib.util
import json
import sys
import time
from pathlib import Path

SOLVER = Path('submissions/mathgraph/solver.py')
SPEC = importlib.util.spec_from_file_location('mg_hard2_0199_ablation', SOLVER)
m = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = m
SPEC.loader.exec_module(m)

SUCCESS = {
    'seconds': 5.0,
    'maximum_term_size': 80,
    'maximum_replay_term_size': 256,
    'maximum_depth': 14,
    'maximum_rules': 384,
    'maximum_rounds': 64,
    'new_clauses_per_round': 256,
    'maximum_clauses': 12000,
    'normalization_steps': 192,
    'maximum_proof_nodes': 50000,
}


def load_case():
    for path in Path('examples/problems').glob('*.jsonl'):
        for line in path.read_text().splitlines():
            if not line.strip():
                continue
            row = json.loads(line)
            if row.get('id') == 'hard2_0199':
                return row
    raise SystemExit('hard2_0199 not found')


def replay(source, target, result, limits):
    if not (isinstance(result, tuple) and len(result) == 2):
        return False
    nodes, root = result
    try:
        return bool(
            (nodes[root].lhs, nodes[root].rhs) == target[:2]
            and m.replay_dag(
                source, nodes, root,
                maximum_term_size=limits.get('maximum_replay_term_size', 256),
                maximum_nodes=limits.get('maximum_proof_nodes', 50000),
            )
        )
    except Exception:
        return False


def run_one(name, source, target, limits):
    seconds = float(limits.get('seconds', 5.0))
    started = time.monotonic()
    try:
        search = m.CompactSuperposition(m, source, target, time.monotonic() + seconds, limits)
        recipe = search.solve()
        result = search.compile(recipe) if recipe is not None else None
        ok = replay(source, target, result, limits)
        row = {
            'name': name,
            'closed': ok,
            'seconds': time.monotonic() - started,
            'clauses': len(getattr(search, 'clauses', ())),
            'rounds': getattr(search, 'rounds', None),
            'superpositions': getattr(search, 'superpositions', None),
            'reductions': getattr(search, 'reductions', None),
            'limits': limits,
        }
    except Exception as exc:
        row = {
            'name': name,
            'closed': False,
            'seconds': time.monotonic() - started,
            'error': f'{type(exc).__name__}: {exc}',
            'limits': limits,
        }
    print('ABLATION_CASE', json.dumps(row, sort_keys=True), flush=True)
    return row


def main():
    case = load_case()
    source = m.parse_equation(case['equation1'])
    target = m.parse_equation(case['equation2'])
    production = dict(getattr(m, 'COMPACT_SUPERPOSITION_PROBE', {}))

    rows = []
    rows.append(run_one('expanded_control', source, target, dict(SUCCESS)))

    # Independently restore each successful parameter to the production value.
    keys = [
        'maximum_term_size', 'maximum_replay_term_size', 'maximum_depth',
        'maximum_rules', 'maximum_rounds', 'new_clauses_per_round',
        'maximum_clauses', 'normalization_steps', 'maximum_proof_nodes',
    ]
    for key in keys:
        if key not in production:
            continue
        limits = dict(SUCCESS)
        limits[key] = production[key]
        rows.append(run_one(f'production_{key}', source, target, limits))

    # Wall-time threshold independent of structural caps.
    for seconds in (0.10, 0.15, 0.25, 0.50, 1.0, 2.0):
        limits = dict(SUCCESS)
        limits['seconds'] = seconds
        rows.append(run_one(f'time_{seconds:g}s', source, target, limits))

    # Full production config as a control.
    prod_full = dict(production)
    prod_full.setdefault('seconds', 0.15)
    rows.append(run_one('production_control', source, target, prod_full))

    decisive = []
    control_ok = rows[0]['closed']
    for row in rows[1:]:
        if control_ok and not row['closed']:
            decisive.append(row['name'])

    summary = {
        'schema': 'mathgraph.hard2-0199-superposition-ablation.v1',
        'production_limits': production,
        'expanded_control_closed': control_ok,
        'decisive_shrinks': decisive,
        'rows': rows,
    }
    out = Path('experiments/mathgraph/results/hard2-0199-superposition-ablation.json')
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    print('ABLATION_SUMMARY', json.dumps({
        'expanded_control_closed': control_ok,
        'decisive_shrinks': decisive,
    }, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()

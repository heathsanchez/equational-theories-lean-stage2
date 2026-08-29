import importlib.util
import json
import sys
import time
from pathlib import Path

SOLVER = Path('submissions/mathgraph/solver.py')
DATA = Path('examples/problems/hard2.jsonl')
OUT = Path('experiments/mathgraph/results/hard2-0199-retry-gate-trace.json')


def load_case():
    for line in DATA.read_text().splitlines():
        row = json.loads(line)
        if row.get('id') == 'hard2_0199':
            return row
    raise RuntimeError('hard2_0199 not found')


def load_solver():
    spec = importlib.util.spec_from_file_location('mathgraph_solver_trace', SOLVER)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def main():
    row = load_case()
    mod = load_solver()
    source = mod.parse_equation(row['equation1'])
    target = mod.parse_equation(row['equation2'])
    limits = dict(mod.COMPACT_SUPERPOSITION_PROBE)
    retry_seconds = 0.15
    trace = {
        'id': 'hard2_0199',
        'retry_entered': True,
        'expanded_seconds': retry_seconds,
        'recipe_found': False,
        'replay_passed': False,
        'judge_accepted': False,
        'compile_passed': False,
    }
    search = mod.CompactSuperposition(
        mod, source, target, time.monotonic() + retry_seconds, limits
    )
    recipe = search.solve()
    trace['recipe_found'] = recipe is not None
    if recipe is not None:
        try:
            nodes, root = search.compile(recipe)
            trace['compile_passed'] = True
            replayed = mod.replay_dag(
                source, nodes, root,
                maximum_term_size=limits.get('maximum_replay_term_size', limits['maximum_term_size']),
                maximum_nodes=limits['maximum_proof_nodes'],
            ) and (nodes[root].lhs, nodes[root].rhs) == target[:2]
            trace['replay_passed'] = bool(replayed)
            if replayed:
                original_judge = mod.judge
                recorded = {'calls': 0, 'verdict': None}
                def fake_judge(verdict, certificate):
                    recorded['calls'] += 1
                    recorded['verdict'] = verdict
                    return {'status': 'accepted'}
                mod.judge = fake_judge
                trace['judge_accepted'] = (
                    mod.finish_compact_superposition_candidate(
                        source, target, search, recipe
                    ) is True
                )
                trace['judge_calls'] = recorded['calls']
                trace['judge_verdict'] = recorded['verdict']
                mod.judge = original_judge
        except Exception as exc:
            trace['exception'] = type(exc).__name__ + ': ' + str(exc)
    trace.update({
        'clauses': len(search.clauses),
        'rounds': search.rounds,
        'superpositions': search.superpositions,
        'reductions': search.reductions,
    })
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(trace, indent=2, sort_keys=True) + '\n')
    print('RETRY_GATE_TRACE ' + json.dumps(trace, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()

# trigger: retry-gate-trace-v3

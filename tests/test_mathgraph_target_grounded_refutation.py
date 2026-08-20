import importlib.util
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load_solver():
    path = ROOT / "submissions/mathgraph/solver.py"
    spec = importlib.util.spec_from_file_location(
        "mathgraph_target_grounded_test_solver", path
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def limits(solver, seconds):
    result = dict(solver.COMPACT_SUPERPOSITION_PROBE)
    result.update({
        "seconds": seconds,
        "maximum_term_size": 45,
        "maximum_replay_term_size": 160,
        "maximum_depth": 10,
        "maximum_rules": 192,
        "maximum_rounds": 16,
        "new_clauses_per_round": 128,
        "maximum_clauses": 2000,
        "normalization_steps": 96,
        "maximum_proof_nodes": 20000,
    })
    return result


def test_target_grounding_produces_replayable_external_proof():
    solver = load_solver()
    source = solver.parse_equation(
        "x = (y * (x * ((z * x) * z))) * z"
    )
    target = solver.parse_equation(
        "x = ((y * x) * (y * (y * z))) * x"
    )
    engine = solver.TargetGroundedRefutation(
        source, target, time.monotonic() + 0.5, limits(solver, 0.5)
    )
    found = engine.solve()
    assert found is not None
    nodes, root = found
    assert (nodes[root].lhs, nodes[root].rhs) == target[:2]
    assert solver.replay_dag(
        source, nodes, root, maximum_term_size=160, maximum_nodes=20000
    )


def test_target_grounding_abstains_on_false_control():
    solver = load_solver()
    source = solver.parse_equation(
        "x = (y * ((y * z) * z)) * (x * z)"
    )
    target = solver.parse_equation(
        "x = y * (x * ((z * w) * (z * z)))"
    )
    engine = solver.TargetGroundedRefutation(
        source, target, time.monotonic() + 0.1, limits(solver, 0.1)
    )
    assert engine.solve() is None

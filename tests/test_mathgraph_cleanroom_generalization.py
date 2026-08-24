import hashlib
import importlib.util
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOLVER_PATH = ROOT / "submissions/mathgraph_cleanroom/solver.py"


def load_solver():
    spec = importlib.util.spec_from_file_location(
        "mathgraph_cleanroom_generalization_solver", SOLVER_PATH
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def given_clause_limits(solver, seconds=3.0):
    limits = dict(solver.COMPACT_SUPERPOSITION_PROBE)
    limits.update({
        "seconds": seconds,
        "maximum_term_size": 65,
        "maximum_replay_term_size": 260,
        "maximum_depth": 12,
        "maximum_rules": 768,
        "maximum_rounds": 64,
        "new_clauses_per_round": 512,
        "maximum_clauses": 12000,
        "normalization_steps": 256,
        "maximum_proof_nodes": 50000,
    })
    return limits


def test_given_clause_route_closes_hard_case_with_replay():
    solver = load_solver()
    source = solver.parse_equation(
        "x = (y * x) * ((x * z) * z)"
    )
    target = solver.parse_equation(
        "x = (y * (z * (y * z))) * z"
    )
    engine = solver.TargetGroundedRefutation(
        source,
        target,
        time.monotonic() + 3.0,
        given_clause_limits(solver),
    )
    found = engine.solve_given_clause()
    assert found is not None
    nodes, root = found
    assert (nodes[root].lhs, nodes[root].rhs) == target[:2]
    assert solver.replay_dag(
        source, nodes, root, maximum_term_size=260, maximum_nodes=50000
    )
    code, _ = solver.make_dag_certificate(target, nodes, root)
    assert len(code.encode("utf-8")) > 100000
    compact = solver.compact_lean_have_bindings(code)
    assert len(compact.encode("utf-8")) < 100000
    assert "sorry" not in compact
    assert not any(
        line.lstrip().startswith("have ") and line.rstrip().endswith(" := rfl")
        and " : " not in line
        for line in compact.splitlines()
    )


def test_affine_family_is_generated_and_independently_replayed():
    solver = load_solver()
    source = solver.parse_equation("x * y = x")
    target = solver.parse_equation("x * y = y")
    found = solver.generated_affine_model_candidate(source, target)
    assert found is not None
    _, order, table, witness, parameters = found
    assert len(table) == order * order
    assert len(parameters) == 3
    assert solver.replay_countermodel(
        source,
        target,
        table,
        order,
        witness,
        solver.serialize_flat_table(table, order),
    )


def test_affine_family_abstains_when_target_is_forced():
    solver = load_solver()
    equation = solver.parse_equation("(x * y) * z = x * (y * z)")
    assert solver.generated_affine_model_candidate(equation, equation) is None


def test_diagonal_fiber_constructor_is_jointly_alpha_invariant():
    solver = load_solver()
    source = solver.parse_equation(
        "a = ((a * b) * (a * c)) * b"
    )
    target = solver.parse_equation(
        "a = ((a * b) * b) * (a * c)"
    )
    code = solver.diagonal_fiber_certificate(source, target)
    assert code is not None
    assert len(code.encode("utf-8")) == 1911
    assert hashlib.sha256(code.encode("utf-8")).hexdigest() == (
        "af4d0e6f1f82be8548aa44debc11761eb96b8964668a5ecbc0e799f44526f6d6"
    )


def test_diagonal_fiber_constructor_fails_closed_on_shape_change():
    solver = load_solver()
    source = solver.parse_equation(
        "a = ((a * b) * (a * c)) * b"
    )
    target = solver.parse_equation(
        "a = ((a * c) * b) * (a * b)"
    )
    assert solver.diagonal_fiber_certificate(source, target) is None

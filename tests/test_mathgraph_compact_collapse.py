import importlib.util
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load_solver():
    path = ROOT / "submissions/mathgraph/solver.py"
    spec = importlib.util.spec_from_file_location(
        "mathgraph_compact_collapse_test_solver", path
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_derived_bare_variable_clause_closes_arbitrary_target():
    solver = load_solver()
    source = solver.parse_equation(
        "x = (y ◇ z) ◇ (w ◇ (x ◇ y))"
    )
    target = solver.parse_equation(
        "x = (y ◇ z) ◇ ((w ◇ w) ◇ y)"
    )
    limits = dict(solver.COMPACT_SUPERPOSITION_PROBE)
    search = solver.CompactSuperposition(
        solver, source, target, time.monotonic() + 1.0, limits
    )
    recipe = search.solve()
    assert recipe is not None
    nodes, root = search.compile(recipe)
    assert (nodes[root].lhs, nodes[root].rhs) == target[:2]
    assert solver.replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=limits["maximum_replay_term_size"],
        maximum_nodes=limits["maximum_proof_nodes"],
    )


def test_collapse_replay_allows_large_specialized_proof_terms():
    solver = load_solver()
    source = solver.parse_equation(
        "x = ((x ◇ y) ◇ y) ◇ (x ◇ y)"
    )
    target = solver.parse_equation(
        "x ◇ x = x ◇ (x ◇ x)"
    )
    limits = dict(solver.COMPACT_SUPERPOSITION_PROBE)
    search = solver.CompactSuperposition(
        solver, source, target, time.monotonic() + 1.0, limits
    )
    recipe = search.solve()
    assert recipe is not None
    nodes, root = search.compile(recipe)
    assert (nodes[root].lhs, nodes[root].rhs) == target[:2]
    assert max(
        max(solver.term_size(node.lhs), solver.term_size(node.rhs))
        for node in nodes
    ) > limits["maximum_term_size"]
    assert solver.replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=limits["maximum_replay_term_size"],
        maximum_nodes=limits["maximum_proof_nodes"],
    )


def test_nonorientable_equalities_remain_available_for_superposition():
    solver = load_solver()
    source = solver.parse_equation(
        "x ◇ (y ◇ z) = (w ◇ x) ◇ u"
    )
    target = solver.parse_equation(
        "x ◇ (y ◇ z) = (w ◇ y) ◇ u"
    )
    limits = dict(solver.COMPACT_SUPERPOSITION_PROBE)
    search = solver.CompactSuperposition(
        solver, source, target, time.monotonic() + 1.0, limits
    )
    recipe = search.solve()
    assert recipe is not None
    nodes, root = search.compile(recipe)
    assert (nodes[root].lhs, nodes[root].rhs) == target[:2]
    assert solver.replay_dag(
        source,
        nodes,
        root,
        maximum_term_size=limits["maximum_replay_term_size"],
        maximum_nodes=limits["maximum_proof_nodes"],
    )

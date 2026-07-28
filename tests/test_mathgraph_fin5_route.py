import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load_solver():
    path = ROOT / "submissions/mathgraph/solver.py"
    spec = importlib.util.spec_from_file_location(
        "mathgraph_fin5_test_solver", path
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_generic_fin5_replay_and_certificate():
    solver = load_solver()
    source = solver.parse_equation(
        "x = (y ◇ (z ◇ (x ◇ y))) ◇ z"
    )
    target = solver.parse_equation(
        "x = x ◇ (((y ◇ y) ◇ x) ◇ x)"
    )
    table = (
        2, 1, 3, 4, 0,
        1, 4, 0, 3, 2,
        3, 0, 1, 2, 4,
        4, 3, 2, 0, 1,
        0, 2, 4, 1, 3,
    )
    engine = solver.FiniteModelEngine(
        5, source, target, float("inf"), 1, 1
    )
    assert engine.replay(table, (0, 1))
    certificate = engine.emit_certificate(table)
    assert "Fin 5" in certificate
    assert len(certificate.encode("utf-8")) < 1000

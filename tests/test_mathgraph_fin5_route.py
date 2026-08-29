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


def test_structured_templates_cover_crossed_coordinate_families():
    solver = load_solver()
    examples = (
        (
            "x = (y * x) * (x * (z * w))",
            "x * (y * z) = x * (z * y)",
            "crossed-square-2",
            4,
        ),
        (
            "x = ((y * y) * x) * (x * z)",
            "x * (x * y) = (x * y) * x",
            "crossed-square-2",
            4,
        ),
        (
            "x = (y * x) * (x * z)",
            "x * y = x * ((z * y) * w)",
            "crossed-square-3-perturbed",
            9,
        ),
    )
    for source_text, target_text, name, order in examples:
        source = solver.parse_equation(source_text)
        target = solver.parse_equation(target_text)
        found = solver.structured_model_candidate(source, target)
        assert found is not None
        assert found[:2] == (name, order)
        _, _, table, witness = found
        assert solver.replay_countermodel(
            source,
            target,
            table,
            order,
            witness,
            solver.serialize_flat_table(table, order),
        )


def test_large_structured_certificate_raises_recursion_bound():
    solver = load_solver()
    _, order, table = solver.STRUCTURED_MODEL_TEMPLATES[1]
    certificate = solver.emit_fin_certificate(table, order)
    assert "set_option maxRecDepth 100000 in" in certificate

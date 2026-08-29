import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOLVER = ROOT / "submissions" / "mathgraph" / "solver.py"


def load_solver():
    spec = importlib.util.spec_from_file_location("mathgraph_stair_test", SOLVER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_external_paramodulation_has_independent_replay():
    solver = load_solver()
    problem = {
        "id": "equation_only_control",
        "equation1": "x = y * ((x * ((z * y) * x)) * y)",
        "equation2": "x = ((y * (z * (w * z))) * w) * z",
    }
    found = solver.external_paramodulation_candidate(problem, 2.0)
    assert found is not None
    code, result = found
    assert result["plan_ok"] is True
    assert result["total_steps"] == 11
    assert "def submission : Goal" in code


def test_external_model_bank_is_equation_driven_and_replayed():
    solver = load_solver()
    source = solver.parse_equation(
        "x = y * (y * (z * (w * (x * x))))"
    )
    target = solver.parse_equation(
        "x = x * ((y * z) * (w * (y * x)))"
    )
    found = solver.structured_model_candidate(source, target)
    assert found is not None
    name, order, table, witness = found
    assert name == "affine-right-offset-5"
    assert order == 5
    assert solver.replay_countermodel(
        source,
        target,
        table,
        order,
        witness,
        solver.serialize_flat_table(table, order),
    )

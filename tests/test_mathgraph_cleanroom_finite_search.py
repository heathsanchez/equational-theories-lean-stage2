import importlib.util
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load_solver():
    path = ROOT / "submissions/mathgraph_cleanroom/solver.py"
    spec = importlib.util.spec_from_file_location(
        "mathgraph_cleanroom_finite_test_solver", path
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_local_table_repair_replays_before_certificate_emission():
    solver = load_solver()
    source = solver.parse_equation("x ◇ y = x")
    target = solver.parse_equation("x ◇ y = y")
    engine, found, metrics = solver.search_finite_model_local(
        source,
        target,
        5,
        time.monotonic() + 2.0,
        seed=12345,
    )
    assert found is not None
    table, witness = found
    assert len(table) == 25
    assert engine.replay(table, witness)
    assert "Fin 5" in engine.emit_certificate(table)
    assert metrics["steps"] > 0


def test_local_table_repair_is_seed_deterministic():
    solver = load_solver()
    source = solver.parse_equation("x ◇ x = x")
    target = solver.parse_equation(
        "(x ◇ y) ◇ z = x ◇ (y ◇ z)"
    )
    results = []
    for _ in range(2):
        engine, found, metrics = solver.search_finite_model_local(
            source,
            target,
            5,
            time.monotonic() + 2.0,
            seed=67890,
        )
        assert found is not None
        assert engine.replay(*found)
        results.append((found, metrics))
    assert results[0] == results[1]


def test_diverse_csp_configuration_changes_only_search_order():
    solver = load_solver()
    configuration = solver.FINITE_MODEL_DIVERSITY
    assert configuration["domain_size"] == 4
    assert not configuration["options"]["symmetry_enabled"]
    assert not configuration["options"]["support_branching"]
    assert configuration["options"]["support_propagation"]
    assert configuration["options"]["incremental_propagation"]


def test_submission_contains_no_external_specialist_payload_markers():
    text = (ROOT / "submissions/mathgraph_cleanroom/solver.py").read_text()
    forbidden = (
        "EXTERNAL_STAIR",
        "_STAIR_ENGINE_PAYLOAD",
        "external_paramodulation_candidate",
        "stair-bank-",
        "huggingface.co",
        "sair-distillation",
    )
    assert not any(marker in text for marker in forbidden)

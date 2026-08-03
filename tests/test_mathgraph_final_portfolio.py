import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FROZEN = ROOT / "submissions" / "mathgraph" / "solver.py"
BASE = ROOT / "submissions" / "mathgraph_cleanroom" / "solver.py"
PORTFOLIO = {
    "solo_gemma": ROOT / "submissions" / "mathgraph_cleanroom_solo_gemma" / "solver.py",
    "solo_oss": ROOT / "submissions" / "mathgraph_cleanroom_solo_oss" / "solver.py",
    "marathon_gemma": ROOT / "submissions" / "mathgraph_cleanroom_marathon_gemma" / "solver.py",
    "marathon_oss": ROOT / "submissions" / "mathgraph_cleanroom_marathon_oss" / "solver.py",
}

FORBIDDEN_PROVENANCE_MARKERS = (
    "EXTERNAL_STAIR", "_STAIR_ENGINE_PAYLOAD", "external_paramodulation_candidate",
    "stair-bank-", "huggingface.co", "sair-distillation",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_solver(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_frozen_production_solver_is_unchanged():
    assert FROZEN.stat().st_size == 313_240
    assert digest(FROZEN) == "fc402fae046096d99a8c01a6848bc4030d282c7f4a90ff5e9c26c3c8d8833fe1"


def test_each_portfolio_entry_is_a_single_file_under_the_intake_cap():
    for solver in PORTFOLIO.values():
        assert solver.parent.exists()
        assert list(solver.parent.iterdir()) == [solver]
        assert 0 < solver.stat().st_size < 500_000
        compile(solver.read_text(encoding="utf-8"), str(solver), "exec")


def test_cleanroom_core_and_portfolio_have_no_external_provenance_markers():
    for path in [BASE, *PORTFOLIO.values()]:
        text = path.read_text(encoding="utf-8")
        for marker in FORBIDDEN_PROVENANCE_MARKERS:
            assert marker not in text


def test_track_and_model_roles_are_explicit_and_credentials_are_absent():
    texts = {name: path.read_text(encoding="utf-8") for name, path in PORTFOLIO.items()}

    assert "PROMPT =" in texts["solo_gemma"]
    assert "PROMPT =" in texts["solo_oss"]
    assert "JUDGE_MARATHON_MANIFEST" in texts["marathon_gemma"]
    assert "JUDGE_MARATHON_MANIFEST" in texts["marathon_oss"]
    assert "from marathon_llm import call_llm" not in texts["marathon_gemma"]
    assert "from marathon_llm import call_llm" in texts["marathon_oss"]
    assert '"max_output_tokens": 60000' in texts["marathon_oss"]
    assert '"reasoning_effort": "medium"' in texts["marathon_oss"]

    for text in texts.values():
        assert "sk-or-v1-" not in text
        assert "OPENROUTER_API_KEY=" not in text


def test_model_output_parsers_fail_closed():
    gemma = load_solver(PORTFOLIO["solo_gemma"], "cleanroom_solo_gemma")
    oss = load_solver(PORTFOLIO["solo_oss"], "cleanroom_solo_oss")

    assert gemma.extract_llm_proof('{"proof":"intro x\\nexact h x x"}')
    assert gemma.extract_llm_proof('{"proof":"sorry"}') is None
    assert gemma.extract_llm_proof('{"proof":"import Mathlib"}') is None
    assert oss.extract_llm_certificate(
        '{"verdict":"true","code":"import JudgeProblem\\n\\n'
        'def submission : Goal := by\\n  intro G _ h\\n  exact h"}'
    )
    assert oss.extract_llm_certificate(
        '{"verdict":"true","code":"def submission : Goal := by sorry"}'
    ) is None

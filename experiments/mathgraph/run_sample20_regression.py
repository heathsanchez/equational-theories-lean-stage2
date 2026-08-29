#!/usr/bin/env python3
"""Run isolated MathGraph regressions and enforce the frozen 162/200 floor."""

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / "submissions" / "mathgraph"
PROBLEMS = ROOT / "examples" / "problems"
RESULTS = ROOT / "experiments" / "mathgraph" / "results"
BASELINES = {
    "sample_20": RESULTS / "fin3_final" / "sample_20.json",
    "sample_200": RESULTS / "fin3_final" / "sample_200.json",
}
EXPECTED_HASHES = {
    "sample_20": "861af3ef20cd2363606b7d75f84aa39dfbf8f56fbf37808eb887dccbe2f3d4f3",
    "sample_200": "1f195aabbb01a884a3c6a6670c804a66580e6428c78bd0d4665b28e7a57f73f6",
    "source_reentry_proxy": "87c15430ae7293e6da65b51234754adb27e30575f1c8583b14cc4741d0f195b9",
    "equality_chain_proxy": "987f7cf71c938d8831337edc6ee8d0d2e8788fa241eb74eb58457cc1f6f6800d",
    "contextual_proxy": "c06d2692ddba7aa0bc3f13fbc926cffb2b0457314ed6df65eeb16c4cbfe7d0dd",
    "finite_model_proxy": "8bf13e4a7d10b098bedb880837018e8261dfc28c63d1327a12b0ea150e1addca",
    "development": "8df0acc3383ea5080dc144127aa95254854204b2ea044d0289dd9896e7095fd4",
    "holdout": "b70927d14da452636db269ffc8109c1f8ccf7934fef8290623ab9887fc25f045",
    "generic_engine_summary": "ae4e4f54fde13da1c2e12077b64891ba102cb28c372666c154fb3cbf0352f8d9",
}
HASHED_ARTIFACTS = {
    **BASELINES,
    "source_reentry_proxy": RESULTS / "source_reentry_proxy.json",
    "equality_chain_proxy": RESULTS / "equality_chain_source_reentry.json",
    "contextual_proxy": RESULTS / "contextual_overlap_proxy.json",
    "finite_model_proxy": RESULTS / "fin3_proxy.json",
    "development": RESULTS / "fin3_development_frozen" / "sample_200_development.json",
    "holdout": RESULTS / "fin3_frozen" / "sample_200_holdout.json",
    "generic_engine_summary": RESULTS / "finite_model_refactor_summary.json",
}
FROZEN_SOLVER = (
    ROOT / "experiments" / "mathgraph" / "regressions" / "solver_fb671c7.py"
)
FROZEN_SOLVER_SHA256 = (
    "c88b9d78daabde4ab099dffef807a8d5aaac803b5b883275a3b4a0cfd6a31816"
)
NORMALIZATION_BASELINE = RESULTS / "normalization_baseline_manifest.json"
NORMALIZATION_BASELINE_SHA256 = (
    "f3a87079fe15ae167ce52dc2f07589b357be8f803742f0118b387836487a07f2"
)
BRIDGE_FROZEN_SOLVER = (
    ROOT / "experiments" / "mathgraph" / "regressions"
    / "solver_f9430e5.py"
)
BRIDGE_FROZEN_SOLVER_SHA256 = (
    "b096ebef09a5cc11de9ad22f37a196111d29979beb8f759463643bba44f6b231"
)


def content_digest(problem):
    payload = (
        problem["equation1"].strip() + "\0" + problem["equation2"].strip()
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def content_hash_split(problems):
    """Return exact deterministic halves using equation text only."""
    ordered = sorted(problems, key=lambda row: (content_digest(row), row["equation1"], row["equation2"]))
    midpoint = len(ordered) // 2
    return ordered[:midpoint], ordered[midpoint:]


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def verify_baseline(name):
    path = HASHED_ARTIFACTS[name]
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    assert digest == EXPECTED_HASHES[name], (
        f"{name} authoritative baseline hash changed: {digest}"
    )
    return load_json(path)


def verify_all_frozen_hashes():
    for name in EXPECTED_HASHES:
        verify_baseline(name)
    assert hashlib.sha256(FROZEN_SOLVER.read_bytes()).hexdigest() == (
        FROZEN_SOLVER_SHA256
    ), "frozen fb671c7 solver changed"
    assert hashlib.sha256(NORMALIZATION_BASELINE.read_bytes()).hexdigest() == (
        NORMALIZATION_BASELINE_SHA256
    ), "frozen 162/200 normalization baseline changed"
    assert hashlib.sha256(BRIDGE_FROZEN_SOLVER.read_bytes()).hexdigest() == (
        BRIDGE_FROZEN_SOLVER_SHA256
    ), "frozen f9430e5 BridgeIR baseline solver changed"


def rejected_categories(rows):
    categories = {}
    for row in rows:
        for event in row.get("log", []):
            if event.get("type") != "judge":
                continue
            status = event.get("response", {}).get("status", "unparsed")
            if status != "accepted":
                categories[status] = categories.get(status, 0) + 1
    return categories


def validate_rows(name, rows, problems, baseline_rows):
    expected_ids = {row["id"] for row in problems}
    actual_ids = [row.get("id") for row in rows]
    assert len(rows) == len(problems), (
        f"result contamination: expected {len(problems)} rows, got {len(rows)}"
    )
    assert set(actual_ids) == expected_ids, f"{name}: result IDs do not match"
    assert len(actual_ids) == len(set(actual_ids)), f"{name}: duplicate result IDs"
    by_id = {row["id"]: row for row in rows}
    baseline_by_id = {
        row["id"]: row
        for row in baseline_rows
        if row["id"] in expected_ids and row.get("solved")
    }
    for problem_id, frozen in baseline_by_id.items():
        current = by_id[problem_id]
        assert current.get("solved"), f"{name}: lost frozen win {problem_id}"
        assert current.get("verdict") == frozen.get("verdict"), (
            f"{name}: changed frozen verdict {problem_id}"
        )
    normalization_floor = load_json(NORMALIZATION_BASELINE)
    exact_floor = normalization_floor[
        "sample_20_accepted" if name == "sample_20"
        else "sample_200_accepted"
    ]
    for problem_id, verdict in exact_floor.items():
        if problem_id not in expected_ids:
            continue
        current = by_id[problem_id]
        assert current.get("solved"), (
            f"{name}: lost frozen 162-floor win {problem_id}"
        )
        assert current.get("verdict") == verdict, (
            f"{name}: changed frozen 162-floor verdict {problem_id}"
        )

    accepted_true = sum(
        row.get("solved") and row.get("verdict") == "true" for row in rows
    )
    accepted_false = sum(
        row.get("solved") and row.get("verdict") == "false" for row in rows
    )
    frozen_true = sum(
        verdict == "true"
        for problem_id, verdict in exact_floor.items()
        if problem_id in expected_ids
    )
    frozen_false = sum(
        verdict == "false"
        for problem_id, verdict in exact_floor.items()
        if problem_id in expected_ids
    )
    assert accepted_true >= frozen_true, (
        f"{name}: TRUE floor {frozen_true}, got {accepted_true}"
    )
    assert accepted_false >= frozen_false, (
        f"{name}: FALSE floor {frozen_false}, got {accepted_false}"
    )
    assert not rejected_categories(rows), (
        f"{name}: rejected judge calls {rejected_categories(rows)}"
    )
    assert all(row.get("llm_calls", 0) == 0 for row in rows), (
        f"{name}: unexpected LLM call"
    )
    return accepted_true, accepted_false


def run_isolated(name, problems, baseline_rows, destination=None):
    with tempfile.TemporaryDirectory(prefix=f"mathgraph-{name}-") as tmp:
        tmp_path = Path(tmp)
        problem_path = tmp_path / f"{name}.json"
        output_path = tmp_path / f"{name}-results.json"
        problem_path.write_text(
            json.dumps(problems, indent=2, ensure_ascii=False), encoding="utf-8"
        )
        command = [
            sys.executable,
            "-m",
            "pipeline.runner",
            "--submission",
            str(SOLVER),
            "--problems",
            str(problem_path),
            "--output",
            str(output_path),
        ]
        subprocess.run(command, cwd=ROOT, check=True)
        rows = load_json(output_path)
        counts = validate_rows(name, rows, problems, baseline_rows)
        if destination is not None:
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(output_path, destination)
    print(
        f"{name} regression: {counts[0]} accepted TRUE, "
        f"{counts[1]} accepted FALSE, zero rejected judge calls"
    )
    return rows, counts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--benchmark",
        choices=("sample20", "sample200", "development", "holdout", "split", "all"),
        default="sample20",
    )
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--official-harnesses", action="store_true")
    args = parser.parse_args()

    verify_all_frozen_hashes()
    baseline20 = load_json(BASELINES["sample_20"])
    baseline200 = load_json(BASELINES["sample_200"])
    sample20 = load_json(PROBLEMS / "sample_20.json")
    sample200 = load_json(PROBLEMS / "sample_200.json")

    def destination(name):
        return args.output_dir / f"{name}.json" if args.output_dir else None

    if args.benchmark in ("sample20", "all"):
        run_isolated("sample_20", sample20, baseline20, destination("sample_20"))
    if args.benchmark in ("sample200", "all"):
        run_isolated(
            "sample_200", sample200, baseline200, destination("sample_200")
        )
    if args.benchmark in ("development", "holdout", "split", "all"):
        development, holdout = content_hash_split(sample200)
    if args.benchmark in ("development", "split", "all"):
        run_isolated(
            "sample_200_development",
            development,
            baseline200,
            destination("sample_200_development"),
        )
    if args.benchmark in ("holdout", "split", "all"):
        run_isolated(
            "sample_200_holdout",
            holdout,
            baseline200,
            destination("sample_200_holdout"),
        )
    if args.official_harnesses:
        subprocess.run([sys.executable, "scripts/run_harness.py"], cwd=ROOT, check=True)
        subprocess.run(
            [sys.executable, "scripts/run_marathon_harness.py"],
            cwd=ROOT,
            check=True,
        )


if __name__ == "__main__":
    main()

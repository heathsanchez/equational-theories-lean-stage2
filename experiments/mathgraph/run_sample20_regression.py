#!/usr/bin/env python3
"""Run isolated MathGraph regressions and enforce the frozen 65270e7 floor."""

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
    "sample_20": RESULTS / "contextual_final" / "sample_20.json",
    "sample_200": RESULTS / "contextual_final" / "sample_200.json",
}
EXPECTED_HASHES = {
    "sample_20": "ef6ea116b1bab964274fee1f205e3bf27c770f6d91c65aac9574d493aaf85e6d",
    "sample_200": "c4efdcca30a9a12ad4a76a26641e3790e44cb8503024c7c762e8ccccf55d8857",
    "source_reentry_proxy": "87c15430ae7293e6da65b51234754adb27e30575f1c8583b14cc4741d0f195b9",
    "equality_chain_proxy": "987f7cf71c938d8831337edc6ee8d0d2e8788fa241eb74eb58457cc1f6f6800d",
    "contextual_proxy": "c06d2692ddba7aa0bc3f13fbc926cffb2b0457314ed6df65eeb16c4cbfe7d0dd",
}
HASHED_ARTIFACTS = {
    **BASELINES,
    "source_reentry_proxy": RESULTS / "source_reentry_proxy.json",
    "equality_chain_proxy": RESULTS / "equality_chain_source_reentry.json",
    "contextual_proxy": RESULTS / "contextual_overlap_proxy.json",
}


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

    accepted_true = sum(
        row.get("solved") and row.get("verdict") == "true" for row in rows
    )
    accepted_false = sum(
        row.get("solved") and row.get("verdict") == "false" for row in rows
    )
    frozen_true = sum(row.get("verdict") == "true" for row in baseline_by_id.values())
    frozen_false = sum(row.get("verdict") == "false" for row in baseline_by_id.values())
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

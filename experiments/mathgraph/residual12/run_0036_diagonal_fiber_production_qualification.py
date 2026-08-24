#!/usr/bin/env python3
"""Run the frozen production qualification for the diagonal-fiber constructor."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
import time
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT))
PREREG = HERE / "0036_diagonal_fiber_production_preregistration.json"
SOLVER = ROOT / "submissions/mathgraph_cleanroom/solver.py"
SIX = ROOT / "colab/data/six_residuals.json"
EXPECTED_PREREG_SHA256 = (
    "4100662b040d58e75a5d405ad7be0c76a40e326d3a07c3bdcb5b346c89d5d00a"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_solver():
    spec = importlib.util.spec_from_file_location(
        "mathgraph_diagonal_fiber_production_solver", SOLVER
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def validate_frozen(protocol):
    parents = []
    for parent in protocol["authoritative_parents"]:
        path = ROOT / parent["evidence_path"]
        manifest = json.loads(path.read_text(encoding="utf-8"))
        parents.append(all((
            manifest.get("workflow_run") == parent["workflow_run"],
            manifest.get("conclusion") == "success",
            manifest.get("result_summary", {}).get("decision")
            == parent["required_decision"],
            manifest.get("result_summary", {}).get("measurement_ok") is True,
            manifest.get("result_summary", {}).get("official_enabled") is True,
        )))
    frozen = protocol["frozen_inputs"]
    return all((
        protocol["status"] == "FROZEN_BEFORE_PRODUCTION_EXECUTABLE_PUBLICATION",
        sha256(PREREG) == EXPECTED_PREREG_SHA256,
        sha256(SIX) == frozen["six_residual_input_sha256"],
        sha256(ROOT / "lean-toolchain") == frozen["lean_toolchain_sha256"],
        sha256(ROOT / "lake-manifest.json") == frozen["lake_manifest_sha256"],
        all(parents),
    ))


def solver_config():
    from pipeline.proxy import load_config

    config = load_config()
    config["solver"]["timeout_seconds"] = 120
    config["judge"]["lean_timeout_seconds"] = 90
    config["sandbox"]["mode"] = "none"
    return config


def run_row(raw, configuration, solver_module, config):
    from pipeline.proxy import run_solver

    problem = {
        key: value for key, value in raw.items()
        if key not in {"truth", "label", "is_true", "answer"}
    }
    source = solver_module.parse_equation(problem["equation1"])
    target = solver_module.parse_equation(problem["equation2"])
    structural_match = (
        solver_module.diagonal_fiber_certificate(source, target) is not None
    )
    result = run_solver(ROOT / "submissions/mathgraph_cleanroom", problem, config)
    return {
        "configuration": configuration,
        "id": raw.get("id"),
        "solved": bool(result.get("solved")),
        "verdict": result.get("verdict"),
        "judge_calls": result.get("judge_calls", 0),
        "llm_calls": result.get("llm_calls", 0),
        "diagonal_fiber_schema_match": structural_match,
        "last_log": (result.get("log") or [None])[-1],
    }


def focused(protocol, solver_module, config):
    qualification = protocol["qualification"]["focused_official_lean"]
    required = set(qualification["required_existing_ids"])
    required.add(qualification["required_new_id"])
    rows = json.loads(SIX.read_text(encoding="utf-8"))
    selected = [row for row in rows if row.get("id") in required]
    results = [run_row(row, "six_residuals", solver_module, config) for row in selected]
    solved = {row["id"] for row in results if row["solved"]}
    matches = [row["id"] for row in results if row["diagonal_fiber_schema_match"]]
    certificate = solver_module.DIAGONAL_FIBER_CERTIFICATE.encode("utf-8")
    certificate_sha256 = hashlib.sha256(certificate).hexdigest()
    ok = all((
        len(results) == len(required),
        solved == required,
        matches == [qualification["required_new_id"]],
        sum(row["llm_calls"] for row in results)
        == qualification["required_llm_calls"],
        certificate_sha256 == qualification["required_new_certificate_sha256"],
        len(certificate)
        == protocol["constructor_constraints"]["expected_certificate_bytes"],
    ))
    return {
        "schema": "mathgraph.0036-diagonal-fiber-production-focused.v1",
        "decision": (
            "DIAGONAL_FIBER_PRODUCTION_FOCUSED_PASSED"
            if ok else "DIAGONAL_FIBER_PRODUCTION_FAILURE"
        ),
        "focused_ok": ok,
        "total": len(results),
        "solved": len(solved),
        "required_ids": sorted(required),
        "missing_required": sorted(required - solved),
        "schema_match_ids": matches,
        "llm_calls": sum(row["llm_calls"] for row in results),
        "certificate_bytes": len(certificate),
        "certificate_sha256": certificate_sha256,
        "rows": results,
    }


def full(protocol, solver_module, config):
    from datasets import load_dataset

    qualification = protocol["qualification"]["released_800_official_audit"]
    rows = []
    for configuration in protocol["frozen_inputs"]["configurations"]:
        dataset = load_dataset(
            protocol["frozen_inputs"]["released_dataset"],
            configuration,
            split="train",
        )
        if len(dataset) != protocol["frozen_inputs"]["rows_per_configuration"]:
            raise RuntimeError("released dataset row count changed")
        for raw in dataset:
            row = run_row(dict(raw), configuration, solver_module, config)
            rows.append(row)
            print(json.dumps(row, sort_keys=True), flush=True)
    solved = [row for row in rows if row["solved"]]
    solved_ids = {row["id"] for row in solved}
    matches = [row["id"] for row in rows if row["diagonal_fiber_schema_match"]]
    llm_calls = sum(row["llm_calls"] for row in rows)
    ok = all((
        len(rows) == qualification["required_total"],
        len(solved) >= qualification["minimum_solved"],
        qualification["required_id"] in solved_ids,
        len(matches) == qualification["required_schema_match_count"],
        matches == [qualification["required_id"]],
        llm_calls == qualification["required_llm_calls"],
    ))
    return {
        "schema": "mathgraph.0036-diagonal-fiber-production-800.v1",
        "decision": (
            "DIAGONAL_FIBER_PRODUCTION_PROMOTED"
            if ok else "DIAGONAL_FIBER_FOCUSED_ONLY"
        ),
        "production_ok": ok,
        "total": len(rows),
        "solved": len(solved),
        "unsolved_count": len(rows) - len(solved),
        "unsolved_ids": [row["id"] for row in rows if not row["solved"]],
        "required_id_solved": qualification["required_id"] in solved_ids,
        "schema_match_count": len(matches),
        "schema_match_ids": matches,
        "verdict_counts": dict(Counter(row["verdict"] for row in solved)),
        "judge_calls": sum(row["judge_calls"] for row in rows),
        "llm_calls": llm_calls,
        "rows": rows,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("focused", "full"), required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    protocol = json.loads(PREREG.read_text(encoding="utf-8"))
    measurement_ok = validate_frozen(protocol)
    started = time.monotonic()
    solver_module = load_solver()
    config = solver_config()
    result = (
        focused(protocol, solver_module, config)
        if args.mode == "focused"
        else full(protocol, solver_module, config)
    )
    result.update({
        "measurement_ok": measurement_ok,
        "official_enabled": True,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    })
    if not measurement_ok:
        result["decision"] = "MEASUREMENT_FAILURE"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        key: result.get(key) for key in (
            "decision", "measurement_ok", "total", "solved",
            "required_id_solved", "schema_match_ids", "llm_calls",
            "elapsed_seconds",
        )
    }, indent=2, sort_keys=True), flush=True)
    expected = (
        "DIAGONAL_FIBER_PRODUCTION_FOCUSED_PASSED"
        if args.mode == "focused"
        else "DIAGONAL_FIBER_PRODUCTION_PROMOTED"
    )
    if result["decision"] != expected:
        raise SystemExit(result["decision"])


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Test the generic diagonal-fiber constructor selected by CN1 ancestry."""

from __future__ import annotations

import argparse
import ast
import hashlib
import importlib.util
import json
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
PREREG = HERE / "0036_diagonal_fiber_constructor_preregistration.json"
INPUT = HERE / "released_residuals_unlabelled.json"
PARENT = HERE / "evidence/0036_cn1_work_frontier_run_32693370694.json"
DEFAULT_OUTPUT_DIR = HERE / "0036_diagonal_fiber_constructor_artifacts"
EXPECTED_PREREG_SHA256 = (
    "344b192c53e42fe362f2f5cce6797e8f7752eeaa2328992a786bedf3b0b67a23"
)


CERTIFICATE = """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have lem1 : ∀ (p : G) (q : G) (r : G), ((p ◇ q) ◇ (p ◇ r)) = ((p ◇ p) ◇ q) := by
    intro p q r
    calc ((p ◇ q) ◇ (p ◇ r))
      _ = (((((p ◇ q) ◇ (p ◇ r)) ◇ q) ◇ (((p ◇ q) ◇ (p ◇ r)) ◇ q)) ◇ q) := h ((p ◇ q) ◇ (p ◇ r)) q q
      _ = ((p ◇ (((p ◇ q) ◇ (p ◇ r)) ◇ q)) ◇ q) := congrArg (· ◇ q) (congrArg (· ◇ (((p ◇ q) ◇ (p ◇ r)) ◇ q)) ((h p q r).symm))
      _ = ((p ◇ p) ◇ q) := congrArg (· ◇ q) (congrArg (p ◇ ·) ((h p q r).symm))
  have lem2 : ∀ (p : G) (q : G) (r : G), (((p ◇ q) ◇ q) ◇ ((p ◇ q) ◇ r)) = p := by
    intro p q r
    calc (((p ◇ q) ◇ q) ◇ ((p ◇ q) ◇ r))
      _ = ((((((p ◇ q) ◇ q) ◇ ((p ◇ q) ◇ r)) ◇ q) ◇ ((((p ◇ q) ◇ q) ◇ ((p ◇ q) ◇ r)) ◇ q)) ◇ q) := h (((p ◇ q) ◇ q) ◇ ((p ◇ q) ◇ r)) q q
      _ = (((p ◇ q) ◇ ((((p ◇ q) ◇ q) ◇ ((p ◇ q) ◇ r)) ◇ q)) ◇ q) := congrArg (· ◇ q) (congrArg (· ◇ ((((p ◇ q) ◇ q) ◇ ((p ◇ q) ◇ r)) ◇ q)) ((h (p ◇ q) q r).symm))
      _ = (((p ◇ q) ◇ (p ◇ q)) ◇ q) := congrArg (· ◇ q) (congrArg ((p ◇ q) ◇ ·) ((h (p ◇ q) q r).symm))
      _ = p := (h p q q).symm
  have lem3 : ∀ (p : G) (q : G) (r : G), ((p ◇ q) ◇ q) = ((p ◇ r) ◇ r) := by
    intro p q r
    calc ((p ◇ q) ◇ q)
      _ = (((((p ◇ q) ◇ q) ◇ r) ◇ (((p ◇ q) ◇ q) ◇ p)) ◇ r) := h ((p ◇ q) ◇ q) r p
      _ = (((((p ◇ q) ◇ q) ◇ ((p ◇ q) ◇ q)) ◇ r) ◇ r) := congrArg (· ◇ r) (lem1 ((p ◇ q) ◇ q) r p)
      _ = ((p ◇ r) ◇ r) := congrArg (· ◇ r) (congrArg (· ◇ r) (lem2 p q q))
  intro x y z
  calc x
    _ = (((x ◇ (x ◇ z)) ◇ (x ◇ z)) ◇ (x ◇ z)) := h x (x ◇ z) z
    _ = (((x ◇ y) ◇ y) ◇ (x ◇ z)) := congrArg (· ◇ (x ◇ z)) ((lem3 x y (x ◇ z)).symm)
"""


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def load_solver(path: Path):
    spec = importlib.util.spec_from_file_location(
        "mathgraph_0036_diagonal_fiber_solver", path
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def alpha_equation_key(equation):
    names = {}

    def visit(term):
        if term[0] == "var":
            names.setdefault(term[1], "v" + str(len(names)))
            return ("var", names[term[1]])
        return ("op", visit(term[1]), visit(term[2]))

    return visit(equation[0]), visit(equation[1])


def official_judge(problem, code):
    from judge.verify import verify_answer

    proxy_tree = ast.parse(
        (ROOT / "pipeline/proxy.py").read_text(encoding="utf-8")
    )
    policy = None
    for node in proxy_tree.body:
        if (
            isinstance(node, ast.Assign)
            and any(
                isinstance(target, ast.Name)
                and target.id == "DEFAULT_PROOF_POLICY"
                for target in node.targets
            )
        ):
            policy = ast.literal_eval(node.value)
            break
    if policy is None:
        raise RuntimeError("DEFAULT_PROOF_POLICY not found")
    started = time.monotonic()
    result = verify_answer(
        {**problem, "proof_policy": policy},
        json.dumps({"verdict": "true", "code": code}),
    )
    return result, round(time.monotonic() - started, 6)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--official", action="store_true")
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    args = parser.parse_args()

    protocol = json.loads(PREREG.read_text(encoding="utf-8"))
    rows = json.loads(INPUT.read_text(encoding="utf-8"))
    expected_headers = set(protocol["frozen_input"]["allowed_input_headers"])
    headers_ok = bool(rows) and all(set(row) == expected_headers for row in rows)
    label_fields = sorted(
        set().union(*(set(row) for row in rows)) - expected_headers
    ) if rows else []
    solver_path = ROOT / protocol["frozen_input"]["solver_path"]
    hashes_ok = all((
        sha256(PREREG) == EXPECTED_PREREG_SHA256,
        sha256(INPUT) == protocol["frozen_input"]["unlabelled_input_sha256"],
        sha256(solver_path) == protocol["frozen_input"]["solver_sha256"],
    ))
    parent = json.loads(PARENT.read_text(encoding="utf-8")) if PARENT.exists() else None
    parent_ok = bool(parent) and all((
        parent.get("conclusion") == "success",
        parent.get("result_summary", {}).get("decision")
        == protocol["pending_public_parent"]["required_decision"],
        parent.get("result_summary", {}).get("lean_status")
        == protocol["pending_public_parent"]["required_lean_status"],
    ))

    solver = load_solver(solver_path)
    source_schema = solver.parse_equation(
        protocol["constructor_constraints"]["source_schema"]
    )
    target_schema = solver.parse_equation(
        protocol["constructor_constraints"]["target_schema"]
    )
    source_key = alpha_equation_key(source_schema)
    target_key = alpha_equation_key(target_schema)
    matches = []
    for row in rows:
        source = solver.parse_equation(row["equation1"])
        target = solver.parse_equation(row["equation2"])
        if (
            alpha_equation_key(source) == source_key
            and alpha_equation_key(target) == target_key
        ):
            matches.append(row)
    schema_ok = len(matches) == 1
    problem = matches[0] if schema_ok else None

    certificate_bytes = len(CERTIFICATE.encode())
    certificate_sha256 = sha256_text(CERTIFICATE)
    expected_certificate_sha256 = protocol["local_selection_evidence"][
        "certificate_sha256"
    ]
    relation = protocol["constructor_constraints"]["derived_diagonal_fiber"]
    relation_ok = (
        "have lem3 : ∀ (p : G) (q : G) (r : G), " + relation
    ) in CERTIFICATE
    final_lift_ok = (
        "congrArg (· ◇ (x ◇ z)) ((lem3 x y (x ◇ z)).symm)"
        in CERTIFICATE
    )
    certificate_static_ok = all((
        certificate_sha256 == expected_certificate_sha256,
        certificate_bytes
        <= protocol["constructor_constraints"]["maximum_certificate_bytes"],
        relation_ok,
        final_lift_ok,
    ))

    judge_status = None
    judge_seconds = None
    if args.official and schema_ok and certificate_static_ok:
        judged, judge_seconds = official_judge(problem, CERTIFICATE)
        judge_status = judged.get("status")

    measurement_ok = all((
        protocol["status"]
        == "AMENDED_AFTER_PARENT_JUDGE_WRAPPER_FAILURE_BEFORE_EXECUTABLE_PUBLICATION",
        parent_ok,
        hashes_ok,
        headers_ok,
        not label_fields,
    ))
    if not measurement_ok:
        decision = "MEASUREMENT_FAILURE"
    elif not schema_ok:
        decision = "DIAGONAL_FIBER_SCHEMA_MISMATCH"
    elif relation_ok and not (
        args.official and judge_status == "accepted" and certificate_static_ok
    ):
        decision = "DIAGONAL_FIBER_RELATION_ONLY"
    elif judge_status == "accepted" and certificate_static_ok:
        decision = "DIAGONAL_FIBER_CONSTRUCTOR_CAUSAL"
    else:
        decision = "DIAGONAL_FIBER_CONSTRUCTOR_FAILURE"

    args.output_dir.mkdir(parents=True, exist_ok=True)
    certificate_path = args.output_dir / "0036_diagonal_fiber_certificate.lean"
    certificate_path.write_text(CERTIFICATE, encoding="utf-8")
    result = {
        "schema": "mathgraph.0036-diagonal-fiber-constructor-results.v1",
        "decision": decision,
        "measurement_ok": measurement_ok,
        "official_enabled": args.official,
        "parent_ok": parent_ok,
        "frozen_hashes_ok": hashes_ok,
        "input_headers_ok": headers_ok,
        "label_fields_available_to_runner": label_fields,
        "schema_match_count": len(matches),
        "source_schema_matches": schema_ok,
        "target_schema_matches": schema_ok,
        "diagonal_fiber_relation": relation,
        "diagonal_fiber_relation_ok": relation_ok,
        "final_congruence_lift_ok": final_lift_ok,
        "certificate_bytes": certificate_bytes,
        "certificate_sha256": certificate_sha256,
        "certificate_static_ok": certificate_static_ok,
        "lean_status": judge_status,
        "judge_seconds": judge_seconds,
    }
    output = args.output_dir / "0036_diagonal_fiber_constructor_results.json"
    output.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(result, sort_keys=True), flush=True)
    if decision != "DIAGONAL_FIBER_CONSTRUCTOR_CAUSAL":
        raise SystemExit(decision)


if __name__ == "__main__":
    main()

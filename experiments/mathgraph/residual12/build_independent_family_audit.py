#!/usr/bin/env python3
"""Build a sealed, prior-contact-excluded transfer audit.

This builder may read labels only to balance the frozen audit.  It writes the
runner input and labels separately; the experiment runner never imports this
module or receives the label path.
"""

import hashlib
import importlib.util
import json
import sys
from pathlib import Path


sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
SOLVER = ROOT / "submissions/mathgraph_cleanroom/solver.py"
EXPERIMENTS = ROOT / "experiments/mathgraph"
PROBLEMS = ROOT / "examples/problems"
HERE = Path(__file__).resolve().parent
FAMILIES = ("normal", "hard1", "hard2", "hard3")
PER_LABEL_PER_FAMILY = 20


def load_solver():
    spec = importlib.util.spec_from_file_location(
        "mathgraph_independent_audit_builder_solver", SOLVER
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def canonical_pair_hash(solver, row):
    source = solver.parse_equation(row["equation1"])
    target = solver.parse_equation(row["equation2"])
    payload = (
        solver.render_term(source[0]) + " = " + solver.render_term(source[1])
        + "\0"
        + solver.render_term(target[0]) + " = " + solver.render_term(target[1])
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def walk_prior(value, solver, used_ids, used_hashes):
    if isinstance(value, dict):
        for key in ("content_sha256", "pair_content_hash", "source_row_hash"):
            digest = value.get(key)
            if isinstance(digest, str) and len(digest) == 64:
                used_hashes.add(digest)
        problem_id = value.get("id")
        if isinstance(problem_id, str):
            used_ids.add(problem_id)
        if isinstance(value.get("equation1"), str) and isinstance(
            value.get("equation2"), str
        ):
            try:
                used_hashes.add(canonical_pair_hash(solver, value))
            except Exception:
                pass
        for child in value.values():
            walk_prior(child, solver, used_ids, used_hashes)
    elif isinstance(value, list):
        for child in value:
            walk_prior(child, solver, used_ids, used_hashes)


def prior_contact_registry(solver):
    used_ids = set()
    used_hashes = set()
    for path in sorted(EXPERIMENTS.rglob("*.json")):
        if HERE in path.parents:
            continue
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError):
            continue
        walk_prior(payload, solver, used_ids, used_hashes)
    return used_ids, used_hashes


def read_jsonl(path):
    return [
        json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def main():
    solver = load_solver()
    used_ids, used_hashes = prior_contact_registry(solver)
    selected = []
    labels = {}
    census = {}
    for family in FAMILIES:
        eligible = []
        for row in read_jsonl(PROBLEMS / f"{family}.jsonl"):
            digest = canonical_pair_hash(solver, row)
            if row["id"] in used_ids or digest in used_hashes:
                continue
            eligible.append((digest, row))
        family_selected = []
        counts = {}
        for label in (True, False):
            candidates = sorted(
                (item for item in eligible if item[1].get("answer") is label),
                key=lambda item: (item[0], item[1]["id"]),
            )
            chosen = candidates[:PER_LABEL_PER_FAMILY]
            counts[str(label).lower()] = {
                "eligible": len(candidates), "selected": len(chosen)
            }
            for digest, row in chosen:
                public_row = {
                    "id": "transfer_" + digest[:20],
                    "source_family": family,
                    "source_problem_id_sha256": hashlib.sha256(
                        row["id"].encode("utf-8")
                    ).hexdigest(),
                    "content_sha256": digest,
                    "eq1_id": row.get("eq1_id"),
                    "eq2_id": row.get("eq2_id"),
                    "equation1": row["equation1"],
                    "equation2": row["equation2"],
                }
                family_selected.append(public_row)
                labels[public_row["id"]] = label
        selected.extend(sorted(family_selected, key=lambda row: row["content_sha256"]))
        census[family] = counts
    selected.sort(key=lambda row: (row["source_family"], row["content_sha256"]))
    if not selected:
        raise SystemExit("no untouched rows remain")
    inputs = {
        "schema": "mathgraph.residual12-independent-family-inputs.v1",
        "selection": {
            "families": list(FAMILIES),
            "per_label_per_family": PER_LABEL_PER_FAMILY,
            "ordering": "canonical content hash",
            "prior_exclusion": "all IDs and reconstructible content hashes in experiments/mathgraph JSON outside residual12",
        },
        "prior_registry": {
            "ids": len(used_ids), "content_hashes": len(used_hashes)
        },
        "census": census,
        "rows": selected,
    }
    label_payload = {
        "schema": "mathgraph.residual12-independent-family-labels.v1",
        "integrity_note": "Plaintext experimental seal; never passed to the search runner.",
        "labels": dict(sorted(labels.items())),
    }
    input_path = HERE / "independent_family_audit_inputs.json"
    label_path = HERE / "independent_family_audit_labels.sealed.json"
    input_path.write_text(json.dumps(inputs, indent=2, sort_keys=True) + "\n")
    label_path.write_text(json.dumps(label_payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "rows": len(selected),
        "families": census,
        "inputs_sha256": hashlib.sha256(input_path.read_bytes()).hexdigest(),
        "labels_sha256": hashlib.sha256(label_path.read_bytes()).hexdigest(),
    }, sort_keys=True))


if __name__ == "__main__":
    main()

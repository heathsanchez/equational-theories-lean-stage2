#!/usr/bin/env python3
"""Proof-producing research constructors for recursive collapse laws."""

import argparse
import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / "submissions/mathgraph/solver.py"


def load_solver():
    spec = importlib.util.spec_from_file_location("collapse_solver", SOLVER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def variable_omission_proof(module, source, target):
    """Prove any target when a source side is a universally collapsed variable."""
    left, right, variables = source
    if left[0] == "var" and left[1] not in module.term_variables(right):
        collapsed_variable = left[1]
        body = right
        reverse = False
    elif right[0] == "var" and right[1] not in module.term_variables(left):
        collapsed_variable = right[1]
        body = left
        reverse = True
    else:
        return None
    target_left, target_right, target_variables = target
    if not target_variables:
        return None
    anchor = ("var", target_variables[0])

    def mapping_for(collapsed_term):
        return {
            variable: collapsed_term if variable == collapsed_variable else anchor
            for variable in variables
        }

    left_mapping = mapping_for(target_left)
    right_mapping = mapping_for(target_right)
    common_left = module.substitute(body, left_mapping)
    common_right = module.substitute(body, right_mapping)
    if common_left != common_right:
        return None
    substitution_left = tuple(
        (variable, left_mapping[variable]) for variable in variables
    )
    substitution_right = tuple(
        (variable, right_mapping[variable]) for variable in variables
    )
    nodes = [
        module.EqualityNode(
            target_left, common_left, "source instance",
            substitution=substitution_left,
            orientation=reverse,
            constructor="variable-omission-collapse",
        ),
        module.EqualityNode(
            target_right, common_right, "source instance",
            substitution=substitution_right,
            orientation=reverse,
            constructor="variable-omission-collapse",
        ),
        module.EqualityNode(
            common_right, target_right, "symmetry", parents=(1,),
            constructor="variable-omission-collapse",
        ),
        module.EqualityNode(
            target_left, target_right, "transitivity", parents=(0, 2),
            constructor="variable-omission-collapse",
        ),
    ]
    if not module.replay_dag(source, nodes, 3):
        return None
    return nodes, 3


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--id")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    module = load_solver()
    rows = json.loads((ROOT / "examples/problems/sample_200.json").read_text())
    results = []
    for row in rows:
        if not row["id"].startswith("true_"):
            continue
        if args.id is not None and row["id"] != args.id:
            continue
        source = module.parse_equation(row["equation1"])
        target = module.parse_equation(row["equation2"])
        found = variable_omission_proof(module, source, target)
        record = {"id": row["id"], "found": found is not None}
        if found is not None:
            nodes, root = found
            code, proof_nodes = module.make_dag_certificate(
                target, nodes, root
            )
            record.update({
                "proof_nodes": proof_nodes,
                "certificate_bytes": len(code.encode()),
                "code": code,
            })
        results.append(record)
    payload = {"constructor": "variable-omission-collapse", "rows": results}
    if args.output:
        args.output.write_text(json.dumps(payload, indent=2))
    print(json.dumps({
        "attempts": len(results),
        "hits": [row["id"] for row in results if row["found"]],
    }, indent=2))


if __name__ == "__main__":
    main()

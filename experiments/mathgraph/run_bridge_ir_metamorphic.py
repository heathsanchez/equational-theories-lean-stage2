#!/usr/bin/env python3
"""Post-unseal metamorphic checks for every external BridgeIR hit."""

import argparse
import importlib.util
import json
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
SOLVER = ROOT / "submissions/mathgraph/solver.py"


def load_solver():
    spec = importlib.util.spec_from_file_location("bridge_metamorphic", SOLVER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rename(term, mapping):
    if term[0] == "var":
        return ("var", mapping[term[1]])
    return ("op", rename(term[1], mapping), rename(term[2], mapping))


def mirror(term):
    if term[0] == "var":
        return term
    return ("op", mirror(term[2]), mirror(term[1]))


def equation_text(module, equation):
    return (
        module.render_term(equation[0])
        + " = "
        + module.render_term(equation[1])
    )


def variants(module, source, target):
    variables = tuple(dict.fromkeys(source[2] + target[2]))
    fresh = tuple(
        value for value in "abcdefghijklmnopqrstuvw"
        if value not in variables
    )
    mapping = dict(zip(variables, fresh))
    renamed_source = (
        rename(source[0], mapping), rename(source[1], mapping),
        tuple(mapping[value] for value in source[2]),
    )
    renamed_target = (
        rename(target[0], mapping), rename(target[1], mapping),
        tuple(mapping[value] for value in target[2]),
    )
    return {
        "variable-renamed": (renamed_source, renamed_target),
        "source-reversed": (
            (source[1], source[0], source[2]), target,
        ),
        "target-reversed": (
            source, (target[1], target[0], target[2]),
        ),
        "mirrored": (
            (mirror(source[0]), mirror(source[1]), source[2]),
            (mirror(target[0]), mirror(target[1]), target[2]),
        ),
    }


def judge(problem, code):
    from judge.verify import verify_answer
    from pipeline.proxy import _to_judge_problem

    result = verify_answer(
        _to_judge_problem(problem),
        json.dumps({"verdict": "true", "code": code}),
    )
    return result.get("status", "unparsed")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--raw-results", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    module = load_solver()
    inputs = {
        row["id"]: row
        for row in json.loads(args.inputs.read_text())["rows"]
    }
    raw = json.loads(args.raw_results.read_text())
    hits = []
    for row in raw["rows"]:
        winning = next(
            (
                attempt for attempt in row["attempts"]
                if attempt.get("judge_status") == "accepted"
            ),
            None,
        )
        if winning is not None:
            hits.append((row, winning))
    records = []
    accepted = 0
    for hit_index, (row, winning) in enumerate(hits):
        original = inputs[row["id"]]
        source = module.parse_equation(original["equation1"])
        target = module.parse_equation(original["equation2"])
        for variant_index, (name, (changed_source, changed_target)) in enumerate(
            variants(module, source, target).items()
        ):
            # Reparse the rendered presentation so quantified-variable order
            # exactly matches the official judge's equation parser.
            changed_source = module.parse_equation(
                equation_text(module, changed_source)
            )
            changed_target = module.parse_equation(
                equation_text(module, changed_target)
            )
            found = None
            used_configuration = None
            search = None
            for configuration in (
                module.BRIDGE_IR_PORTFOLIO[2],
                module.BRIDGE_IR_PORTFOLIO[3],
            ):
                search = module.BridgeIR(
                    changed_source,
                    changed_target,
                    time.monotonic() + configuration["seconds"],
                    configuration,
                )
                found = search.solve()
                if found is not None:
                    used_configuration = configuration["name"]
                    break
            record = {
                "source_hit_id": row["id"],
                "source_configuration": winning["configuration"],
                "variant": name,
                "found": found is not None,
                "configuration": used_configuration,
                "activations": (
                    search.no_match_activations if search is not None else 0
                ),
            }
            if found is not None:
                code, proof_nodes = module.make_dag_certificate(
                    changed_target, *found
                )
                problem = {
                    "id": f"bridge_meta_{hit_index}_{variant_index}",
                    "eq1_id": 983000 + hit_index * 20 + variant_index * 2,
                    "eq2_id": 983001 + hit_index * 20 + variant_index * 2,
                    "equation1": equation_text(module, changed_source),
                    "equation2": equation_text(module, changed_target),
                }
                status = judge(problem, code)
                record.update({
                    "judge_status": status,
                    "proof_nodes": proof_nodes,
                    "certificate_bytes": len(code.encode()),
                })
                if status == "accepted":
                    accepted += 1
            records.append(record)
            print(
                row["id"], name, record.get("judge_status", "abstained"),
                flush=True,
            )
    summary = {
        "external_hits": len(hits),
        "variants": len(records),
        "official_acceptances": accepted,
        "abstentions": sum(not record["found"] for record in records),
        "invalid_outcomes": sum(
            record.get("judge_status") not in (None, "accepted")
            for record in records
        ),
        "records": records,
    }
    args.output.write_text(json.dumps(summary, indent=2, sort_keys=True))
    print(json.dumps({
        key: summary[key]
        for key in (
            "external_hits", "variants", "official_acceptances",
            "abstentions", "invalid_outcomes",
        )
    }, indent=2))


if __name__ == "__main__":
    main()

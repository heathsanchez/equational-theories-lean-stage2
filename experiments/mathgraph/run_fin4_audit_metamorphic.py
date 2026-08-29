#!/usr/bin/env python3
"""Metamorphic checks for unsealed, officially accepted Fin-4 audit hits."""

import argparse
import hashlib
import importlib.util
import json
import string
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
SOLVER = ROOT / "submissions/mathgraph/solver.py"
EXPECTED_SOLVER_SHA256 = (
    "ddb646624106d143a6b0882b1ec46fa9e047dc40214310010b5dda89f55f2eb7"
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_solver():
    assert sha256(SOLVER) == EXPECTED_SOLVER_SHA256
    spec = importlib.util.spec_from_file_location(
        "fin4_audit_metamorphic_solver", SOLVER
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def render_equation(module, equation):
    return (
        module.render_term(equation[0])
        + " = "
        + module.render_term(equation[1])
    )


def map_term(term, mapping=None, mirror=False):
    if term[0] == "var":
        return ("var", mapping.get(term[1], term[1]) if mapping else term[1])
    left = map_term(term[1], mapping, mirror)
    right = map_term(term[2], mapping, mirror)
    return ("op", right, left) if mirror else ("op", left, right)


def transform_equation(module, text, mapping=None, reverse=False,
                       mirror=False):
    left, right, _ = module.parse_equation(text)
    left = map_term(left, mapping, mirror)
    right = map_term(right, mapping, mirror)
    if reverse:
        left, right = right, left
    return module.render_term(left) + " = " + module.render_term(right)


def relabel_table(table, permutation, order=4):
    result = [0] * (order * order)
    for left in range(order):
        for right in range(order):
            result[order * permutation[left] + permutation[right]] = (
                permutation[table[order * left + right]]
            )
    return tuple(result)


def verify(problem, code):
    from judge.verify import verify_answer
    from pipeline.proxy import _to_judge_problem

    answer = json.dumps({"verdict": "false", "code": code})
    result = verify_answer(_to_judge_problem(problem), answer)
    return result.get("status", "unparsed")


def run_search(module, problem, configuration):
    started = time.monotonic()
    engine = module.FiniteModelEngine(
        4,
        module.parse_equation(problem["equation1"]),
        module.parse_equation(problem["equation2"]),
        started + configuration["seconds"],
        configuration["maximum_states"],
        configuration["maximum_models"],
        options=configuration["options"],
    )
    found = engine.search_target_guided()
    result = {
        "found": found is not None,
        "seconds": round(time.monotonic() - started, 6),
        "partial_states": engine.partial_states,
        "exhaustion": engine.exhaustion,
    }
    if found is not None:
        table, witness = found
        result["replay_ok"] = engine.replay(table, witness)
        result["judge_status"] = verify(
            problem, engine.emit_certificate(table)
        )
        result["canonical_table"] = list(engine.canonicalize(table))
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    module = load_solver()
    inputs = json.loads(args.inputs.read_text(encoding="utf-8"))["rows"]
    by_id = {row["id"]: row for row in inputs}
    summary = json.loads(args.summary.read_text(encoding="utf-8"))
    records = []
    permutation = (1, 2, 3, 0)
    for hit_index, hit in enumerate(
        summary["fin4"]["hit_records"], 1
    ):
        row = by_id[hit["id"]]
        source = module.parse_equation(row["equation1"])
        target = module.parse_equation(row["equation2"])
        names = sorted(set(source[2]) | set(target[2]))
        replacements = [
            name for name in reversed(string.ascii_lowercase)
            if name not in names
        ]
        mapping = dict(zip(names, replacements))
        original_table = tuple(hit["canonical_table"])
        variants = {
            "variable-renaming": (
                transform_equation(module, row["equation1"], mapping=mapping),
                transform_equation(module, row["equation2"], mapping=mapping),
                original_table,
            ),
            "source-side-reversal": (
                transform_equation(module, row["equation1"], reverse=True),
                row["equation2"],
                original_table,
            ),
            "target-side-reversal": (
                row["equation1"],
                transform_equation(module, row["equation2"], reverse=True),
                original_table,
            ),
            "mirrored-presentation": (
                transform_equation(module, row["equation1"], mirror=True),
                transform_equation(module, row["equation2"], mirror=True),
                tuple(
                    original_table[4 * right + left]
                    for left in range(4) for right in range(4)
                ),
            ),
            "element-relabeling": (
                row["equation1"],
                row["equation2"],
                relabel_table(original_table, permutation),
            ),
        }
        configuration = next(
            item for item in module.FIN4_PORTFOLIO
            if item["name"] == hit["configuration"]
        )
        print(
            f"[{hit_index}/{len(summary['fin4']['hit_records'])}] "
            f"{hit['id']}",
            flush=True,
        )
        variant_records = {}
        for offset, (name, (source_text, target_text, table)) in enumerate(
            variants.items(), 1
        ):
            problem = {
                "id": f"{row['id']}_{offset}",
                "eq1_id": row["eq1_id"] + 100 + offset,
                "eq2_id": row["eq2_id"] + 100 + offset,
                "equation1": source_text,
                "equation2": target_text,
            }
            constructed_status = verify(
                problem, module.emit_fin_certificate(table, 4)
            )
            search = None
            if name != "element-relabeling":
                search = run_search(module, problem, configuration)
            canonical_constructed = list(
                module.FiniteModelEngine(
                    4,
                    module.parse_equation(source_text),
                    module.parse_equation(target_text),
                    time.monotonic() + 0.01,
                    1,
                    1,
                ).canonicalize(table)
            )
            relation = (
                "same-canonical-model"
                if canonical_constructed == hit["canonical_table"]
                else "isomorphic-or-opposite-valid-model"
            )
            if search and search.get("found"):
                relation = (
                    "same-canonical-model"
                    if search["canonical_table"] == hit["canonical_table"]
                    else "different-valid-model"
                )
            variant_records[name] = {
                "constructed_certificate_status": constructed_status,
                "search": search,
                "model_relation": relation,
            }
        records.append({
            "id": hit["id"],
            "configuration": hit["configuration"],
            "variants": variant_records,
        })
    failures = []
    search_found = 0
    search_total = 0
    for record in records:
        for name, variant in record["variants"].items():
            if variant["constructed_certificate_status"] != "accepted":
                failures.append(
                    f"{record['id']}:{name}:constructed:"
                    f"{variant['constructed_certificate_status']}"
                )
            if variant["search"] is not None:
                search_total += 1
                if variant["search"]["found"]:
                    search_found += 1
                    if variant["search"].get("judge_status") != "accepted":
                        failures.append(
                            f"{record['id']}:{name}:search:"
                            f"{variant['search'].get('judge_status')}"
                        )
    payload = {
        "solver_sha256": sha256(SOLVER),
        "hit_count": len(records),
        "variants_per_hit": 5,
        "official_constructed_certificates_accepted":
            5 * len(records) - len([
                item for item in failures if ":constructed:" in item
            ]),
        "search_presentations_found": search_found,
        "search_presentations_attempted": search_total,
        "failures": failures,
        "records": records,
    }
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8"
    )
    print(json.dumps({
        "hits": len(records),
        "constructed_accepted":
            payload["official_constructed_certificates_accepted"],
        "search_found": search_found,
        "search_attempted": search_total,
        "failures": failures,
    }, indent=2))


if __name__ == "__main__":
    main()

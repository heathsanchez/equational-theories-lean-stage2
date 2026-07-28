#!/usr/bin/env python3
"""Corrupt one accepted forward-demodulation trace and require rejection."""

from __future__ import annotations

import argparse
import copy
import importlib.util
import json
import re
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
SOURCE = HERE / "run_forward_demodulation_ablation.py"


def load_ablation():
    spec = importlib.util.spec_from_file_location("forward_demod_ablation", SOURCE)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def first_step(spec):
    for lemma in spec.get("lemmas", []):
        if lemma.get("steps"):
            return lemma["steps"], 0
    return spec["goal_steps"], 0


def rejected(replayer, spec):
    try:
        replayer.replay_plan(spec)
    except (KeyError, TypeError, ValueError):
        return True
    return False


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--input", type=Path, default=Path("/tmp/mathgraph-six-residuals.json")
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=HERE / "demodulation_corruption_tests.json",
    )
    args = parser.parse_args()
    ablation = load_ablation()
    solver = ablation.load_solver()
    engine, _ = ablation.prepare_engine(solver)
    independent = ablation.load_independent_replayer()
    problem = next(
        row for row in json.loads(args.input.read_text())
        if row["id"] == "evaluation_normal_0158"
    )
    settings = engine["argparse"].Namespace(
        max_clauses=8000,
        max_weight=36,
        max_term_size=30,
        max_processed=8000,
        pair_budget=300,
        timeout=2.0,
        translate=True,
        unordered=False,
        neg_bias=0,
        old_rules_first=False,
        tautology_prune=False,
        forward_subsumption=False,
    )
    result = ablation.ForwardDemodulationRun(engine, problem, settings).solve()
    if result.get("status") != "proved" or not independent.replay_plan(result["spec"]):
        raise RuntimeError("control proof did not replay")
    original = result["spec"]
    cases = {}

    changed = copy.deepcopy(original)
    steps, index = first_step(changed)
    steps[index]["rule"] = "missing_demodulator"
    cases["altered_demodulator"] = rejected(independent, changed)

    changed = copy.deepcopy(original)
    steps, index = first_step(changed)
    steps[index]["kind"] = "rev" if steps[index]["kind"] == "fwd" else "fwd"
    cases["reverse_orientation"] = rejected(independent, changed)

    changed = copy.deepcopy(original)
    steps, index = first_step(changed)
    steps[index]["path"] = steps[index].get("path", "") + "L"
    cases["altered_path"] = rejected(independent, changed)

    changed = copy.deepcopy(original)
    steps, index = first_step(changed)
    steps[index]["args"] = list(steps[index].get("args", [])) + ["x"]
    cases["altered_substitution"] = rejected(independent, changed)

    changed = copy.deepcopy(original)
    steps, index = first_step(changed)
    del steps[index]
    cases["missing_intermediate"] = rejected(independent, changed)

    changed = copy.deepcopy(original)
    changed["equation2"] = "x = x * x"
    cases["changed_final_target"] = rejected(independent, changed)

    proof_text = result["proof_text"]
    lines = proof_text.splitlines()
    for line_index, line in enumerate(lines):
        if line.startswith(result["closed_id"] + " ") and "[para(" in line:
            lines[line_index] = re.sub(
                r"para\(\d+\(", "para(999999(", line, count=1
            )
            break
    changed_text = "\n".join(lines)
    try:
        engine["translate_proof"](
            problem["equation1"], problem["equation2"], changed_text
        )
    except (KeyError, TypeError, ValueError, engine["pm_p9t_TranslateError"]):
        cases["altered_parent_clause"] = True
    else:
        cases["altered_parent_clause"] = False

    payload = {
        "schema": "mathgraph.demodulation-corruption-tests.v1",
        "control": {
            "id": problem["id"],
            "replayed": True,
            "forward_demodulations": result["forward_demodulations"],
        },
        "cases": cases,
        "passed": all(cases.values()),
    }
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2))
    if not payload["passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()

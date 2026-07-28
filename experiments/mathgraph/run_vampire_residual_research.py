#!/usr/bin/env python3
"""Diagnostic Vampire coverage of the current TRUE residuals."""

import importlib.util
import argparse
import json
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def load_solver():
    path = ROOT / "submissions/mathgraph/solver.py"
    spec = importlib.util.spec_from_file_location("mathgraph_solver", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def render(term):
    if term[0] == "var":
        return "V_" + term[1].upper()
    return f"f({render(term[1])},{render(term[2])})"


def quantified(equation):
    lhs, rhs, variables = equation
    binders = ",".join("V_" + variable.upper() for variable in variables)
    return f"! [{binders}] : {render(lhs)} = {render(rhs)}"


def current_residuals():
    rows = json.loads((ROOT / "examples/problems/sample_200.json").read_text())
    accepted = set(
        json.loads(
            (ROOT / "experiments/mathgraph/results/"
             "normalization_baseline_manifest.json").read_text()
        )["sample_200_accepted"]
    )
    accepted.update(
        json.loads(
            (ROOT / "experiments/mathgraph/results/"
             "quotient_matcher_promotion_summary.json").read_text()
        )["public_hits"]
    )
    accepted.update(
        json.loads(
            (ROOT / "experiments/mathgraph/results/"
             "variable_omission_collapse_summary.json").read_text()
        )["sample_200"]["new_hits"]
    )
    return [
        row for row in rows
        if row["id"].startswith("true_") and row["id"] not in accepted
    ]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path)
    parser.add_argument("--output", type=Path, default=Path(
        "/tmp/mathgraph-vampire-residuals.json"
    ))
    parser.add_argument("--seconds", type=int, default=10)
    args = parser.parse_args()
    module = load_solver()
    results = []
    rows = current_residuals()
    if args.input:
        payload = json.loads(args.input.read_text())
        rows = payload["rows"] if isinstance(payload, dict) else payload
    for index, row in enumerate(rows, 1):
        source = module.parse_equation(row["equation1"])
        target = module.parse_equation(row["equation2"])
        problem = (
            f"fof(source,axiom,({quantified(source)})).\n"
            f"fof(target,conjecture,({quantified(target)})).\n"
        )
        started = time.monotonic()
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".p", dir="/tmp", delete=True
        ) as handle:
            handle.write(problem)
            handle.flush()
            try:
                run = subprocess.run(
                    [
                        "vampire", "--mode", "casc", "--time_limit",
                        str(args.seconds),
                        "--proof", "tptp", handle.name,
                    ],
                    capture_output=True, text=True, timeout=args.seconds + 2,
                )
                output = run.stdout + run.stderr
            except subprocess.TimeoutExpired as error:
                output = (error.stdout or "") + (error.stderr or "")
        proof_lines = [
            line for line in output.splitlines()
            if line.startswith("fof(")
        ]
        record = {
            "id": row["id"],
            "theorem": "SZS status Theorem" in output,
            "seconds": round(time.monotonic() - started, 6),
            "proof_lines": len(proof_lines),
            "superposition_steps": output.count("inference(superposition"),
            "demodulation_steps": output.count("demodulation"),
            "peak_memory_mb": next(
                (
                    line.split(":")[-1].strip()
                    for line in output.splitlines()
                    if "Peak memory usage:" in line
                ),
                None,
            ),
            "proof": output if "SZS status Theorem" in output else None,
        }
        results.append(record)
        print(
            f"[{index}/{len(rows)}] "
            + json.dumps({k: v for k, v in record.items() if k != "proof"}),
            flush=True,
        )
    args.output.write_text(
        json.dumps({"diagnostic_only": True, "rows": results}, indent=2)
    )


if __name__ == "__main__":
    main()

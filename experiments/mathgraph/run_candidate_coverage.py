#!/usr/bin/env python3
"""Measure fail-closed solver candidate coverage without invoking Lean."""

import argparse
import concurrent.futures
import json
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def load_rows(path):
    text = path.read_text()
    if text.lstrip().startswith("["):
        return json.loads(text)
    return [json.loads(line) for line in text.splitlines() if line.strip()]


def run_one(solver, row, timeout):
    started = time.monotonic()
    process = subprocess.Popen(
        [sys.executable, str(solver)],
        cwd=solver.parent,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    startup = {
        "type": "start",
        "problem": row,
        "budget": {
            "timeout_seconds": timeout,
            "max_code_length": 100000,
            "max_false_cert_bytes": 20000,
        },
    }
    process.stdin.write(json.dumps(startup) + "\n")
    process.stdin.flush()
    candidate = None
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        line = process.stdout.readline()
        if not line:
            break
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            continue
        if message.get("call") == "judge":
            candidate = {
                "verdict": message.get("verdict"),
                "code": message.get("code", ""),
            }
            process.stdin.write(json.dumps({
                "status": "accepted",
                "message": "candidate-coverage audit",
            }) + "\n")
            process.stdin.flush()
            break
        if message.get("call") == "llm":
            process.stdin.write(json.dumps({
                "error": "LLM disabled in deterministic coverage audit",
            }) + "\n")
            process.stdin.flush()
    try:
        process.terminate()
        _, stderr = process.communicate(timeout=2)
    except subprocess.TimeoutExpired:
        process.kill()
        _, stderr = process.communicate()
    return {
        "id": row["id"],
        "candidate": candidate,
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "metrics": [
            line for line in stderr.splitlines()
            if line.startswith("MATHGRAPH_METRICS ")
        ],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--solver",
        type=Path,
        default=ROOT / "submissions/mathgraph/solver.py",
    )
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--timeout", type=float, default=120)
    arguments = parser.parse_args()
    rows = load_rows(arguments.inputs)
    with concurrent.futures.ThreadPoolExecutor(
        max_workers=arguments.workers
    ) as executor:
        futures = [
            executor.submit(
                run_one, arguments.solver.resolve(), row, arguments.timeout
            )
            for row in rows
        ]
        results = [future.result() for future in futures]
    arguments.output.write_text(json.dumps(results, separators=(",", ":")))
    counts = {}
    for result in results:
        candidate = result["candidate"]
        verdict = candidate["verdict"] if candidate else "abstain"
        counts[verdict] = counts.get(verdict, 0) + 1
    print(json.dumps({"rows": len(results), "counts": counts}, indent=2))


if __name__ == "__main__":
    main()

"""Bounded label-blind solver run with labels used only by the evaluator.

This measures deterministic coverage and verdict correctness. It does not
replace official Lean certificate verification.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path


def load_rows(paths):
    rows = []
    for path in paths:
        source = Path(path)
        text = source.read_text(encoding="utf-8")
        parsed = json.loads(text) if text.lstrip().startswith("[") else [
            json.loads(line) for line in text.splitlines() if line.strip()
        ]
        for row in parsed:
            item = dict(row)
            item["_corpus"] = source.stem
            rows.append(item)
    return rows


def run_one(task):
    solver, row, timeout = task
    problem = {key: value for key, value in row.items() if not key.startswith("_")}
    started = time.monotonic()
    process = subprocess.Popen(
        [os.environ.get("PYTHON", "python"), str(solver)],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        bufsize=1,
    )
    candidate = None
    llm_calls = 0
    try:
        process.stdin.write(json.dumps({
            "problem": problem,
            "budget": {"timeout_seconds": timeout},
        }) + "\n")
        process.stdin.flush()
        deadline = time.monotonic() + timeout + 2.0
        while time.monotonic() < deadline:
            line = process.stdout.readline()
            if not line:
                break
            try:
                message = json.loads(line)
            except json.JSONDecodeError:
                continue
            if message.get("call") == "llm":
                llm_calls += 1
                process.stdin.write(json.dumps({"error": "disabled"}) + "\n")
                process.stdin.flush()
            elif message.get("call") == "judge":
                candidate = {
                    "verdict": message.get("verdict"),
                    "certificate_sha256": hashlib.sha256(
                        message.get("code", "").encode()
                    ).hexdigest(),
                    "certificate_bytes": len(message.get("code", "").encode()),
                }
                expected = bool(row.get("answer"))
                accepted = candidate["verdict"] == ("true" if expected else "false")
                process.stdin.write(json.dumps({
                    "status": "accepted" if accepted else "rejected"
                }) + "\n")
                process.stdin.flush()
                if accepted:
                    break
        try:
            process.wait(timeout=1)
        except subprocess.TimeoutExpired:
            process.terminate()
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    expected_verdict = "true" if bool(row.get("answer")) else "false"
    actual = candidate.get("verdict") if candidate else None
    return {
        "id": row.get("id"),
        "corpus": row["_corpus"],
        "expected": expected_verdict,
        "candidate": actual,
        "correct": actual == expected_verdict,
        "wrong": actual is not None and actual != expected_verdict,
        "llm_calls": llm_calls,
        "elapsed_seconds": round(time.monotonic() - started, 4),
        **({key: value for key, value in candidate.items() if key != "verdict"}
           if candidate else {}),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", required=True, type=Path)
    parser.add_argument("--inputs", nargs="+", required=True)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=45.0)
    args = parser.parse_args()
    rows = load_rows(args.inputs)
    tasks = [(args.solver, row, args.timeout) for row in rows]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        results = list(pool.map(run_one, tasks))
    corpora = {}
    for name in sorted({row["corpus"] for row in results}):
        subset = [row for row in results if row["corpus"] == name]
        corpora[name] = {
            "rows": len(subset),
            "accepted_candidates": sum(row["correct"] for row in subset),
            "true": sum(row["correct"] and row["expected"] == "true" for row in subset),
            "false": sum(row["correct"] and row["expected"] == "false" for row in subset),
            "wrong": sum(row["wrong"] for row in subset),
            "abstained": sum(row["candidate"] is None for row in subset),
            "wall_sum_seconds": round(sum(row["elapsed_seconds"] for row in subset), 3),
        }
    payload = {
        "schema": "mathgraph.cleanroom-label-audit.v1",
        "warning": "Label audit only; certificates require separate official Lean verification.",
        "solver_sha256": hashlib.sha256(args.solver.read_bytes()).hexdigest(),
        "rows": len(results),
        "accepted_candidates": sum(row["correct"] for row in results),
        "wrong": sum(row["wrong"] for row in results),
        "abstained": sum(row["candidate"] is None for row in results),
        "llm_calls": sum(row["llm_calls"] for row in results),
        "corpora": corpora,
        "results": results,
    }
    args.output.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(json.dumps({key: value for key, value in payload.items() if key != "results"}, indent=2))


if __name__ == "__main__":
    main()

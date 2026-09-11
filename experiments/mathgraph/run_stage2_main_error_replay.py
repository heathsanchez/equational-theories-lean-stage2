#!/usr/bin/env python3
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from pipeline.proxy import load_config, load_problems, run_solver

DEFAULT_ERROR_INDICES = (3, 11, 34, 41, 50)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--main", required=True)
    ap.add_argument("--output", required=True)
    ap.add_argument("--timeout", type=float, default=3600.0)
    ap.add_argument("--indices", nargs="+", type=int, default=list(DEFAULT_ERROR_INDICES))
    args = ap.parse_args()
    error_indices = tuple(args.indices)

    rows = list(load_problems(args.main))
    by_index = {int(row.get("index", i + 1)): row for i, row in enumerate(rows)}
    missing = [i for i in error_indices if i not in by_index]
    if missing:
        raise SystemExit(f"missing Stage 2 main indices: {missing}; rows={len(rows)}")

    solver_path = ROOT / "submissions/mathgraph/solver.py"
    solver_bytes = solver_path.read_bytes()
    solver_meta = {
        "path": str(solver_path.relative_to(ROOT)),
        "bytes": len(solver_bytes),
        "sha256": hashlib.sha256(solver_bytes).hexdigest(),
    }
    print("STAGE2_ERROR_REPLAY_SOLVER", json.dumps(solver_meta, sort_keys=True), flush=True)

    config = json.loads(json.dumps(load_config()))
    config["solver"]["timeout_seconds"] = args.timeout
    config.setdefault("sandbox", {})["mode"] = "none"

    out_rows = []
    for index in error_indices:
        row = by_index[index]
        trace = []
        started = time.monotonic()
        try:
            result = run_solver(
                ROOT / "submissions/mathgraph",
                row,
                config,
                trace_hook=lambda event, trace=trace: trace.append(event),
            )
            exception = None
        except Exception as exc:
            result = {}
            exception = f"{type(exc).__name__}: {exc}"
        elapsed = time.monotonic() - started

        judge_events = [x for x in trace if x.get("type") == "judge"]
        stderr_lines = [
            line
            for event in trace
            for line in str(event.get("stderr", "")).splitlines()
        ]
        entry = {
            "index": index,
            "id": row.get("id"),
            "difficulty": row.get("difficulty"),
            "eq1_id": row.get("eq1_id"),
            "eq2_id": row.get("eq2_id"),
            "equation1": row.get("equation1"),
            "equation2": row.get("equation2"),
            "ground_truth": row.get("answer"),
            "elapsed_seconds": elapsed,
            "exception": exception,
            "solved": bool(result.get("solved")),
            "verdict": result.get("verdict"),
            "judge_calls": result.get("judge_calls"),
            "llm_calls": result.get("llm_calls"),
            "judge_statuses": [
                (x.get("response") or {}).get("status") for x in judge_events
            ],
            "judge_messages": [
                (x.get("response") or {}).get("message") for x in judge_events
            ],
            "stderr_tail": stderr_lines[-40:],
            "stderr_metrics": [line for line in stderr_lines if "MATHGRAPH_METRICS" in line],
            "trace_event_types": [x.get("type") for x in trace],
        }
        out_rows.append(entry)
        print("STAGE2_ERROR_REPLAY", json.dumps(entry, sort_keys=True), flush=True)

    summary = {
        "schema": "mathgraph.stage2-main-error-replay.v1",
        "diagnostic_only": True,
        "solver": solver_meta,
        "dataset_rows": len(rows),
        "error_indices": list(error_indices),
        "rows": out_rows,
        "solved": [x["index"] for x in out_rows if x["solved"]],
        "unsolved": [x["index"] for x in out_rows if not x["solved"]],
        "exceptions": [x["index"] for x in out_rows if x["exception"]],
    }
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print("STAGE2_ERROR_REPLAY_SUMMARY", json.dumps({
        "solved": summary["solved"],
        "unsolved": summary["unsolved"],
        "exceptions": summary["exceptions"],
    }, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()

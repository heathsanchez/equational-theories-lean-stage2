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

POSITIONS = tuple(range(1, 201))
EXPECTED_SOLVER_BYTES = 423718
EXPECTED_SOLVER_SHA256 = "42c96092bad4b03ce13ab80df927675b65ab65225bff1d971ff328949a6ef7f4"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset", required=True)
    ap.add_argument("--position", required=True, type=int, choices=POSITIONS)
    ap.add_argument("--output", required=True)
    ap.add_argument("--timeout", type=float, default=3600.0)
    args = ap.parse_args()

    rows = list(load_problems(args.dataset))
    by_index = {int(row.get("index", i + 1)): row for i, row in enumerate(rows)}
    if args.position not in by_index:
        raise SystemExit(f"missing evaluation index {args.position}; rows={len(rows)}")
    row = by_index[args.position]

    solver_path = ROOT / "submissions/mathgraph_solo_hybrid/solver.py"
    solver_bytes = solver_path.read_bytes()
    solver_sha256 = hashlib.sha256(solver_bytes).hexdigest()
    if len(solver_bytes) != EXPECTED_SOLVER_BYTES:
        raise SystemExit(f"wrong solver bytes: {len(solver_bytes)}")
    if solver_sha256 != EXPECTED_SOLVER_SHA256:
        raise SystemExit(f"wrong solver sha256: {solver_sha256}")

    config = json.loads(json.dumps(load_config()))
    config["solver"]["timeout_seconds"] = args.timeout
    config.setdefault("sandbox", {})["mode"] = "none"
    llm = config.setdefault("llm", {})
    llm["model"] = "google/gemma-4-31b-it"
    llm["base_url"] = "https://openrouter.ai/api/v1"
    llm["max_output_tokens"] = 65536
    llm["temperature"] = 0.0
    llm["use_seed"] = False
    llm.pop("seed", None)
    llm.pop("provider", None)
    llm.pop("reasoning_effort", None)

    trace = []
    started = time.monotonic()
    try:
        result = run_solver(
            ROOT / "submissions/mathgraph_solo_hybrid",
            row,
            config,
            trace_hook=lambda event: trace.append(event),
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
        "schema": "mathgraph.stage2-main-evaluation-exact-solo-replay.v1",
        "execution_mode": "deterministic_baseline_no_llm_credentials",
        "position": args.position,
        "known_success_control": args.position == 1,
        "id": row.get("id"),
        "global_index": row.get("index"),
        "difficulty": row.get("difficulty"),
        "eq1_id": row.get("eq1_id"),
        "eq2_id": row.get("eq2_id"),
        "equation1": row.get("equation1"),
        "equation2": row.get("equation2"),
        "ground_truth": row.get("answer"),
        "solver_bytes": len(solver_bytes),
        "solver_sha256": solver_sha256,
        "model": llm["model"],
        "elapsed_seconds": elapsed,
        "exception": exception,
        "solved": bool(result.get("solved")),
        "verdict": result.get("verdict"),
        "judge_calls": result.get("judge_calls"),
        "llm_calls": result.get("llm_calls"),
        "reached_llm_seam": bool(result.get("llm_calls")),
        "solved_before_llm": bool(result.get("solved")) and not bool(result.get("llm_calls")),
        "judge_statuses": [
            (x.get("response") or {}).get("status") for x in judge_events
        ],
        "judge_messages": [
            (x.get("response") or {}).get("message") for x in judge_events
        ],
        "stderr_metrics": [line for line in stderr_lines if "MATHGRAPH_METRICS" in line],
        "stderr_tail": stderr_lines[-60:],
        "trace_event_types": [x.get("type") for x in trace],
        "proxy_log_types": [x.get("type") for x in result.get("log", [])],
        "proxy_errors": [
            x.get("message")
            for x in result.get("log", [])
            if x.get("type") == "error" and x.get("message")
        ][-10:],
    }
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(entry, indent=2, sort_keys=True) + "\n")
    print("STAGE2_MAIN_EVALUATION_EXACT_SOLO_REPLAY", json.dumps(entry, sort_keys=True), flush=True)
    if exception:
        raise SystemExit(2)


if __name__ == "__main__":
    main()

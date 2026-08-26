#!/usr/bin/env python3
import argparse, json
from pathlib import Path

from pipeline.proxy import load_config, load_problems, run_solver

CASES = (
    "evaluation_hard_0196",
    "evaluation_normal_0036",
    "evaluation_normal_0040",
    "evaluation_normal_0158",
    "evaluation_order5_0014",
    "evaluation_order5_0042",
)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--normal", required=True)
    ap.add_argument("--hard", required=True)
    ap.add_argument("--order5", required=True)
    ap.add_argument("--output", required=True)
    ap.add_argument("--timeout", type=float, default=60.0)
    args = ap.parse_args()

    rows = {}
    for p in (args.normal, args.hard, args.order5):
        for row in load_problems(p):
            rows[row["id"]] = row

    missing = [rid for rid in CASES if rid not in rows]
    if missing:
        raise SystemExit(f"missing rows: {missing}")

    config = load_config()
    config = json.loads(json.dumps(config))
    config["solver"]["timeout_seconds"] = args.timeout
    config.setdefault("sandbox", {})["mode"] = "none"

    out_rows = []
    for rid in CASES:
        trace = []
        result = run_solver(
            Path("submissions/mathgraph"), rows[rid], config,
            trace_hook=lambda event, trace=trace: trace.append(event),
        )
        judge_events = [x for x in trace if x.get("type") == "judge"]
        entry = {
            "id": rid,
            "solved": bool(result.get("solved")),
            "verdict": result.get("verdict"),
            "judge_calls": result.get("judge_calls"),
            "llm_calls": result.get("llm_calls"),
            "judge_statuses": [
                (x.get("response") or {}).get("status") for x in judge_events
            ],
            "stderr_metrics": [
                line for x in trace
                for line in str(x.get("stderr", "")).splitlines()
                if "MATHGRAPH_METRICS" in line
            ],
        }
        out_rows.append(entry)
        print("SIX_RESIDUAL_796", json.dumps(entry, sort_keys=True), flush=True)

    out = {
        "schema": "mathgraph.796-six-residual-probe.v1",
        "diagnostic_only": True,
        "solver_behavior_changed": False,
        "rows": out_rows,
        "solved": [x["id"] for x in out_rows if x["solved"]],
        "remaining": [x["id"] for x in out_rows if not x["solved"]],
    }
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print("SIX_RESIDUAL_796_SUMMARY", json.dumps({"solved": out["solved"], "remaining": out["remaining"]}, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()

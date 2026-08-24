#!/usr/bin/env python3
"""Run a paired full-800 official A/B of compact-fast scheduling only."""

import argparse
import hashlib
import json
import tempfile
import time
from collections import Counter
from pathlib import Path

from datasets import load_dataset
from pipeline.proxy import load_config, run_solver


ROOT = Path(__file__).resolve().parents[3]
CONTROL = ROOT / "submissions/mathgraph_cleanroom/solver.py"
EXPECTED_CONTROL_SHA256 = "a92eae8cce4fdf7c787c3218fa4f7eb1158c92a6b57f2920199ddbe6e7726a08"
EXPECTED_INTERVENTION_SHA256 = "652fba6799e9066368f135319023865a4a58399f7a7228f20b31ea59bdc8f39c"
DATASETS = (
    "evaluation_normal",
    "evaluation_hard",
    "evaluation_extra_hard",
    "evaluation_order5",
)
OLD_ALLOCATION = '''    compact_seconds = min(
        compact_limits["seconds"], max(0.1, timeout / 40.0)
    )'''
NEW_ALLOCATION = '''    compact_seconds = min(
        compact_limits["seconds"], max(0.1, timeout / 24.0)
    )'''


def digest_bytes(payload):
    return hashlib.sha256(payload).hexdigest()


def make_intervention(destination):
    destination.mkdir(parents=True)
    source = CONTROL.read_text(encoding="utf-8")
    if source.count(OLD_ALLOCATION) != 1 or NEW_ALLOCATION in source:
        raise SystemExit("compact allocation edit is not unique")
    changed = source.replace(OLD_ALLOCATION, NEW_ALLOCATION)
    payload = changed.encode("utf-8")
    if digest_bytes(payload) != EXPECTED_INTERVENTION_SHA256:
        raise SystemExit("generated intervention hash differs from freeze")
    (destination / "solver.py").write_bytes(payload)


def judge_statuses(result):
    return [
        event.get("response", {}).get("status", "unparsed")
        for event in result.get("log", [])
        if event.get("type") == "judge"
    ]


def run_arm(submission, problem, config):
    started = time.monotonic()
    result = run_solver(submission, problem, config)
    return {
        "solved": bool(result.get("solved")),
        "verdict": result.get("verdict"),
        "judge_calls": result.get("judge_calls", 0),
        "llm_calls": result.get("llm_calls", 0),
        "judge_statuses": judge_statuses(result),
        "elapsed_seconds": round(time.monotonic() - started, 6),
    }


def summarize(rows, arm):
    selected = [row[arm] for row in rows]
    solved = [row for row in selected if row["solved"]]
    statuses = Counter(
        status for row in selected for status in row["judge_statuses"]
    )
    return {
        "solved": len(solved),
        "unsolved": len(selected) - len(solved),
        "verdict_counts": dict(Counter(row["verdict"] for row in solved)),
        "judge_calls": sum(row["judge_calls"] for row in selected),
        "llm_calls": sum(row["llm_calls"] for row in selected),
        "judge_status_counts": dict(statuses),
        "elapsed_seconds": round(sum(row["elapsed_seconds"] for row in selected), 3),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if digest_bytes(CONTROL.read_bytes()) != EXPECTED_CONTROL_SHA256:
        raise SystemExit("control solver hash differs from freeze")
    config = load_config()
    config["solver"]["timeout_seconds"] = 120
    config["judge"]["lean_timeout_seconds"] = 90
    config["sandbox"]["mode"] = "none"
    with tempfile.TemporaryDirectory(prefix="mathgraph-compact5-") as temp:
        intervention = Path(temp) / "submission"
        make_intervention(intervention)
        rows = []
        for dataset_name in DATASETS:
            dataset = load_dataset(
                "SAIRfoundation/equational-theories-selected-problems",
                dataset_name,
                split="train",
            )
            columns = list(dataset.column_names)
            required = {"id", "equation1", "equation2"}
            if not required <= set(columns):
                raise SystemExit(f"unexpected columns for {dataset_name}: {columns}")
            print(dataset_name, "columns=", columns, flush=True)
            for raw in dataset:
                record = dict(raw)
                problem = {
                    key: value for key, value in record.items()
                    if key not in {"truth", "label", "is_true", "answer"}
                }
                parity = int(hashlib.sha256(record["id"].encode()).hexdigest(), 16) & 1
                order = (
                    ("compact3", CONTROL.parent), ("compact5", intervention)
                ) if parity == 0 else (
                    ("compact5", intervention), ("compact3", CONTROL.parent)
                )
                outcomes = {}
                for arm, submission in order:
                    outcomes[arm] = run_arm(submission, problem, config)
                row = {
                    "configuration": dataset_name,
                    "id": record["id"],
                    "arm_order": [arm for arm, _ in order],
                    **outcomes,
                }
                rows.append(row)
                print(json.dumps(row, sort_keys=True), flush=True)
    ids = {
        arm: {row["id"] for row in rows if row[arm]["solved"]}
        for arm in ("compact3", "compact5")
    }
    summaries = {arm: summarize(rows, arm) for arm in ("compact3", "compact5")}
    gained = sorted(ids["compact5"] - ids["compact3"])
    lost = sorted(ids["compact3"] - ids["compact5"])
    nonaccepted = {
        arm: {
            status: count for status, count in summaries[arm]["judge_status_counts"].items()
            if status != "accepted"
        }
        for arm in ("compact3", "compact5")
    }
    valid_boundary = (
        len(rows) == 800
        and summaries["compact3"]["solved"] >= 788
        and summaries["compact5"]["solved"] >= 788
        and summaries["compact3"]["verdict_counts"].get("false", 0) == 400
        and summaries["compact5"]["verdict_counts"].get("false", 0) == 400
        and not lost
        and not any(nonaccepted.values())
        and summaries["compact3"]["llm_calls"] == 0
        and summaries["compact5"]["llm_calls"] == 0
    )
    output = {
        "schema": "mathgraph.residual12-full-800-compact-budget-ab-results.v1",
        "control_solver_sha256": EXPECTED_CONTROL_SHA256,
        "intervention_solver_sha256": EXPECTED_INTERVENTION_SHA256,
        "total": len(rows),
        "summaries": summaries,
        "compact5_gained_ids": gained,
        "compact5_lost_ids": lost,
        "nonaccepted_judge_statuses": nonaccepted,
        "decision": {
            "valid_boundary": valid_boundary,
            "strict_gain_no_loss": valid_boundary and bool(gained),
            "identical_accepted_sets": valid_boundary and not gained and not lost,
            "next_action": (
                "attack_marginal_gains" if valid_boundary and gained
                else "retain_compact3" if valid_boundary
                else "diagnose_boundary_failure"
            ),
        },
        "rows": rows,
    }
    args.output.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps({
        "summaries": summaries,
        "gained": gained,
        "lost": lost,
        "decision": output["decision"],
    }, indent=2, sort_keys=True), flush=True)
    if not valid_boundary:
        raise SystemExit("paired full-800 validity boundary failed")


if __name__ == "__main__":
    main()

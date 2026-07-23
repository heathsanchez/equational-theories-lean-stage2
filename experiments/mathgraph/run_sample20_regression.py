#!/usr/bin/env python3
"""Run an isolated sample_20 regression and enforce the frozen FALSE floor."""

import json
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / "submissions" / "mathgraph"
PROBLEMS = ROOT / "examples" / "problems" / "sample_20.json"


def main():
    with tempfile.TemporaryDirectory(prefix="mathgraph-sample20-") as tmp:
        output = Path(tmp) / "sample_20.json"
        command = [
            sys.executable,
            "-m",
            "pipeline.runner",
            "--submission",
            str(SOLVER),
            "--problems",
            str(PROBLEMS),
            "--output",
            str(output),
        ]
        subprocess.run(command, cwd=ROOT, check=True)
        rows = json.loads(output.read_text(encoding="utf-8"))

    expected_ids = {row["id"] for row in json.loads(PROBLEMS.read_text())}
    actual_ids = [row.get("id") for row in rows]
    assert len(rows) == 20, f"result contamination: expected 20 rows, got {len(rows)}"
    assert set(actual_ids) == expected_ids, "result IDs do not match sample_20"
    assert len(actual_ids) == len(set(actual_ids)), "duplicate result IDs"

    accepted_false = sum(
        row.get("solved") and row.get("verdict") == "false" for row in rows
    )
    accepted_true = sum(
        row.get("solved") and row.get("verdict") == "true" for row in rows
    )
    rejected = []
    for row in rows:
        for event in row.get("log", []):
            if event.get("type") != "judge":
                continue
            status = event.get("response", {}).get("status")
            if status != "accepted":
                rejected.append((row.get("id"), status))
    assert accepted_false == 8, (
        f"FALSE floor changed: expected exactly 8, got {accepted_false}"
    )
    assert accepted_true >= 1, (
        f"TRUE equality-chain floor changed: expected at least 1, got {accepted_true}"
    )
    assert not rejected, f"rejected judge calls: {rejected}"
    print(
        "sample_20 regression: "
        f"{accepted_true} accepted TRUE, 8 accepted FALSE, zero rejected judge calls"
    )


if __name__ == "__main__":
    main()

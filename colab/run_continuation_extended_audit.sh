#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON="${PYTHON:-python3}"
OUTPUT_DIR="${1:-$ROOT/colab/results_extended_30s}"
INPUT="$ROOT/colab/data/six_residuals.json"
RUNNER="$ROOT/experiments/mathgraph/paramodulator_control/run_forward_demodulation_ablation.py"
mkdir -p "$OUTPUT_DIR"

cd "$ROOT"

for condition in CN1 CN2; do
  output="$OUTPUT_DIR/${condition,,}.json"

  PYTHONDONTWRITEBYTECODE=1 "$PYTHON" "$RUNNER" \
    --input "$INPUT" \
    --conditions "$condition" \
    --timeout 30 \
    --output "$output"
done

"$PYTHON" - "$OUTPUT_DIR/cn1.json" "$OUTPUT_DIR/cn2.json" <<'PY'
import json
import sys

expected = {
    "CN1": {"evaluation_normal_0036", "evaluation_normal_0158"},
    "CN2": {"evaluation_normal_0036", "evaluation_normal_0158"},
}

for filename, condition in zip(sys.argv[1:], ("CN1", "CN2")):
    with open(filename) as handle:
        payload = json.load(handle)

    rows = payload["conditions"][condition]

    accepted = {
        row["id"]
        for row in rows
        if row.get("status") == "proved"
        and row.get("lean_status") == "accepted"
        and row.get("independent_replay") is True
        and row.get("external_plan_replay") is True
    }

    if accepted != expected[condition]:
        raise SystemExit(
            f"FAIL: {condition}: accepted={sorted(accepted)}, "
            f"expected={sorted(expected[condition])}"
        )

    print(f"{condition}: PASS ({len(accepted)}/6 accepted)")

print("PASS: extended 30-second audit")
PY

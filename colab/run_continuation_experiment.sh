#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON="${PYTHON:-python3}"
OUTPUT_DIR="${1:-$ROOT/colab/results}"
INPUT="$ROOT/colab/data/six_residuals.json"
RUNNER="$ROOT/experiments/mathgraph/paramodulator_control/run_forward_demodulation_ablation.py"
mkdir -p "$OUTPUT_DIR"

cd "$ROOT"
for condition in CN1 CN2; do
  case "$condition" in
    CN1) output="$OUTPUT_DIR/cn1.json" ;;
    CN2) output="$OUTPUT_DIR/cn2.json" ;;
    *) echo "FAIL: unsupported condition $condition" >&2; exit 1 ;;
  esac
  PYTHONDONTWRITEBYTECODE=1 "$PYTHON" "$RUNNER" \
    --input "$INPUT" \
    --conditions "$condition" \
    --output "$output"
done

"$PYTHON" - "$OUTPUT_DIR/cn1.json" "$OUTPUT_DIR/cn2.json" <<'PY'
import json
import sys

expected = {
    "CN1": {"evaluation_normal_0036", "evaluation_normal_0158"},
    "CN2": {"evaluation_normal_0158"},
}
for filename, condition in zip(sys.argv[1:], ("CN1", "CN2")):
    payload = json.load(open(filename))
    rows = payload["conditions"][condition]
    accepted = {
        row["id"] for row in rows if row.get("lean_status") == "accepted"
    }
    rejected = [
        row["id"] for row in rows
        if row.get("status") == "proved"
        and row.get("lean_status") != "accepted"
    ]
    if accepted != expected[condition] or rejected:
        raise SystemExit(
            f"FAIL: {condition}: accepted={sorted(accepted)}, "
            f"rejected={rejected}"
        )
    if not all(
        row.get("independent_replay") and row.get("external_plan_replay")
        for row in rows if row.get("lean_status") == "accepted"
    ):
        raise SystemExit(f"FAIL: {condition}: replay failure")
    print(f"{condition}: PASS ({len(accepted)}/6 accepted)")
PY

echo "PASS"

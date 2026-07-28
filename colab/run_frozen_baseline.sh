#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON="${PYTHON:-python3}"
EXPECTED_SHA="fc402fae046096d99a8c01a6848bc4030d282c7f4a90ff5e9c26c3c8d8833fe1"
EXPECTED_BYTES="313240"
SOLVER="$ROOT/submissions/mathgraph/solver.py"
INPUT="$ROOT/colab/data/smoke_normal_0158.json"
RUNNER="$ROOT/experiments/mathgraph/paramodulator_control/run_forward_demodulation_ablation.py"
TMP_DIR="$(mktemp -d)"
OUTPUT="$TMP_DIR/smoke.json"
trap 'rm -rf "$TMP_DIR"' EXIT

actual_sha="$(sha256sum "$SOLVER" | awk '{print $1}')"
actual_bytes="$(wc -c < "$SOLVER" | tr -d '[:space:]')"
test "$actual_sha" = "$EXPECTED_SHA"
test "$actual_bytes" = "$EXPECTED_BYTES"
test -f "$INPUT"
test -f "$ROOT/experiments/mathgraph/audit_stair_climber_components.py"
test -f "$ROOT/judge/verify.py"

cd "$ROOT"
PYTHONDONTWRITEBYTECODE=1 "$PYTHON" "$RUNNER" \
  --input "$INPUT" \
  --conditions F \
  --output "$OUTPUT"

"$PYTHON" - "$OUTPUT" <<'PY'
import json
import sys

payload = json.load(open(sys.argv[1]))
rows = payload["conditions"]["F"]
if len(rows) != 1:
    raise SystemExit("FAIL: smoke output must contain exactly one row")
row = rows[0]
required = {
    "status": "proved",
    "plan_ok": True,
    "independent_replay": True,
    "external_plan_replay": True,
    "lean_status": "accepted",
}
failures = {
    key: (row.get(key), expected)
    for key, expected in required.items()
    if row.get(key) != expected
}
if failures:
    raise SystemExit(f"FAIL: smoke verification mismatch: {failures}")
print(json.dumps({
    "id": row["id"],
    "independent_replay": row["independent_replay"],
    "external_replay": row["external_plan_replay"],
    "lean_status": row["lean_status"],
    "certificate_bytes": row["certificate_bytes"],
}, indent=2))
PY

echo "PASS"

#!/usr/bin/env python3
"""Schedule replay-preserving DAG-shared projection closure before deep routes."""

import build_projection_closure_specialist as base

OLD_SECONDS = "seconds = min(10.0, max(0.5, timeout / 100.0))"
NEW_SECONDS = "seconds = min(3.0, max(0.5, timeout / 1200.0))"
if base.SPECIALIST.count(OLD_SECONDS) != 1:
    raise SystemExit("projection closure seconds marker not unique")
base.SPECIALIST = base.SPECIALIST.replace(OLD_SECONDS, NEW_SECONDS, 1)
base.CALL_BEFORE = "    # Fin 2 uses the same generic finite-model evaluator, replay, symmetry,\n"
base.CALL = '''    # Generic source-only closure before finite-model and deep routes.\n    if run_projection_closure_fallback(source, target, timeout):\n        return\n\n'''

import build_projection_closure_dag_shared  # noqa: E402,F401

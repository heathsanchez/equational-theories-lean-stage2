#!/usr/bin/env python3
"""Schedule the generic source-only closure specialist before deep routes.

This wrapper changes only generic scheduling/resource bounds.  It contains no
benchmark IDs, equation IDs, stored certificates, or named target lemmas.
"""

import build_projection_closure_specialist as base

OLD_SECONDS = "seconds = min(10.0, max(0.5, timeout / 100.0))"
NEW_SECONDS = "seconds = min(3.0, max(0.5, timeout / 1200.0))"
if base.SPECIALIST.count(OLD_SECONDS) != 1:
    raise SystemExit("projection closure seconds marker not unique")
base.SPECIALIST = base.SPECIALIST.replace(OLD_SECONDS, NEW_SECONDS, 1)

# Run after the existing cheap TRUE searches, but before finite-model and deep
# routes.  A failed attempt is bounded to three seconds and cannot emit anything
# unless its expanded proof DAG replays and Lean accepts the certificate.
base.CALL_BEFORE = "    # Fin 2 uses the same generic finite-model evaluator, replay, symmetry,\n"
base.CALL = '''    # Generic source-only closure before finite-model and deep routes.\n    if run_projection_closure_fallback(source, target, timeout):\n        return\n\n'''

# This module upgrades emission to schematic learned-lemma sharing and invokes
# base.main() with the current command-line arguments.
import build_projection_closure_schematic  # noqa: E402,F401

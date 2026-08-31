#!/usr/bin/env python3
"""Instrument generic projection-closure certificates and judge responses.

Diagnostic only: no benchmark identifiers or stored certificates are embedded.
"""

import build_projection_closure_specialist as base

OLD_SECONDS = "seconds = min(10.0, max(0.5, timeout / 100.0))"
NEW_SECONDS = "seconds = min(3.0, max(0.5, timeout / 1200.0))"
if base.SPECIALIST.count(OLD_SECONDS) != 1:
    raise SystemExit("projection closure seconds marker not unique")
base.SPECIALIST = base.SPECIALIST.replace(OLD_SECONDS, NEW_SECONDS, 1)

OLD_JUDGE = '        return judge("true", code).get("status") == "accepted"\n'
NEW_JUDGE = '''        response = judge("true", code)\n        print(\n            "PROJECTION_CERTIFICATE_DIAGNOSTIC " + json.dumps({\n                "certificate": code,\n                "response": response,\n                "certificate_bytes": code_bytes,\n                "added_clauses": added,\n                "proof_nodes": proof_nodes,\n            }, sort_keys=True),\n            file=sys.stderr, flush=True,\n        )\n        return response.get("status") == "accepted"\n'''
if base.SPECIALIST.count(OLD_JUDGE) != 1:
    raise SystemExit("projection judge marker not unique")
base.SPECIALIST = base.SPECIALIST.replace(OLD_JUDGE, NEW_JUDGE, 1)

base.CALL_BEFORE = "    # Fin 2 uses the same generic finite-model evaluator, replay, symmetry,\n"
base.CALL = '''    # Generic source-only closure before finite-model and deep routes.\n    if run_projection_closure_fallback(source, target, timeout):\n        return\n\n'''

# Upgrades the expanded emitter to schematic learned-lemma sharing, then invokes
# base.main() with the current command line.
import build_projection_closure_schematic  # noqa: E402,F401

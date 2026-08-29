from pathlib import Path

P = Path('submissions/mathgraph/solver.py')
s = P.read_text()
marker = '''    # BridgeIR is a TRUE-side representation constructor. Its production\n    # portfolio remains empty unless a sealed external audit promotes it.\n'''
if marker not in s:
    raise SystemExit('compact-superposition insertion marker not found')
block = '''    # Audited pseudo-hidden fallback: the ordinary compact probe can stop\n    # before a small replayable proof becomes selectable.  This retry keeps\n    # the same inference system but relaxes structural caps, with a tiny\n    # independent time budget.  It remains fail-closed through compile + DAG\n    # replay + Lean judge in finish_compact_superposition_candidate.\n    expanded_limits = dict(COMPACT_SUPERPOSITION_PROBE)\n    expanded_limits.update({\n        "seconds": 0.15,\n        "maximum_term_size": 80,\n        "maximum_replay_term_size": 256,\n        "maximum_depth": 14,\n        "maximum_rules": 384,\n        "maximum_rounds": 64,\n        "new_clauses_per_round": 256,\n        "maximum_clauses": 12000,\n        "normalization_steps": 192,\n        "maximum_proof_nodes": 50000,\n    })\n    expanded_seconds = min(0.15, max(0.05, timeout / 100.0))\n    try:\n        expanded_search = CompactSuperposition(\n            sys.modules[__name__], source, target,\n            time.monotonic() + expanded_seconds, expanded_limits,\n        )\n        expanded_recipe = expanded_search.solve()\n    except (\n        KeyError, IndexError, MemoryError, RecursionError, TypeError, ValueError\n    ):\n        expanded_recipe = None\n    if expanded_recipe is not None and finish_compact_superposition_candidate(\n        source, target, expanded_search, expanded_recipe\n    ):\n        return\n\n'''
s = s.replace(marker, block + marker, 1)
P.write_text(s)
print('patched expanded compact-superposition retry')

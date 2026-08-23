# Developmental Experiment Graph v1

This directory externalizes the verified research state for the five remaining SAIR residuals. It is an engineering substrate, not a new theorem solver.

The graph separates three things that were previously mixed across conversation, workflow history, and result files:

1. **Raw evidence nodes** are auto-ingested from `experiments/mathgraph/results/*.json` when their `id` is one of the five scoped residuals. The result JSON remains authoritative and is content-hashed in the graph.
2. **Scientific relations** such as `RIVAL_OF`, `FAILS_AT`, `CHANGES_REPRESENTATION`, and `COMPILES_TO` are admitted only from `lineage-v1.json`. The builder never invents these relations from filenames or prose.
3. **Problem membership** is carried directly as `problem_id`, allowing graph queries without inventing another edge type.

The design is intentionally stricter than a keep/revert experiment DAG. Negative results remain first-class nodes because a result can sharpen a residual, eliminate a rival, or expose a representation/constructor boundary without improving the headline theorem score.

## Build

```bash
python experiments/mathgraph/developmental_graph/build_graph.py
```

Outputs:

- `developmental-graph-v1.json` — typed evidence graph.
- `developmental-graph-summary-v1.json` — coverage and census suitable for CI/controller queries.

## Current scientific role

V1 is the memory substrate only. It does **not** autonomously choose experiments. The next descaffolding test is to give a controller only this graph plus the frozen method/routing rules and ask it to recover the current residual, surviving rivals, and smallest discriminating next experiment without reading conversation history.

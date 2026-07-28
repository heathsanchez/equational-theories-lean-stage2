# MathGraph Paramodulator-Control Handoff

## Immutable state

- Repository: `https://github.com/heathsanchez/equational-theories-lean-stage2.git`
- Research branch: `mathgraph/context-calculus-research`
- Frozen research snapshot:
  `d8c40c8608db034436273b25846b51fbea0f7655`
- Snapshot subject: `record paramodulator control research freeze`
- Production solver: `submissions/mathgraph/solver.py`
- Production SHA-256:
  `fc402fae046096d99a8c01a6848bc4030d282c7f4a90ff5e9c26c3c8d8833fe1`
- Production size: `313240` bytes
- Frozen released-set result: **794/800**
  (`394 TRUE + 400 FALSE`, six unresolved TRUE rows)
- LLM calls: zero

The production solver was not edited during any paramodulator-control
experiment or during this handoff.

## Completed experiments

1. Frozen baseline and proof-component audit.
2. Retrieval-equivalence tests.
3. B/F factorial forward-demodulation test.
4. Independent plan replay and official Lean verification.
5. Seven corruption tests; every corrupted certificate was rejected.
6. First sealed 100 TRUE / 100 FALSE transfer audit.
7. Scheduler S and local-demodulation FS comparison.
8. Second sealed 100 TRUE / 100 FALSE scheduler audit.
9. Proof-ancestry causal analysis.
10. Global demodulation budgets K1/K2/K4 and capped variants.
11. Minimal clause quotient Q, all-representative QA and merge QM.
12. Paired S/FS continuation-effect traces.
13. Nineteen single-rewrite counterfactual deletions:
    16 replaceable, three necessary under frozen search.
14. Operation-relative QR representation.
15. Lazy selection-time QL representation.
16. Strict immediate continuation novelty CN1.
17. One-contraction/one-inference corridor CN2.
18. CN1 proof-ancestral materialization deletion; the proof remained
    independently replayed and officially Lean accepted.

## Rejected hypotheses

- Canonical normal forms are universally better search representations.
- Eager forward demodulation transfers safely.
- Local demodulation plus scheduling preserves saturation breadth.
- A fixed global rewrite budget recovers all three residual contraction paths.
- Raw/cheapest/goal-facing clause representatives are sufficient.
- Safe passive equality merging produces a useful quotient density.
- Operation-relative representative selection alone is sufficient.
- Lazy representative materialization alone is sufficient.
- Proof ancestry is a strong causal activation signal.
- Current-frontier operational novelty identifies valuable contractions.
- One contraction plus one speculative inference identifies the connected
  `normal_0040` corridor.

## Current scientific conclusion

Logically equivalent clauses are not interchangeable search states.
Demodulation value lies in the continuation it makes reachable, but forward
enumeration of current-frontier continuation novelty is still too broad and
destroys scheduler throughput. CN1 materialized 43 contractions; only one
entered accepted proof ancestry, and deleting it preserved an officially
accepted proof. CN2 materialized 38 contractions, found no qualifying corridor
preview and used no contraction in accepted proof ancestry.

Do not widen forward lookahead and do not promote CN1 or CN2.

## Exact next hypothesis

**Backward continuation requirements.**

Begin from the denied goal, describe a missing inference interface using only
generic role/side/path/repetition constraints, index that request against the
active frontier, and materialize at most one verified representation capable
of satisfying it. The three necessary `normal_0040` transitions may calibrate
diagnostics but must never become equation-specific production rules.

No backward-continuation implementation exists in this handoff.

## Reproduction

From the repository root after bootstrap:

```bash
bash colab/run_frozen_baseline.sh
```

Reproduce both frozen continuation experiments:

```bash
bash colab/run_continuation_experiment.sh /tmp/mathgraph-cn-reproduction
```

Equivalent explicit CN1 command:

```bash
python experiments/mathgraph/paramodulator_control/run_forward_demodulation_ablation.py \
  --input colab/data/six_residuals.json \
  --conditions CN1 \
  --output /tmp/mathgraph-cn1.json
```

Equivalent explicit CN2 command:

```bash
python experiments/mathgraph/paramodulator_control/run_forward_demodulation_ablation.py \
  --input colab/data/six_residuals.json \
  --conditions CN2 \
  --output /tmp/mathgraph-cn2.json
```

## Starting a future experiment safely

1. Verify `git status --short` is empty.
2. Verify solver hash and size with `bash colab/run_frozen_baseline.sh`.
3. Create a new branch from the immutable handoff checkout.
4. Write and commit a preregistration before executing development rows.
5. Place new code under `experiments/mathgraph/`; do not edit
   `submissions/mathgraph/solver.py`.
6. Use new result paths; never overwrite these committed artifacts.
7. Keep all candidates non-terminal until independent replay and official Lean
   verification succeed.
8. Require the frozen six-row gate before any sealed external audit.

## Important paths

- Main runner:
  `experiments/mathgraph/paramodulator_control/run_forward_demodulation_ablation.py`
- Independent replay:
  `experiments/mathgraph/audit_stair_climber_components.py`
- Soundness specification:
  `experiments/mathgraph/paramodulator_control/demodulation_soundness_spec.md`
- Continuation causal analysis:
  `experiments/mathgraph/paramodulator_control/continuation_effect_analysis.json`
- Clause-state specification:
  `experiments/mathgraph/paramodulator_control/continuation_aware_clause_state_spec.md`
- CN preregistration:
  `experiments/mathgraph/paramodulator_control/continuation_novelty_preregistration.json`
- CN1 result:
  `experiments/mathgraph/paramodulator_control/six_residual_continuation_novelty_cn1_results.json`
- CN2 result:
  `experiments/mathgraph/paramodulator_control/six_residual_continuation_novelty_cn2_results.json`
- Counterfactual:
  `experiments/mathgraph/paramodulator_control/continuation_novelty_counterfactual.json`
- Final decision:
  `experiments/mathgraph/paramodulator_control/continuation_novelty_summary.json`
- Source rows: `colab/data/six_residuals.json`
- Environment: `requirements-lock.txt`, `lean-toolchain`,
  `environment_manifest.json`
- Compact archive:
  `colab/mathgraph_paramodulator_control_bundle.tar.gz`

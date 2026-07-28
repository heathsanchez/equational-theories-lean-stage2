# MathGraph Paramodulator-Control Colab Handoff

This directory reproduces the frozen research state without changing the
production solver. No API key or other credential is required.

## One-command bootstrap

In a fresh Colab cell:

```bash
!curl -fsSLo /content/bootstrap_mathgraph.py \
  https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/context-calculus-research/colab/bootstrap_mathgraph.py
!python /content/bootstrap_mathgraph.py
```

The bootstrap clones the repository, checks out its pinned immutable handoff
commit, installs the pinned Lean and Python environments, verifies the frozen
solver hash and byte size, then runs the one-row proof/replay/Lean smoke test.
It prints `PASS` only when every stage succeeds.

## Commands after bootstrap

```bash
%cd /content/mathgraph-stage2
!bash colab/run_frozen_baseline.sh
!bash colab/run_continuation_experiment.sh /content/mathgraph-results
```

The continuation command reproduces CN1 and CN2 in fresh output files. It does
not overwrite the committed results.

## Files

- `bootstrap_mathgraph.ipynb`: uploadable Colab notebook.
- `bootstrap_mathgraph.py`: fail-closed clone/install/verify driver.
- `run_frozen_baseline.sh`: solver hash/size plus one-row certificate smoke.
- `run_continuation_experiment.sh`: exact six-row CN1/CN2 reproduction.
- `data/`: repository-relative source rows used by those commands.
- `experiment_bundle_manifest.json`: path, size and SHA-256 for every archive
  member.
- `mathgraph_paramodulator_control_bundle.tar.gz`: compact offline experiment
  bundle. It excludes caches, build products, ATP outputs, sealed labels,
  credentials and unrelated experiment artifacts.

## Frozen invariants

- Production solver:
  `submissions/mathgraph/solver.py`
- SHA-256:
  `fc402fae046096d99a8c01a6848bc4030d282c7f4a90ff5e9c26c3c8d8833fe1`
- Size: `313240` bytes
- Frozen released-set result: `794/800` (`394 TRUE + 400 FALSE`)
- Research snapshot commit:
  `d8c40c8608db034436273b25846b51fbea0f7655`
- Exact Colab checkout commit:
  `8b09788b4c3ad4e09203f26c891055d4a5d9b7eb`

See
`experiments/mathgraph/paramodulator_control/HANDOFF.md`
for the complete experiment ledger and scientific conclusion.

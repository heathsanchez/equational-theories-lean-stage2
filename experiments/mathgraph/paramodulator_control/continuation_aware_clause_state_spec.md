# Continuation-Aware Clause State: Diagnostic Specification

Status: `CANDIDATE` research representation. It is not production code and
does not establish any new accepted claim.

## Causal finding

The paired scheduler/demodulation traces falsify the assumption that
theorem-equivalent clauses are interchangeable search states.

- S and FS diverge after only 2–4 selected clauses on the six residuals.
- In the three FS proofs, 19 demodulations occur in proof ancestry.
- Single-transition deletion leaves 16/19 variants with independently
  replayed, officially accepted Lean proofs.
- Three transitions are necessary under the frozen search. They form one
  connected contraction chain in `evaluation_normal_0040`.
- On the external scheduler audit, FS adds two accepted proofs but loses 28
  accepted S proofs. Representative paired reruns reproduce both gains and
  two losses.

Proof ancestry is therefore insufficient as a retention signal. Most ancestry
rewrites are replaceable, while a small connected subset is proof-enabling.

## Falsified representations

1. Eager local demodulation: useful on three residuals but consumes the
   inference frontier.
2. Cheapest canonical representative: loses structurally useful overlap
   positions.
3. At-most-three raw/cheap/goal representatives scheduled as one class:
   only one of six residuals.
4. Operation-relative source/target representative selection with eager
   materialization (`QR`): one of six.
5. Lazy operation-relative materialization (`QL`): two of six, including the
   new accepted `evaluation_normal_0036`, but below the 3/6 gate.

## Required next representation

The next clause state should retain continuation signatures, not merely
syntactic representatives:

```text
ClauseState
  shared age
  raw proof-carrying representation
  bounded derived representations
  per-representation superposition-source positions
  per-representation superposition-target positions
  denied-goal ancestry and overlap paths
  proof paths between representations
  observed transformation cost
  observed continuation delta
```

A transformation is materialized only after the state is selected and only
when it enables an operation that the retained representations cannot already
perform. Weight reduction alone is not sufficient.

## Next falsification test

Use the frozen six rows first. For every selected state:

1. compute the raw representative's eligible source and target positions;
2. propose at most one verified contraction;
3. compute positions gained and lost by that contraction;
4. retain it only if it enables a previously impossible unification with an
   active clause or the denied goal;
5. expose raw and contracted forms only for the operations each uniquely
   enables;
6. preserve shared age and charge one scheduling event to the state.

Promotion to an external sealed audit requires at least 3/6 officially
accepted residual proofs with independent replay. Production remains frozen
until a later holdout-positive result.

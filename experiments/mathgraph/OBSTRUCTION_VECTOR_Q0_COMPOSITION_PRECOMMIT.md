# O5-0014 obstruction-vector protocol — bounded Q0 and composition ordering

Target: `evaluation_order5_0014` after `PASS_UNIFIED_PROGRESS`.

## Purpose

Diagnose the post-Stage-2 residual without making unbounded non-existence claims and without assuming that independently diagnosed refinements compose or commute.

Starting verified state `S2` has both target endpoints present, target components unjoined, and cross-component distance 12.

## Q0 — bounded specification validity

The provisional residual predicate is:

`K3(E) := E.replay_valid and (E.joined or (E.cross_distance is not None and E.cross_distance < 12))`.

Do **not** claim this is globally necessary.

Freeze a bounded effect probe universe `Phi_B` generated from the current atomic intervention pool and all replay-valid one-step state effects reachable under the frozen resource budget. For every probe, record the effect vector:

- target lhs present
- target rhs present
- joined
- cross distance
- number of live component boundary terms
- number of replay-valid unifiable cross-component boundary pairs
- number of addressable target-context occurrences
- number of residual-required motif occurrences

A Q0 counterexample is any replay-valid intervention whose scalar `K3` is false but which strictly improves at least one non-distance potential coordinate without worsening all others.

Report only:

- `K3_COUNTEREXAMPLE_IN_PHI_B`, or
- `K3_SURVIVED_PHI_B`

Never strengthen `K3_SURVIVED_PHI_B` to a global necessity claim.

## Q1 — bounded atomic admissibility

Freeze an explicitly enumerated atomic universe `H_B` using the existing replay-valid atomic families available at `S2` under the same resource cap.

Report whether `K3 ∩ H_B` is empty. This is only a bounded carrier result.

## Q2 — representation / generator coverage

Partition `H_B` by atomic family and verified effect signature. Record which effect signatures required by `K3` are absent from each family and from the union.

Do not infer global non-existence from absence in `H_B`.

## Q3 — addressability

Measure whether replay-valid consequences already latent in the source-law closure fail to instantiate because the required endpoint, substitution term, context path, or component anchor is not addressable in the current state interface.

Report addressability evidence independently of Q1/Q2.

## Q4 — atomicity / synergy

Search bounded ordered pairs of atomic interventions `(d1,d2)` with each individual intervention failing `K3`, but the composition satisfying `K3` when applied sequentially.

A positive result is `ATOMICITY_OBSTRUCTION_IN_BOUND`: the continuation unit is too small within the frozen bound.

A negative result is only `NO_BOUNDED_SYNERGY_FOUND`.

## Non-exclusive obstruction vector

Return all independently supported coordinates:

`O(rho3) = (specification, bounded_atomic, representation, addressability, atomicity)`.

Coordinates are not mutually exclusive.

## Composition and ordering rule

If multiple refinement dimensions are implicated, do **not** construct a synthetic `address+program` intervention and do not assume commutativity.

For any two diagnosed refinement operators `F` and `G`, test both legal sequential orders where well-typed:

`S --F--> S_F --G--> S_FG`

and

`S --G--> S_G --F--> S_GF`.

Record:

- whether each ordering is well-typed,
- intermediate residual after the first refinement,
- final closure/effect,
- whether `FG` and `GF` are verifier-equivalent,
- ablations of the first and second refinement separately.

Classify as one of:

- `COMMUTE_WITHIN_BOUND`
- `ORDER_SENSITIVE_F_THEN_G`
- `ORDER_SENSITIVE_G_THEN_F`
- `ONLY_ONE_ORDER_WELL_TYPED`
- `NO_COMPOSED_PROGRESS`

A combined refinement may be treated as one carrier element only in a later experiment after a common carrier and cost for that composite object are prospectively defined.

## Claim boundary

This protocol can establish bounded counterexamples, bounded empty intersections, bounded synergy, and ordering dependence. It cannot establish global necessity, global atomic impossibility, or global commutativity.
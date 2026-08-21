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

## Q4 — bounded atomicity / synergy

This test is explicitly bounded and must not be interpreted as exhaustive over `H_B × H_B`.

From the individually non-`K3` interventions in `H_B`, sort by the same frozen atomic proof cost used by the unified refinement experiment. Let `P24` be the first 24 such interventions (or all of them if fewer than 24 exist). Exhaust all ordered distinct pairs in `P24 × P24`, i.e. at most `24 × 23 = 552` ordered compositions.

A synergistic pair is `(d1,d2)` such that:

- `K3(E(S2,d1)) = false`,
- `K3(E(S2,d2)) = false`, and
- `K3(E(S2 + d1 + d2)) = true` when applied sequentially in that order.

A positive result is `ATOMICITY_OBSTRUCTION_IN_BOUND`: the atomic continuation unit is too small for at least one verified two-step effect within this frozen pair slice.

A negative result is only `NO_BOUNDED_SYNERGY_FOUND_IN_P24xP24`. It must **not** be strengthened to `no synergy in H_B × H_B`, `atomicity is not the obstruction`, or any global claim.

The result artifact must record `|P24|` and the maximum ordered-pair count implied by that bound.

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

## Stage-3 causal ablation rule for any later closure experiment

This diagnostic does not itself select a Stage-3 winner or claim Stage-3 theorem closure. If a subsequent Call-3 experiment selects an atomic `d3*` from the accumulated state `S2` and obtains closure, the causal ablation must remove **only** `d3*` while preserving every Stage-1 and Stage-2 intervention:

`closure(S2 + d3*) = true`

and

`closure((S2 + d3*) - d3*) = closure(S2) = false`.

Re-ablating Stage 1, Stage 2, or the whole chain does not count as evidence that Call 3 itself caused closure.

## Claim boundary

This protocol can establish bounded counterexamples, bounded empty intersections, bounded synergy within the explicitly frozen `P24 × P24` slice, and ordering dependence. It cannot establish global necessity, global atomic impossibility, absence of synergy outside that pair slice, or global commutativity.
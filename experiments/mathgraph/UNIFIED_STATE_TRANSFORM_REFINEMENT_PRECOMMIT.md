# Unified state-transform refinement — frozen protocol

Target: `evaluation_order5_0014`.

## Strong question

Can constructor refinement and attachment refinement be implemented as two calls to the **same typed operator** over the same carrier, with the same cost function and the same admissibility form?

The carrier is not a term grammar or a context path. It is the set of finite **replay-verified equality interventions** that can be installed into a proof state without changing the trusted inference base.

A state is `S = (source, target, installed, closure-geometry)`.

An intervention is one object type throughout:

`Delta = (proof_DAG, resulting equality, provenance)`

with the invariant that `proof_DAG` replays to the original source law.

Applying `Delta` means installing that replay-verified equality into the current state and recomputing/verifying its effect on the state closure geometry.

## One cost function

The same lexicographic intervention complexity is used on every call:

`d(Delta) = (proof_DAG_nodes, lhs_term_size + rhs_term_size, root_derivation_depth)`.

No stage-specific graph-distance or context-path term appears in the cost.

## One effect-signature type

Every intervention is evaluated into the same effect record:

- replay-valid;
- newly introduced residual-required subterms;
- target lhs present;
- target rhs present;
- target components joined by the installed equality graph;
- cross-component structural distance after the intervention where defined;
- full bounded closure result when the selected intervention is validated.

## One admissibility form

Each residual compiles to a predicate over the same effect-signature type:

`K(rho)(E(S, Delta)) -> Bool`.

Call 1 residual: motif/grammar residual.  `K1` requires introduction of at least one residual-required missing target subterm.

Call 2 residual: component-disconnection residual computed **after installing the Call 1 winner**.  `K2` requires either direct joining of the live target components or strict reduction of their verified cross-component structural distance.

The predicates differ because the residuals differ, but their type and satisfaction relation are identical: predicates over verified intervention effects.

## One refine implementation

Both stages must invoke the same function:

`refine(S, rho, candidate_interventions) = argmin_d { Delta : K(rho)(E(S,Delta)) }`.

The candidate proposer may be state/residual conditioned, but every proposal has the same `Intervention` type and passes through the same replay filter, effect map, admissibility call, and cost function.

## Candidate sources

Call 1 candidate interventions are drawn from the already frozen replay-valid residual-derived families R/M/J/C.

Call 2 candidate interventions are replay-valid context-lift/component-anchor proposals generated from the updated state after Call 1. They are not a new carrier: they are converted to the same intervention type and evaluated by the same `refine` routine.

## Empirical gates

The experiment records type/cost/predicate implementation identity by code path, then tests:

1. frozen state does not close the theorem;
2. Call 1 has a finite admissible intervention and selects the minimum by the universal `d`;
3. installing Call 1 changes the state and yields a component-disconnection residual if closure still fails;
4. Call 2 uses the exact same `refine` function and exact same `d`;
5. Call 2 has a finite admissible intervention;
6. the selected Call 2 intervention is replay-valid and gives the predicted cut effect;
7. full bounded closure is tested after both interventions;
8. ablation of Call 2 while retaining Call 1 removes any Call-2-specific closure gain.

## Decision

- `PASS_STRONG_UNIFIED_CLOSURE`: same typed operator twice, both nontrivial admissible refinements, closure only after Call 2, and Call-2 ablation loses closure.
- `PASS_UNIFIED_PROGRESS`: same typed operator twice with nontrivial admissible refinements and verified predicted effects, but theorem remains open.
- `STAGE1_ONLY`: Call 1 refines but Call 2 has no admissible intervention in the frozen bounded proposal pool.
- `NO_STAGE1_REFINEMENT`: Call 1 has no admissible intervention.

## Claim boundary

A positive result establishes identity of the refinement **operator type, cost function, effect-signature type, and satisfaction form** for these two actual residual stages in a bounded SAIR experiment. It does not prove that all possible developmental residuals admit this carrier or that the candidate proposers are complete.
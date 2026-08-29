# Stair-climber integration decision

## Decision: SPECIALIST INTEGRATION

Import only two independently useful capabilities:

1. the bounded given-clause paramodulation engine with congruence proof plans;
2. the equation-blind finite table bank plus the general affine right-offset
   model found by the audited finite-model engine.

Do not import the full flagship orchestrator, public certificate manifest,
known-counterexample lookup, completion stage as a search route, LLM tail, or
public problem recipes.

## Evidence

On the 33 current TRUE opportunities, the paramodulation specialist produced
27 candidates. A separately authored replayer checked all 27 proof plans, and
the official Lean judge accepted the exact 27 emitted certificates. It emitted
no candidate on the 16 matched FALSE controls.

Standalone completion found 12/33, all already covered by paramodulation, so
its marginal gain was zero.

Across the 16 current FALSE opportunities, the 139-table bank found 15 with
zero contamination on 33 TRUE controls. All 15 certificates were officially
accepted. A generic affine right-offset model found the final FALSE row and
its MathGraph certificate was officially accepted. The full external CE engine
also found 16/16 diagnostically, but added no coverage beyond this smaller
portfolio.

The verified projected union is:

| Solver | TRUE | FALSE | Total |
|---|---:|---:|---:|
| Frozen MathGraph | 367 | 384 | 751 |
| Specialist gains | +27 | +16 | +43 |
| Verified union | 394 | 400 | 794 |
| Remaining | 6 | 0 | 6 |

## Production order

Keep every existing deterministic route unchanged. On rows that remain
unresolved:

1. try the external table bank equation-blindly;
2. require complete source satisfaction, a concrete target witness, and
   independent semantic replay;
3. emit the existing generic finite certificate;
4. after existing TRUE routes, run bounded paramodulation;
5. independently replay its entire equality plan;
6. emit Lean only if both replayers agree.

The imported routes contain no LLM calls and no ID-, hash-, label-, or
benchmark-based routing.

## Next experiment

The full flagship's deep-constancy stage emits a TRUE candidate for each of
the six remaining rows, but all six candidates are officially rejected: their
`lem1` declarations use an underscore whose type Lean cannot synthesize.
The next experiment is therefore precise. Reconstruct the intended compound
source instance, infer its explicit equality endpoint, independently replay
the inner rewrite, and feed that typed lemma into the existing proof DAG. Do
not promote the present placeholder-based certificates.

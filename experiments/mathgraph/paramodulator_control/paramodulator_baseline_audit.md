# Frozen paramodulator baseline audit

## Scope

The audited engine is the embedded Stair-climber specialist in the frozen
313,240-byte MathGraph solver. Production SHA-256 is
`fc402fae046096d99a8c01a6848bc4030d282c7f4a90ff5e9c26c3c8d8833fe1`.
This research fork does not modify it.

## Clause representation

- One unit equality or disequality per clause.
- Terms are variables or applications of the single binary magma operation.
- Target variables are replaced by rigid Skolem constants in the denied goal.
- Variables in derived clauses are alpha-normalized.
- Duplicate detection uses an alpha-normalized unordered equality key.
- Optional tautology and forward-subsumption deletion exist but are disabled
  in the frozen production configuration.
- Every derived clause stores a Prover9-shaped `para` justification with source
  clause, orientation, target clause, literal side, and term path.

## Inference power

- The universally quantified source equality is the sole positive axiom.
- The target is negated and Skolemized as a negative unit equality.
- Positive unit equalities paramodulate into positive and negative clauses.
- Rewriting at variable positions is attempted by the underlying enumerator;
  failed or forbidden unifications simply produce no clause.
- Both literal sides and all syntactic subterm paths are scanned.
- Equality closure occurs when the two sides of a negative clause unify under
  rigid target constants.
- There is no dedicated factoring rule.
- Congruence is reconstructed later from recorded contextual rewrite paths.

## Scheduling

- Passive clauses are held in one heap.
- Priority is clause weight plus derivation depth, with insertion sequence as
  the deterministic tie-breaker.
- There is no age quota.
- There is no protected goal-relevance quota.
- Negative clauses may receive a configurable bias; production uses zero.
- Each selected clause receives a fresh budget of 300 inference-pair attempts.
- Newly generated clauses can participate in the live inference lists.

## Retrieval

- Positive source equalities and target clauses are stored in flat lists.
- Candidate pairs are found by repeated scans.
- Every selected pair enumerates both target literal sides and every subterm
  path, then invokes unification.
- There is no discrimination, path, substitution, or demodulator index.
- There is no simplification cache.

## Missing saturation controls

The baseline has no forward or backward demodulation. Consequently large
derived clauses remain in the passive set, duplicates are recognized only
after exact alpha-normalization, and useful descendants compete with
unsimplified ancestors.

## Frozen six-row baseline

The prior isolated run produced:

| row | generated | processed | exit |
|---|---:|---:|---|
| `evaluation_hard_0196` | 8,000 | 180 | clause cap |
| `evaluation_normal_0036` | 7,484 | 292 | timeout |
| `evaluation_normal_0040` | 3,819 | 295 | timeout |
| `evaluation_normal_0158` | 8,000 | 243 | clause cap |
| `evaluation_order5_0014` | 383 | 202 | timeout |
| `evaluation_order5_0042` | 2,276 | 272 | timeout |

The original engine does not expose retained, duplicate-deleted, peak-active,
or peak-passive counters. Phase-one diagnostic condition B records the fields
it can observe without changing production; condition F adds explicit counters.

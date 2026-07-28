# Six-residual obstruction atlas

This is a diagnostic record. It does not alter the production solver or count
external ATP output as a MathGraph proof.

## Decisive result

Vampire 5.0.1 proves all six remaining TRUE implications in 0.015–0.085
seconds. Every proof uses superposition, and every proof uses at least one
forward-demodulation step. The two largest traces use 25 and 41
forward-demodulation steps.

The frozen MathGraph paramodulator already denies the target and performs
goal-grounded paramodulation, but it has no demodulation stage. Its selected
clause priority is essentially term weight plus derivation depth. On the six
rows it generates between 383 and 8,000 clauses, processes only 180–295, and
either reaches the clause cap or times out.

This makes the common obstruction much narrower than a missing representation
or latent mathematical concept:

```text
available goal-grounded superposition
→ insufficient simplification and clause selection
→ useful refutation buried by generated clauses
```

## Evidence hierarchy

| System or component | Six-row evidence | Trust status |
|---|---|---|
| Frozen MathGraph | 0/6 | production replayed |
| Stair paramodulation | 0/6 | portfolio exhausted |
| Stair completion | 0/6 | no candidate |
| Flagship deep constancy | claims 6/6 | all six Lean-rejected |
| Independent context reconstruction | one valid prefix, 0 proofs | explicit replay |
| Vampire 5.0.1 | 6/6 | external ATP proofs, not Lean certificates |

The direct-instance, two-step, public completion, TWEE-521, and versioned
public-certificate corpora contain no claims about these released-evaluation
rows. They remain useful proof-shape controls but cannot be entered as row-level
successes in this ledger.

## Row summary

| Row | Vampire superposition | Vampire demodulation | MathGraph exit | Diagnosis |
|---|---:|---:|---|---|
| `evaluation_hard_0196` | 38 | 25 | 8,000-clause cap | demodulation/search control |
| `evaluation_normal_0036` | 13 | 1 | timeout | clause selection |
| `evaluation_normal_0040` | 18 | 4 | timeout | demodulation/search control |
| `evaluation_normal_0158` | 7 | 1 | 8,000-clause cap | clause selection |
| `evaluation_order5_0014` | 28 | 16 | timeout | demodulation/search control |
| `evaluation_order5_0042` | 60 | 41 | timeout | demodulation/search control |

## What the buckets invalidate

The buckets do not support six separate residual constructors. They also do
not support the placeholder-based deep-constancy route: five advertised inner
contractions have no matching subterm, and the sole valid prefix does not prove
its target.

The external ATP traces show that ordinary superposition is sufficient for all
six. The missing capability is the engineering around it: proof-carrying
demodulation, indexed retrieval, and a better given-clause schedule.

## Next bounded experiment

Use a diagnostic fork of the existing paramodulator and add, separately:

1. forward demodulation;
2. backward demodulation;
3. deterministic age/weight alternation with a goal-clause quota;
4. indexed subterm and demodulator retrieval.

Every simplification must remain in the proof DAG. First require at least three
of the six to replay and receive official Lean acceptance. Then freeze the
configuration and test on unused, label-hidden TRUE opportunities. Do not
import Vampire proof traces or add residual-specific routing.

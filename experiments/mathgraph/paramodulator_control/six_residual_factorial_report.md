# Six-residual saturation-control report

## Result

The first causal gate passes without changing scheduling, retrieval, or
backward simplification:

```text
B: 0/6
F: 3/6 independently replayed and officially Lean accepted
```

Accepted under forward demodulation:

- `evaluation_hard_0196`
- `evaluation_normal_0040`
- `evaluation_normal_0158`

There were three judge calls and all three were accepted.

## Causal interpretation

Forward demodulation is present on every accepted proof ancestry:

| row | ancestry superpositions | ancestry demodulations |
|---|---:|---:|
| `evaluation_hard_0196` | 5 | 11 |
| `evaluation_normal_0040` | 6 | 6 |
| `evaluation_normal_0158` | 4 | 5 |

The result is not merely a runtime correlation. Condition B and F share the
same source axiom, denied goal, superposition implementation, weight-plus-depth
scheduler, exhaustive flat retrieval, clause limit, term limits, pair budget,
and wall time. The added demodulation nodes lie on the final accepted proof
ancestries.

Search contraction is substantial:

| row | B generated/processed | F generated/processed |
|---|---:|---:|
| `evaluation_hard_0196` | 8,000 / 180 | 1,649 / 6 |
| `evaluation_normal_0040` | 4,419 / 327 | 471 / 6 |
| `evaluation_normal_0158` | 8,000 / 243 | 865 / 4 |

## Replay

Each simplification is a recorded paramodulation node. The external plan
verifier and the separately authored MathGraph plan replayer both accepted all
three traces. Seven corruption classes were tested and rejected, including
altered rule, orientation, path, substitution, parent, missing step, and final
target.

## Remaining rows

Forward demodulation alone does not solve:

- `evaluation_normal_0036`
- `evaluation_order5_0014`
- `evaluation_order5_0042`

This does not justify backward demodulation or indexing yet. The preregistered
interpretation is that simplification is the primary missing capability.
Transfer was subsequently tested on a sealed, content-hash-fresh 100 TRUE plus
100 matched FALSE audit. Condition F added zero proofs beyond B and lost 22 B
proofs because 180,881 eager simplifications starved given-clause processing.
Thus the causal six-row finding remains valid, but the eager global control is
rejected for production. The next experiment must control when and where
demodulation fires; larger budgets or backward demodulation are not justified.

# Production promotion decision

## Decision: rejected for production

Forward demodulation passed the six-row causal gate with three independently
replayed, officially accepted proofs. The subsequent sealed transfer audit,
however, decisively rejected the eager global implementation:

| condition | accepted TRUE | false-control proofs |
|---|---:|---:|
| frozen baseline B | 31/100 | 0/100 |
| forward demodulation F | 9/100 | 0/100 |

Every F proof was already proved by B. F therefore added zero external proofs
and lost 22 baseline proofs across 21 source families. The failure is not
logical unsoundness: all generated proofs replayed and all Lean calls were
accepted. It is a control failure. Eager demodulation generated 180,881
explicit simplification steps and reduced processed given clauses from 28,070
to 1,633 under the same time limits.

The production solver therefore remains byte-for-byte unchanged at:

```text
fc402fae046096d99a8c01a6848bc4030d282c7f4a90ff5e9c26c3c8d8833fe1
```

The six-row result establishes that simplification is causally useful, but the
sealed result establishes that unconditional eager simplification is not a
production route. The next isolated experiment should test bounded or
given-clause-local demodulation control, with B and this frozen F serving as
comparators. It must reduce simplification volume without changing the
proof-carrying rule or retrieval semantics.

## Scheduler and bounded-local follow-up

The preregistered second experiment tested deterministic age/weight scheduling
(`S`) and the same scheduler combined with at most four local rewrites from the
eight newest demodulators (`FS`).

On the six motivating residuals:

```text
S:  0/6
FS: 3/6
```

FS recovered exactly the three rows already recovered by eager F. A new sealed
audit excluded all 200 rows from the first transfer audit by normalized content
hash and selected another 100 TRUE plus 100 matched FALSE rows.

| condition | accepted TRUE | false-control proofs |
|---|---:|---:|
| S | 41/100 | 0/100 |
| FS | 15/100 | 0/100 |

FS added two proofs beyond S across two source families, below the frozen
five-proof, three-family promotion threshold. It also lost 28 S proofs and
performed 121,281 explicit demodulations. A per-generated-clause rewrite cap
therefore does not control total rewrite work.

Neither S nor FS is promoted: S fails the six-row causal gate, while FS fails
the external transfer gate. Production remains byte-for-byte frozen. The next
valid experiment should move the simplification budget to the invocation or
selected-given-clause level and use proof-ancestry value to decide which raw
children are eligible. Indexing can then reduce retrieval cost, but larger
rewrite budgets are not justified.

## Independent scheduler audit correction

Scheduler-only S was reconsidered independently of the demodulation residual
gate. Its sealed improvement from 31 to 41 proofs is real evidence of broad
transfer. However, the production solver already accepts 794 of the released
800 rows, and S proves none of the only six unresolved rows. When appended as a
safe fallback it therefore adds zero released-benchmark verdicts and cannot
meet the independent requirement of at least one new accepted TRUE. No
production integration was attempted.

## Globally budgeted dual-retention experiment

The next preregistered matrix retained every raw child, added simplified
siblings only under a structural goal gate, and shared rewrite budgets across
all children of one selected given clause. It tested K1, K2, K4, G64, G128 and
G256 combinations without changing time or clause limits.

No single condition met the 3/6 development gate:

- K1 proved `evaluation_normal_0040` and `evaluation_normal_0158`;
- K2/K4 proved `evaluation_hard_0196` and `evaluation_normal_0158`;
- capped variants proved one or two rows;
- no condition proved `evaluation_normal_0036` or either order-5 residual.

K1 reduced the six-row demodulation volume from FS's 6,755 to 575, but retained
only 52.7% of S's selected-clause throughput, below the required 70%. Because
the primary three-residual condition failed, no third sealed audit was run.

This falsifies a fixed numerical budget as the missing control. The next
experiment should test semantics-preserving indexed retrieval and allocate a
small rewrite budget only when the selected demodulator actually matches a
goal-relevant child. Budget should be charged after indexed match discovery,
not while exhaustively scanning children.

## Proof-carrying clause quotient diagnostic

A minimal multi-representative saturation IR was tested next. Each scheduled
class shared one age and retained at most a raw, cheapest and most
goal-relevant replay-connected representative. Three policies were compared:
one exposed representative (`Q`), all strategic representatives under one
class event (`QA`), and passive cross-class union through an identical verified
representative (`QM`).

All three solved only `evaluation_normal_0158` (1/6). The decisive diagnostic
was quotient density:

```text
QM classes created:       18,104
safe passive class merges:    73
merge fraction:             0.4%
```

Thus the proof-carrying quotient machinery is sound enough for continued
research, but the current rewrite discovery leaves more than 99% of generated
classes as singletons. Scheduling classes instead of clauses cannot compress a
frontier whose equivalences have not been discovered.

No sealed audit or production integration is justified. Indexed retrieval and
replayed canonicalization must first demonstrate substantially higher
equivalence discovery at lower cost. The quotient should remain an isolated
research IR until that prerequisite passes exhaustive retrieval-equivalence
tests.

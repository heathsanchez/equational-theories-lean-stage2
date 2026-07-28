# Continuation Novelty Decision

CN1 and CN2 are rejected. Neither advances to an external audit or production.

CN1 proves two of six residuals (`normal_0036` and `normal_0158`). CN2 proves
only `normal_0158`; it loses the new lazy-state `normal_0036` proof and does not
recover the connected `normal_0040` contraction corridor.

The cost controls pass only in the narrow demodulation sense: CN1 performs 43
and CN2 38 contractions, both below 5% of the six-row FS total. They fail the
more important breadth control. CN1 processes 31.2% and CN2 34.3% as many
clauses as scheduler S, far below the 80% gate.

The causal gate fails decisively. CN1 retains 43 contractions. One occurs in an
accepted proof ancestry. Deleting that contraction and repeating the frozen
search still produces an independently replayed, officially accepted proof.
Thus none of the 43 retained contractions is shown counterfactually necessary.
CN2 retains 38 contractions and none occurs in accepted proof ancestry.

The result falsifies two candidate abstractions:

1. current-frontier operational novelty is sufficient to identify valuable
   representations;
2. one contraction plus one speculative inference is sufficient to recognize
   the connected contraction corridor.

The next experiment should not expand the forward lookahead. It should reverse
the direction of representation demand:

```text
denied goal
→ missing inference interface
→ indexed active/frontier request
→ representation capable of satisfying that request
→ materialize one verified contraction
```

This is a backward continuation requirement, not another clause-normalization
policy. Its vocabulary must be generic—role, side, path skeleton, repeated
variable constraints and partner interface—and must be frozen before testing.
The three necessary `normal_0040` transitions may calibrate diagnostics but
cannot become equation-specific production rules.

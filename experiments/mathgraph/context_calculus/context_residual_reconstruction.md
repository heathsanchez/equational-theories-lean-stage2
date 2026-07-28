# Polynomial Context Calculus: Phase 1 Reconstruction

## Outcome

The proposed reconstruction path is falsified at its preregistered Phase 1
gate.

The six rejected candidates all attempted:

1. select the first proper source-RHS subterm containing the distinguished
   variable;
2. substitute that compound term for the distinguished source variable;
3. contract an occurrence using the concrete reversed source instance;
4. call the resulting equality `lem1`.

Only one of the six instantiated equalities contains the concrete source
right-hand side required by step 3. The other five contain no matching
subterm at any context path. Consequently their advertised `rw
[(h ...).symm]` step has no independently reconstructible meaning.

The continuation threshold was three unambiguous, independently replayable
prefixes. The observed result is one.

## Frozen baseline

- Starting HEAD: `9ea235dc3a55ac01b42033db656f9d82e6083345`
- Branch: `mathgraph/context-calculus-research`
- Solver SHA-256:
  `fc402fae046096d99a8c01a6848bc4030d282c7f4a90ff5e9c26c3c8d8833fe1`
- Solver size: 313,240 bytes
- Frozen projection: 394 TRUE + 400 FALSE = 794/800
- Solo: 66/66
- Marathon: 25/25
- Production solver changes: none

The exact solver and 794-row manifest are preserved under `artifacts/`.

## Reconstruction table

| Row | Compound substitution | Instantiated source RHS | Embedded contraction | Result |
|---|---|---|---|---|
| `evaluation_hard_0196` | `y ◇ x` | `(y ◇ (y ◇ x)) ◇ (((y ◇ x) ◇ z) ◇ z)` | none | prefix invalid |
| `evaluation_normal_0036` | `(x ◇ y) ◇ (x ◇ z)` | `((((x ◇ y) ◇ (x ◇ z)) ◇ y) ◇ (((x ◇ y) ◇ (x ◇ z)) ◇ z)) ◇ y` | RHS path `LL` | unambiguous |
| `evaluation_normal_0040` | `((x ◇ y) ◇ x) ◇ x` | compound substitution contains no original source RHS | none | prefix invalid |
| `evaluation_normal_0158` | `x ◇ (y ◇ y)` | compound substitution contains no original source RHS | none | prefix invalid |
| `evaluation_order5_0014` | `x ◇ (((z ◇ y) ◇ y) ◇ y)` | compound substitution contains no original source RHS | none | prefix invalid |
| `evaluation_order5_0042` | `(x ◇ (x ◇ y)) ◇ z` | compound substitution contains no original source RHS | none | prefix invalid |

Complete endpoints and rejected Lean sources are recorded in
`results/six_row_context_diagnostics.json`.

## The one valid prefix

For `evaluation_normal_0036`, write

```text
S = (x ◇ y) ◇ (x ◇ z)
R = ((x ◇ y) ◇ (x ◇ z)) ◇ y.
```

The compound source instance is:

```text
S = (((S ◇ y) ◇ (S ◇ z)) ◇ y).
```

Its right side contains the original source right side `R` at path `LL`.
Contracting that occurrence with the reversed source instance yields:

```text
S = (x ◇ (S ◇ z)) ◇ y.
```

Therefore the explicit derived lemma is:

```text
∀ x y z,
  (x ◇ y) ◇ (x ◇ z)
    =
  (x ◇ (((x ◇ y) ◇ (x ◇ z)) ◇ z)) ◇ y.
```

The prefix was independently reconstructed from two source instances and one
congruence lift. The explicit theorem in `artifacts/normal0036_prefix.lean`
compiles under the frozen Lean toolchain. This validates the prefix only; it
does not prove the benchmark target.

## Why the other five fail

Their compound instantiations contain altered copies of the selected
subcontext, but not the exact concrete source instance used by the rejected
proof. A congruence contraction requires exact equality at the recorded path.
Skeleton similarity, shared variables, or a plausible context shape is not
sufficient.

Repairing those five would require discovering different substitutions,
different source instances, or additional derived equalities. That would be a
new search hypothesis, not reconstruction of the rejected proof prefix.

## Scientific conclusion

This does not refute context objects as a generally useful representation.
It refutes the stronger causal claim that the six rejected candidates already
exhibited one shared, valid compound-substitution-and-contraction derivation.

The flagship mock runner accepted candidates before Lean feedback. Its six
similar-looking certificates therefore provided misleading evidence of a
shared proof mechanism.

Per the falsification-first protocol, Context IR implementation, synthetic
suite construction, external audit, and production integration stop here.

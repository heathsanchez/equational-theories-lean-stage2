# Proof-carrying forward-demodulation soundness

A demodulator is an already processed positive unit equality `l = r`.
An orientation is eligible only when `l` is not a variable and:

```text
(term_size(l), render(l)) > (term_size(r), render(r)).
```

The strict frozen order makes every accepted rewrite decreasing. A clause is
simplified by the first eligible match in deterministic activation, side, and
path order. No unproved, passive, or deleted equality is used.

For a substitution `σ` and context `C`, a rewrite:

```text
C[lσ] = t  →  C[rσ] = t
```

is stored as the same sound paramodulation inference already supported by the
external translator. It is not a silent mutation. The unsimplified clause
remains in the proof graph as the parent of the simplified clause, although
only the simplified endpoint enters the passive search set.

Demodulation does not add mathematical inference power beyond superposition.
It changes which equivalent clauses survive the fixed resource bounds.

Fail-closed conditions include:

- nondecreasing orientation;
- rewriting by a nonactive clause;
- failed unification;
- invalid literal side or path;
- term or clause bound violation;
- mismatch between planned and materialized rewrite;
- failed plan translation;
- failed independent replay;
- failed Lean verification.

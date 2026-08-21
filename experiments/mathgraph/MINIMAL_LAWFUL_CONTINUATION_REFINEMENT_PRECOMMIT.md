# Minimal lawful continuation-space refinement — frozen protocol

Target: `evaluation_order5_0014`.

## Question

Can the real residual from the frozen theorem frontier drive the *smallest lawful change to the continuation language* that makes a residual-required continuation expressible, and can the same experiment then find the smallest replay-valid attachment that actually reduces or closes the target cut?

This is the direct executable test of

`rho -> K(rho) -> H' -> delta -> attachment -> closure`.

## Frozen evidence boundary

Before this experiment we already know:

1. the frozen G1/G2 frontier does not close the theorem;
2. target subterms absent from that frontier induce a necessary first-introduction constraint `K(rho)`;
3. the tested G2/G3/G4 recursive operator grammar produced zero candidates satisfying that constraint;
4. residual reification can make the missing structure generatable, but structure generation alone has not closed the target;
5. the current residual is therefore a combination of constructor-language and attachment/cut geometry.

No Vampire proof body, answer identity, theorem-specific proof trace, or new trusted inference rule may be read or supplied.

## Constructor-language search space

A continuation-language regime is a subset of the following *generic replay-valid constructor families*, ordered by cost:

- `R`: direct residual reification by source-law substitution using the missing subterms as substitution atoms;
- `M`: residual-unified simultaneous source-law substitutions already derived from the missing-subterm constraint;
- `J`: endpoint promotion of an `M` substitution into either target endpoint (semantic JOIN constructor);
- `C`: component-anchored promotion of an `M` substitution into a live equality-component term.

Every installed equality must replay to the original source equation. These are proposal-language changes only; the verifier/trust base is unchanged.

Regime cost is lexicographic `(number_of_families, number_of_installed_candidates, total_term_size)`.

The experiment enumerates all non-empty subsets of `{R,M,J,C}` and chooses the minimum-cost regime for which at least one replay-valid candidate satisfies the residual first-introduction constraint `K(rho)`. This is the bounded analogue of a coarsest lawful refinement.

A matched near-miss control replaces missing residual atoms with nearest frontier terms wherever a constructor permits it.

## Attachment search

For the minimum K-satisfying regime only, search replay-valid target-context attachments of its candidates. Attachment cost is lexicographic `(path_length, attached_term_size, candidate_index)`.

The selected attachment is the cheapest one that strictly improves target cut geometry, measured first by direct cross-component connection and otherwise by the minimum structural distance between the two target equality components.

## Arms

- `A_frozen`: original frozen continuation state.
- `B_control`: matched near-miss constructor regime at the same family/candidate budget.
- `C_refined`: minimum residual-derived K-satisfying regime, no attachment.
- `D_attached`: `C_refined` plus the minimum verified improving attachment.
- `D_ablation`: remove only the selected attachment while retaining `C_refined`.

## PASS hierarchy

`PASS_CLOSURE` requires:

1. a finite minimum lawful constructor regime exists;
2. it contains a replay-valid candidate satisfying `K(rho)`;
3. the matched control does not close;
4. a replay-valid attachment is selected by the frozen cost rule;
5. `D_attached` closes the target while `A_frozen`, `B_control`, and `D_ablation` do not.

If closure is not reached, report the strongest mechanistic result without promoting it:

- `MINIMAL_GRAMMAR_REFINEMENT_ONLY`: a minimum K-satisfying regime exists but no attachment improves the cut;
- `MINIMAL_ATTACHMENT_PROGRESS`: a minimum attachment strictly improves cut geometry but does not close;
- `NO_LAWFUL_REFINEMENT`: no searched regime intersects `K(rho)`.

## Claim boundary

A positive result is only a bounded result over this prospectively frozen constructor-family lattice. It does not establish globally minimal representation invention. It does test the exact causal pattern required by Developmental Intelligence: a verified residual constrains a minimal continuation-language change, all generated capabilities remain replay-valid, and attachment/closure are independently tested and ablated.

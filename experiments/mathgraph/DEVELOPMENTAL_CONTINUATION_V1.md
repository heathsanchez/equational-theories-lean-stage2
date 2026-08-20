# Developmental Continuation V1

## Question
Does bounded continuation from verified derived clauses expose useful future closure that immediate target-directed ranking misses?

## Motivation
The five-residual atlas showed mixed superposition/demodulation divergence. Operator attribution showed that the existing MathGraph calculus can generate the first missing Vampire transition in 3/5 residuals, while teacher-forced retention of that single generated transition solved 0/3. Therefore the next hypothesis is multi-generation developmental value, not single-clause retention.

## Frozen intervention
For each newly verified derived equality considered by the compact prover, allocate a small bounded local continuation probe. The probe may use only the ordinary MathGraph inference operators and the current problem state. It must not use Vampire traces, residual IDs, memorized equations, answer labels, or problem-specific rules.

Measure a candidate by downstream verified effects within the probe budget:

1. number of novel replayable equalities generated;
2. number of retained rules/clauses simplified by those descendants;
3. number of novel critical-pair opportunities exposed;
4. best target-distance improvement among descendants;
5. whether a descendant closes the target under the existing replay gate.

Retain a small developmental channel alongside the existing target-directed channel. The developmental channel is ranked by downstream productivity, not by immediate target proximity.

## Controls
A. Existing target-directed selector, unchanged.
B. Equal extra compute with random/non-productivity retention.
C. Developmental continuation channel.
D. Ablation of the developmental channel after candidate discovery.

Budgets must be matched between B and C. No teacher trace may enter C.

## Primary evaluation
First run on the five genuine residuals:
- evaluation_normal_0036
- evaluation_normal_0040
- evaluation_hard_0196
- evaluation_order5_0014
- evaluation_order5_0042

Any hit must replay into an accepted Lean certificate through the existing official-compatible judge path.

## Generalization gate
If C beats both A and B on the residual set, freeze the selector before running the released 800-case audit. Retain only if it preserves prior accepted cases and improves the end-to-end accepted count. Then run a held-out/source-distinct perturbation or generated-law suite to test that the signal is not residual-specific.

## Interpretation
Positive result: verified downstream productivity is a useful selector signal beyond immediate target distance.
Negative result: multi-step continuation as defined here is insufficient; inspect the earliest descendant-level divergence and revise the representation/operator rather than increasing budgets blindly.

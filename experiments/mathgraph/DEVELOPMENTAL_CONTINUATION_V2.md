# Developmental Continuation V2 — relevance-weighted rewrite productivity

## Frozen question
Can verified downstream productivity improve proof search when weighted by convergence toward the target and rewrite utility, rather than by raw branching volume?

## Evidence forcing V2
V1 produced 289 vs 162 replayable descendants and 270447 vs 136869 critical-pair opportunities, but 0/5 closure and worse aggregate target improvement (8 vs 48). It also produced zero actual simplifications in either arm. Therefore raw generativity is not sufficient.

## Frozen intervention
Use the same warm-search, candidate-pool, per-seed probe, retention width, continuation budget, and fresh-engine arm discipline as V1.

For each seed, measure only verified descendants produced by ordinary MathGraph inference. Rank developmental seeds lexicographically by:
1. descendant target closure (highest priority);
2. actual retained-clause simplifications caused by orientable descendants;
3. count of orientable/decreasing descendant rules;
4. target-relevant critical-pair opportunities, defined as overlap opportunities involving descendants whose structural target distance is no worse than the seed;
5. best target-distance improvement among descendants;
6. replayable descendant count (tiebreaker only).

Do not reward total critical-pair volume independent of target relevance.

## Arms
A. Current/random matched-compute retention control.
B. V1 raw-productivity selector (ablation/reference).
C. V2 relevance-weighted rewrite-productivity selector.

All arms receive identical warm time, candidate count, probe time per seed, retention width, descendant-addition cap, and continuation time.

## Primary set
The five genuine 795/800 residuals:
- evaluation_normal_0036
- evaluation_normal_0040
- evaluation_hard_0196
- evaluation_order5_0014
- evaluation_order5_0042

## Promotion rule
Do not alter submission solver.py unless V2 closes at least one residual that both control and V1 miss, with replay-valid proof construction. Any promoted implementation must then pass a full competition-equivalent 800-case official proxy + Lean judge regression with zero loss of previously accepted cases and zero FALSE regressions.

## Prohibitions
No Vampire traces, residual IDs, memorized equations, answer labels, problem-specific rules, or hand-coded case routing may enter the V2 selector.

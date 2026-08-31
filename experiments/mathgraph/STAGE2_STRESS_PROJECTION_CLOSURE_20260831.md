# Stage 2 stress projection/closure result — 31 August 2026

## Status

A frozen deterministic MathGraph solver was evaluated on the 200-problem Stage 2 stress set under the pinned official Lean 4.33.1 / Mathlib 4.33.1 judge. The untouched first pass solved 198/200. A generic source-only consequence-closure mechanism was then developed from the two residuals, isolated, verifier-debugged, and integrated. The resulting frozen candidate solved 200/200 with 200 actual judge `accepted` responses and zero LLM calls.

This note preserves the chronological distinction between untouched transfer evidence and post-residual development.

## Official environment

- Official repository commit: `817a4653bf762584931d49c6714c9fcfab7df66a`
- Lean: `4.33.1`
- Mathlib commit: `0df444a360eaa60ab8c11dca51a86af692955474`
- Solver byte limit: 500000
- TRUE certificate byte limit: 100000
- Judge Lean timeout: 300 seconds per judge phase
- Solver timeout: 3600 seconds per problem

## 1. Untouched frozen first pass

Workflow run: `33350693733`

Source commit: `98076a8f4247acfef597a959b19cbd1195061693`

Frozen solver:

- bytes: `339289`
- SHA256: `f039604f35f03b9c2caf20226e54250777653554093443d205fd2fcd9558f404`

Aggregate result:

- solved: `198/200`
- Order-4: `150/150`
- FALSE: `100/100`
- LLM calls: `0`

The only residuals were both TRUE Order-5 cases:

1. `order5_normal_0030`, equation pair `19040 -> 12906`
   - elapsed: `3430.673 s`
   - judge calls: `0`
2. `order5_normal_0036`, equation pair `6543 -> 29450`
   - elapsed: `1122.924 s`
   - judge calls: `0`

Thus the untouched failure was upstream of Lean certificate verification: the solver did not reach a judge candidate on either row.

## 2. Generic repair

A source-only best-first critical-pair / compact-superposition closure route was added.

Properties of the route:

- seeded only by the incoming source equation;
- no benchmark IDs;
- no equation IDs;
- no stored certificates;
- no named projection or collapse lemma;
- search ordered by consequence weight with a bounded depth penalty;
- target used only to test whether already-proved source consequences normalize the target sides to equality;
- discovered consequences compiled to a Recipe/DAG;
- expanded proof DAG independently replayed before judge submission;
- schematic learned-lemma sharing used only to compress Lean serialization.

The early production schedule bounds this generic closure to at most three seconds before finite-model and deeper routes.

## 3. First isolated verifier result

The first compact schematic emitter reached a judge candidate quickly for both residuals but Lean returned `incorrect`:

- `0030`: `3.436 s`, one judge call, `incorrect`
- `0036`: `1.114 s`, one judge call, `incorrect`

Diagnostic run: `33356042366`

The exact judge errors showed the same defect in both certificates: `CompactSuperposition` had stored its initial source clause in normalized reverse orientation, while the compact emitter represented that stored helper as the original hypothesis `h` without applying symmetry.

This was a certificate-representation error, not a failure to discover the consequence.

## 4. Verifier-derived emitter correction

The compact emitter now checks whether the stored root clause is equal to the incoming source equation in forward or reverse orientation. If reversed, uses of the shared root hypothesis emit `Eq.symm h`.

Emitter fix commit: `15b765e07a8d6fec96909048e9d8517132715196`

No search/ranking change was made for this correction.

## 5. Fail-closed causal gate

Workflow run: `33356279887`

The test solver was modified to exit immediately if the new generic closure route abstained, preventing later portfolio routes from masking the mechanism responsible for success.

Official judge results:

### `order5_normal_0030`

- elapsed: `2.760 s`
- judge calls: `1`
- judge status: `accepted`
- LLM calls: `0`
- emitted Lean certificate: `8468 bytes`

### `order5_normal_0036`

- elapsed: `1.731 s`
- judge calls: `1`
- judge status: `accepted`
- LLM calls: `0`
- emitted Lean certificate: `4084 bytes`

Therefore the new generic mechanism itself closes both fresh residuals under the official Lean judge.

## 6. Frozen post-repair 200-problem audit

Workflow run: `33356499619`

Source commit: `31f3a5aa4e1940adc962e0c40e5b52f85aeba4fd`

Frozen repaired solver:

- bytes: `351404`
- SHA256: `2df0d30e7bed845338fd6957a71d0f9e38201baba6eae19439394e78de6ae3d6`

Aggregate result:

- rows observed: `200`
- unique IDs: `200`
- solved: `200`
- failed: `0`
- accepted rows: `200`
- judge calls: `200`
- LLM calls: `0`
- TRUE: `100/100`
- FALSE: `100/100`
- `order4_normal`: `50/50`
- `order4_hard`: `50/50`
- `order4_extra_hard`: `50/50`
- `order5_normal`: `50/50`

Full-portfolio residual runtimes after repair:

- `order5_normal_0030`: `2.086 s`, `accepted`
- `order5_normal_0036`: `1.861 s`, `accepted`

Overall runtime observations for the repaired 200-case audit:

- median: about `2.28 s`
- 90th percentile: about `3.95 s`
- 95th percentile: about `5.78 s`
- 99th percentile: about `6.66 s`
- maximum: `7.087 s`

## 7. Canonical promotion

Promotion run: `33356836563`

Canonical promotion commit: `5d5d0b7eaf54c2743660556bed7adc58fcaf54e5`

The promotion workflow rebuilt the candidate and refused to commit unless both of the following matched the frozen successful candidate exactly:

- SHA256 `2df0d30e7bed845338fd6957a71d0f9e38201baba6eae19439394e78de6ae3d6`
- byte count `351404`

The exact frozen bytes were then committed to `submissions/mathgraph/solver.py`.

## Interpretation

The strongest supported claim is not merely that the stress set was eventually solved. The recorded sequence is:

`frozen 198/200 -> two zero-judge residuals -> generic source-consequence closure -> concrete but verifier-rejected certificates -> exact verifier residual -> representation/orientation correction -> isolated generic Lean acceptance on both residuals -> frozen 200/200`.

The immutable 198/200 first-pass result remains distinct from the developed 200/200 result.

# MathGraph Stage 2 portfolio

This is the recommended four-file submission portfolio. Each file is built
from `submissions/mathgraph_cleanroom/solver.py`, uses only MathGraph source,
contains no credential or direct-network logic, and carries no third-party
solver payload, table bank, link, or branding. Competition-provided models are
used only after all deterministic, replay-checked routes abstain.

## Upload map

| Track | Model slot | Upload file | Deterministic role |
|---|---|---|---|
| Solo | Google: Gemma 4 31B | `submissions/mathgraph_cleanroom_solo_gemma/solver.py` | Precision deterministic configuration, then three proof-only model attempts with concise judge feedback |
| Solo | OpenAI: gpt-oss-120b | `submissions/mathgraph_cleanroom_solo_oss/solver.py` | Coverage deterministic configuration, then four full-certificate model attempts with concise judge feedback |
| Marathon | Google: Gemma 4 31B | `submissions/mathgraph_cleanroom_marathon_gemma/solver.py` | Precision batch pass, then model triage over deterministic residuals |
| Marathon | OpenAI: gpt-oss-120b | `submissions/mathgraph_cleanroom_marathon_oss/solver.py` | Coverage batch pass, then model triage over deterministic residuals |

Solo candidates are accepted only after immediate official-judge verification.
Marathon candidates are scored by that same verifier at the end of the run;
invalid candidates and abstentions both score zero, so the residual pass cannot
remove a deterministic point.

## Provenance boundary

The cleanroom line starts from
`experiments/mathgraph/regressions/solver_4c0023b.py` and contains independently
implemented generic finite-model search, local table repair, equality search,
compact superposition, a proof-carrying given-clause schedule, and modular
affine model synthesis. Tests scan the core and every upload file for foreign
identifiers, URLs, compressed payload machinery, artifact names, and
credentials. None are present.

The historical 794/800 solver remains byte-for-byte unchanged at 313,240 bytes
and SHA-256
`fc402fae046096d99a8c01a6848bc4030d282c7f4a90ff5e9c26c3c8d8833fe1`.
It is not an upload candidate.

## Evidence

### Generalization-oriented precision result

- `hard3`: 377/400 (174 TRUE, 203 FALSE), 23 abstentions, zero wrong.
- All 16 gains over the exact pre-change base were officially Lean accepted.
- The aggressive TRUE route produced exactly the same accepted-ID set as the
  precision compact-superposition route on all 400 `hard3` rows.
- The aggressive finite repair solved neither of the two precision FALSE
  residuals. Therefore aggressive search is retained only as slot diversity.

### New clean-room general mechanisms

- The bounded age/goal given-clause route closes 3/6 of the common hardest
  theorem residuals locally, including `evaluation_hard_0196`; every result is
  reconstructed and independently replayed. Official Lean requalification of
  these new certificates remains required before claiming leaderboard gains.
- Runtime modular-affine synthesis finds countermodels for 154/205 FALSE
  `hard3` rows and 483/500 FALSE `normal` rows. It derives each operation from
  three coefficients, replays the source law and target witness, and stores no
  per-problem model table.

### Released evaluation regression result

Across the four released 200-row strata, a short-budget screen produced
767/800 with zero wrong. Under full Solo budgets:

- the precision configuration recovers three additional order-5 FALSE rows,
  for 770/800;
- wider compact superposition adds four TRUE rows;
- two deterministic local-repair seeds add three further FALSE rows;
- the coverage configuration therefore reaches 777/800 by the verified union;
- all seven incremental certificates were officially Lean accepted;
- the remaining composition is 22 TRUE and one FALSE.

These rows influenced configuration selection and are regression evidence, not
fresh transfer evidence.

### Format and platform gates

- All 62,576 organizer-provided `eq_size5.txt` laws parse successfully.
- Solo platform gate: 66/66 solver cases and all auxiliary checks passed.
- Marathon platform gate: 25/25.
- Focused cleanroom/portfolio routes: 18/18 after the order-5 parser test.
- Both Solo files pass the local stdin/stdout protocol smoke test and retain
  immediate judge verification before model-generated submission.
- Marathon retains the previously verified deterministic pass and now queues
  model calls only for its residual set.
- All upload files are below 293 KB, well under the 500 KB cap.

## Decision

The precision configuration remains the primary unseen-evaluation bet. The
coverage configuration is the second-slot search-order hedge. Both now use the
assigned competition model only after deterministic abstention, so all four
legal track/model opportunities contribute rather than duplicating a zero-model
solver.

Rebuild and verify with:

```bash
python experiments/mathgraph/build_cleanroom_submission_portfolio.py
python -m pytest -q tests/test_mathgraph_cleanroom_finite_search.py \
  tests/test_mathgraph_final_portfolio.py
```

Compare upload hashes with
`experiments/mathgraph/results/cleanroom_submission_readiness.json` immediately
before submission.

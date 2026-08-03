# MathGraph deterministic Stage 2 portfolio

This is the recommended four-file, zero-LLM submission portfolio. Each file is
built from `submissions/mathgraph_cleanroom/solver.py`; no file calls a model,
contains a credential, performs a network request, or embeds an external
specialist payload.

## Upload map

| Track | Model slot | Upload file | Deterministic role |
|---|---|---|---|
| Solo | Google: Gemma 4 31B | `submissions/mathgraph_cleanroom_solo_gemma/solver.py` | Precision configuration; strongest transfer evidence and lower worst-case cost |
| Solo | OpenAI: gpt-oss-120b | `submissions/mathgraph_cleanroom_solo_oss/solver.py` | Coverage hedge; wider compact superposition and two-seed Fin-5 repair |
| Marathon | Google: Gemma 4 31B | `submissions/mathgraph_cleanroom_marathon_gemma/solver.py` | Precision manifest pass for maximum breadth |
| Marathon | OpenAI: gpt-oss-120b | `submissions/mathgraph_cleanroom_marathon_oss/solver.py` | Coverage manifest pass; aggressive routes scale down automatically with per-row remaining budget |

The selected model name is operationally inert because the files make zero
model calls. The four slots are used for deterministic search diversity.

## Provenance boundary

The cleanroom line starts from
`experiments/mathgraph/regressions/solver_4c0023b.py` and contains independently
implemented generic finite-model search, local table repair, equality search,
and compact superposition. Tests scan the core and every upload file for known
external integration identifiers, URLs, artifact names, and credentials. None
are present.

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
- Both Solo files officially accepted TRUE and FALSE smoke certificates with
  zero model calls.
- Both Marathon files scored 1/1 with a zero-token budget.
- All upload files are below 278 KB, well under the 500 KB cap.

## Decision

The precision configuration is the primary unseen-evaluation bet. The coverage
configuration is a deliberate second-slot hedge: it has seven official gains
on released evaluation data but zero marginal `hard3` transfer. This avoids
mistaking development-set improvement for general capability while still using
the legal extra slots to cover search-order variance.

Rebuild and verify with:

```bash
python experiments/mathgraph/build_cleanroom_submission_portfolio.py
python -m pytest -q tests/test_mathgraph_cleanroom_finite_search.py \
  tests/test_mathgraph_final_portfolio.py
```

Compare upload hashes with
`experiments/mathgraph/results/cleanroom_submission_readiness.json` immediately
before submission.

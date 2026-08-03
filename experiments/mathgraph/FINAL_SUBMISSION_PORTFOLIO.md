# MathGraph cleanroom Stage 2 portfolio

This is the recommended four-file submission portfolio. Each entry is built
from the independently maintained MathGraph solver at
`submissions/mathgraph_cleanroom/solver.py`. The older
`submissions/mathgraph_final_*` files are retained research artifacts and are
not the upload candidates.

## Upload map

| Track | Model | Upload file | Role |
|---|---|---|---|
| Solo | Google: Gemma 4 31B | `submissions/mathgraph_cleanroom_solo_gemma/solver.py` | Deterministic core, then bounded TRUE-proof fallback |
| Solo | OpenAI: gpt-oss-120b | `submissions/mathgraph_cleanroom_solo_oss/solver.py` | Deterministic core, then bounded full-certificate fallback |
| Marathon | Google: Gemma 4 31B | `submissions/mathgraph_cleanroom_marathon_gemma/solver.py` | Deterministic manifest pass; no model calls |
| Marathon | OpenAI: gpt-oss-120b | `submissions/mathgraph_cleanroom_marathon_oss/solver.py` | Deterministic manifest pass, then sparse TRUE-proof fallback |

Every model response is only a candidate. It contributes a verdict only after
the official judge accepts its Lean certificate. Malformed, unsafe, rejected,
or timed-out candidates fail closed.

## Provenance boundary

The cleanroom core starts from
`experiments/mathgraph/regressions/solver_4c0023b.py` and adds independently
implemented generic finite-model search diversification, deterministic local
table repair, and a wider bounded compact-superposition route. The core and all
four generated files are automatically scanned for the known external
integration identifiers, URLs, and artifact names. None are present.

The frozen historical production solver remains byte-for-byte unchanged at
313,240 bytes and SHA-256
`fc402fae046096d99a8c01a6848bc4030d282c7f4a90ff5e9c26c3c8d8833fe1`.
It is not the cleanroom upload candidate.

## Evidence

- `hard3`: 377/400 candidates (174 TRUE, 203 FALSE), 23 abstentions, zero
  wrong; the cleanroom changes add 16 over their exact pre-change base.
- All 16 marginal `hard3` certificates were officially accepted.
- Strict order-5 audit: 46/48 in isolated execution (14 TRUE, 32 FALSE), with
  all 14 newly recovered certificates officially accepted.
- Solo smoke: TRUE and FALSE both officially accepted for both Solo files;
  zero model calls.
- Marathon smoke: 1/1 officially accepted for both Marathon files.
- Official Solo gate: 66/66 solver cases and every auxiliary check passed.
- Official Marathon gate: 25/25.
- Focused cleanroom and portfolio tests: 17/17.
- All upload files are below 280 KB and contain no credential.

The strict order-5 audit was used during development and is regression evidence,
not sealed transfer evidence. `hard3` is broader transfer evidence but is still
public data. The organizer's private distribution remains unknowable.

## Readiness boundary

The deterministic portfolio is ready for upload. The remaining evidence gap is
live, repeated fallback testing against the competition's exact Gemma and
gpt-oss endpoints. Until that is performed, the honest readiness assessment is
9.8/10 rather than a guaranteed 10/10. The deterministic Gemma Marathon entry
provides a no-model-risk hedge.

Rebuild the files with:

```bash
python experiments/mathgraph/build_cleanroom_submission_portfolio.py
python -m pytest -q tests/test_mathgraph_cleanroom_finite_search.py \
  tests/test_mathgraph_final_portfolio.py
```

Immediately before upload, compare sizes and hashes with
`experiments/mathgraph/results/cleanroom_submission_readiness.json`.

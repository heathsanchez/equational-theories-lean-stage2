# MathGraph Stage 2 validation log

## Trust boundary

Only `accepted` from the unmodified official Lean judge counts as solved.
The solver derives candidates from the incoming equation strings, replays
finite models locally, and fails closed when it has no certificate. It does
not use problem IDs, answer labels, or an LLM.

## Repository and environment

- Branch: `mathgraph/general-solver`
- Fork/upstream starting commit: `6805e2323018fbd8a85f41ca09fc33d74d5a02a5`
- OS: macOS 26.4.1 (build 25E253), Apple arm64
- Python: 3.11.14
- Lean: 4.30.0-rc2, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
- Lake: 5.0.0-src+3dc1a08
- Pinned toolchain: `leanprover/lean4:v4.30.0-rc2`
- Mathlib revision: `896cc56a395e1615786fac56564a3fe6bfeebcc4`
- Production sandbox: pinned `python:3.11-slim` image plus `sympy==1.13.3`;
  otherwise Python standard library only.
- Local Docker status: unavailable. The documented `sandbox.mode="none"`
  fallback is used locally; judge verification is unchanged.

## Exact setup and validation commands

```bash
bash scripts/setup.sh
source .env.judge
python3 scripts/run_harness.py
python3 scripts/run_marathon_harness.py
```

The first setup attempt was blocked by the execution sandbox's denial of a
write to `~/.elan/settings.toml`. The unchanged command was rerun with that
filesystem permission. Mathlib checkout then exhausted the disk. Only the
failed local `.lake` checkout was replaced with copy-on-write clones from an
existing local package cache containing the pinned commit. Four recoverable,
older Lean toolchains (4.8.0, 4.16.0-rc1, 4.22.0, and 4.24.0) were uninstalled
to provide enough space; the pinned toolchain was retained. The unchanged
setup then completed, including its accepted smoke certificate.

The first Marathon harness invocation passed five cases and then hit the
execution sandbox's loopback-bind restriction in `_pick_free_port`. The
unmodified command was rerun with localhost socket permission.

## Official harness status

| Gate | Result |
|---|---:|
| Setup smoke judge | accepted |
| Solo harness | 66/66 cases; all auxiliary and challenger checks green |
| Marathon harness | 25 passed, 0 failed |

## Initial deterministic solver

The first implementation contains:

1. a strict, full-consumption parser for the official equation grammar;
2. a one-source-instance TRUE constructor;
3. exhaustive Fin 2 operation-table search;
4. independent semantic replay before FALSE certificate generation;
5. compact `decideFin!` certificate generation;
6. Solo judge request handling and safe unresolved termination.

Marathon I/O and broader deterministic constructors are not implemented yet.

## Certificate and benchmark results

Both initial certificates were sent by `solver.py` through
`pipeline.proxy`, then compiled and checked by the official judge:

| Regression | Verdict | Status | Judge calls | LLM calls | Wall time | Bytes |
|---|---:|---:|---:|---:|---:|---:|
| `mathgraph_initial_true` | TRUE | accepted | 1 | 0 | 10.34 s | 103 |
| `mathgraph_initial_false` | FALSE | accepted | 1 | 0 | 1.69 s | 259 |

Exact accepted sources are preserved in
`experiments/mathgraph/certificates/`, and their equation-only proxy inputs
are in `experiments/mathgraph/regressions/initial_proxy_cases.json`.

### `sample_20.json`

Command:

```bash
python3 -m pipeline.runner \
  --submission submissions/mathgraph \
  --problems examples/problems/sample_20.json
```

| Metric | Result |
|---|---:|
| Accepted TRUE | 0 |
| Accepted FALSE | 8 |
| Incorrect / incomplete / malformed / unparsed | 0 / 0 / 0 / 0 |
| Unresolved / not attempted | 12 |
| Deterministic wins | 8 |
| LLM-assisted wins | 0 |
| Median runtime, all / accepted | 0.03 s / 1.65 s |
| Maximum / total runtime | 4.78 s / 16.7 s |
| Solver source size | 8,228 bytes |
| Largest TRUE / FALSE certificate | n/a / 259 bytes |

`sample_200.json` and the full public sets have not been run in this initial
minimal-constructor pass.

### Reporting discrepancy discovered

`pipeline.runner` reuses `pipeline/results/<submission-name>.json` across
different problem files and initializes its displayed solved count from all
previous accepted IDs in that file. After the two initial proxy regressions,
the first `sample_20` footer therefore reported `10/20` even though its rows
contained 8 accepted and 12 unresolved. No judge result was wrong. Clearing
that generated result file and rerunning the exact benchmark produced the
correct `8/20` footer. Benchmark sets must use isolated output files (or a
clean default result file) to prevent cross-set aggregation.

## Known limitations

- TRUE coverage is limited to a target that is one direct source instance.
- FALSE search is limited to exhaustive Fin 2.
- No reusable semantic model bank, completion, proof DAG, or LLM path yet.
- Docker sandbox execution could not be tested because Docker is unavailable.
- The default runner output path is submission-name-based rather than
  problem-set-based, so clean or isolated outputs are required for accurate
  per-set summaries.

## Next highest-leverage experiment

Add generic equality-chain replay on the TRUE side. The current `sample_20`
misses all ten TRUE controls, while its exhaustive Fin 2 constructor already
accepts eight FALSE cases without a single rejected judge attempt.

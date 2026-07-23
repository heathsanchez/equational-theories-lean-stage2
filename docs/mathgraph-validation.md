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

- FALSE search is limited to exhaustive Fin 2.
- TRUE search is bounded equality chaining and congruence, not completion.
- The term pool and graph limits deliberately leave many target sides
  unreachable.
- No semantic model bank, critical-pair completion, or LLM path exists yet.
- Docker sandbox execution could not be tested because Docker is unavailable.
- The default runner output path is submission-name-based rather than
  problem-set-based, so clean or isolated outputs are required for accurate
  per-set summaries.

## Equality-chain pass

### Frozen baseline and disk gate

This pass started from known-good commit
`24dbc72fdd520debb1818b9c323be293dc2469a1`. Its 8,228-byte solver is
preserved byte-for-byte at
`experiments/mathgraph/regressions/solver_24dbc72.py`.

Before cleanup, `df -h .` reported 268 MiB free, `.lake` used 7.1 GiB, and
`~/.elan` used 18 GiB. The following safe, reproducible data was removed:

- `~/.cache/mathlib` (806 MiB downloaded package cache);
- generated `pipeline/results/mathgraph.json` (12 KiB);
- unused Lean release candidates 4.27.0-rc1 and 4.30.0-rc1 (about 4.8 GiB).

The pinned 4.30.0-rc2 toolchain, current package checkouts, compiled
dependencies, accepted regressions, source, and Git history were retained.
After cleanup and all benchmarks, 5.7 GiB remains free; `.lake` is 7.1 GiB
and `~/.elan` is 13 GiB.

### Algorithm and proof provenance

Parsed terms remain immutable tuples. Each derived equality records its
left and right terms, derivation kind, parent node IDs, exact source
substitution, orientation, and (for congruence) child side plus sibling term.
The permitted node kinds are:

1. source instance;
2. symmetry;
3. transitivity;
4. congruence on the left child;
5. congruence on the right child;
6. reflexivity.

The runtime order is strict parse, direct TRUE instance, exhaustive and
independently replayed Fin 2 FALSE search, bounded TRUE equality search, then
abstention.

The bounded TRUE search constructs a deterministic term pool from target
variables, target/source subterms whose variables are bound by the target,
and shallow compositions. It performs target-guided source matching followed
by fair layered substitution enumeration. Source-instance edges form an
undirected graph; explicit symmetry nodes account for reverse traversal.
Bounded congruence rounds wrap proved equalities in left and right one-hole
contexts. A weighted shortest-path search minimizes source instances, then
congruence steps, then aggregate term size and path length. The selected path
is compiled into explicit transitivity nodes.

Before judge submission, a separate Python replay checks every node against
its parents and exact source substitution. Lean generation uses only source
hypotheses, `Eq.symm`, `Eq.trans`, `congrArg`, and `rfl`.

Hard limits:

| Resource | Limit |
|---|---:|
| Maximum generated term size | 13 tree nodes |
| Term pool | 40 |
| Substitution core | 9 terms |
| Source-substitution attempts | 30,000 |
| Source graph edges | 1,600 |
| Total graph edges | 4,000 |
| Derivation nodes | 4,500 |
| Congruence rounds | 3 |
| Fin 2 local deadline | 1.0 s |
| Equality-chain local deadline | 2.0 s |
| Generated TRUE certificate | 50,000 bytes |

### Exact commands

```bash
source .env.judge
python3 -m pipeline.runner \
  --submission submissions/mathgraph \
  --problems experiments/mathgraph/regressions/equality_chain_cases.json \
  --output /tmp/mathgraph-equality-chain.json
python3 experiments/mathgraph/run_sample20_regression.py
python3 -m pipeline.runner \
  --submission submissions/mathgraph \
  --problems examples/problems/sample_20.json \
  --output experiments/mathgraph/results/sample_20_equality_chain.json
python3 -m pipeline.runner \
  --submission submissions/mathgraph \
  --problems examples/problems/sample_200.json \
  --output experiments/mathgraph/results/sample_200_equality_chain.json
python3 scripts/run_harness.py
python3 scripts/run_marathon_harness.py
```

`run_sample20_regression.py` always uses a fresh temporary result path,
asserts the exact 20 problem IDs with no duplicates, requires exactly eight
accepted FALSE certificates, and rejects any non-accepted judge call.

### Synthetic and existing regressions

All nine equation-only synthetic cases passed through the real proxy and
official judge:

| Constructor requirement | Official result |
|---|---:|
| Direct source instance | accepted TRUE |
| Two source uses plus transitivity | accepted TRUE |
| Reversed source orientation | accepted TRUE |
| Left-child congruence | accepted TRUE |
| Right-child congruence | accepted TRUE |
| Nested congruence | accepted TRUE |
| Both sides converge to an intermediate | accepted TRUE |
| Idempotent/noncommutative FALSE control | accepted FALSE |
| Associative/noncommutative FALSE control | accepted FALSE |

Each used one judge call and zero LLM calls. The original TRUE and FALSE
proxy regressions also remain 2/2 officially accepted. Exact generated Lean,
judge status, timings, and logs are retained in
`experiments/mathgraph/results/equality_chain_proxy.json` and
`initial_proxy_equality_chain.json`.

### Clean benchmark results

| Metric | `sample_20` | `sample_200` |
|---|---:|---:|
| Accepted TRUE | 1 | 64 |
| Accepted FALSE | 8 | 84 |
| Unresolved | 11 | 52 |
| Incorrect / incomplete / malformed / unparsed | 0 / 0 / 0 / 0 | 0 / 0 / 0 / 0 |
| Direct-instance TRUE hits | 0 | 57 |
| Equality-chain TRUE hits | 1 | 7 |
| Fin 2 FALSE hits | 8 | 84 |
| LLM-assisted hits | 0 | 0 |
| Median runtime | 0.09 s | 1.225 s |
| Maximum runtime | 4.15 s | 6.60 s |
| Total runtime | 19.02 s | 237.14 s |
| Largest TRUE certificate | 623 bytes | 1,093 bytes |
| Largest FALSE certificate | 259 bytes | 259 bytes |

The solver is 23,678 bytes. Equality-chain DAGs had 8 nodes for the
`sample_20` win and 3–13 nodes (median 4) for the seven `sample_200` chain
wins. Every emitted mathematical DAG replayed successfully, and every
resulting judge request was officially accepted. There is currently no gap
between mathematical replay and official acceptance.

Equality chaining therefore generalizes beyond direct instances: it adds one
clean `sample_20` TRUE and seven `sample_200` TRUEs without losing any frozen
FALSE win or producing a rejected judge attempt.

### Unresolved TRUE phenotypes

The frozen post-benchmark structural audit grouped the 36 unresolved
TRUE-labelled `sample_200` rows as:

| Generic phenotype | Count |
|---|---:|
| Only one target side generated | 21 |
| Bounded graph saturated without a connection | 12 |
| Both target sides generated but disconnected | 3 |

The dominant obstruction is one-sided reachability, not Lean compilation.

### Official harness regression

After implementation and both benchmarks, the unmodified Solo harness
remained 66/66 green with all challenger checks passing. The unmodified
Marathon harness remained 25 passed, 0 failed.

## Next highest-leverage experiment

Add bounded source re-entry: feed newly proved intermediate terms back into
target-guided source instantiation while preserving the existing proof DAG
and limits. This directly targets the dominant one-sided-reachability
phenotype without jumping to unrestricted critical-pair completion.

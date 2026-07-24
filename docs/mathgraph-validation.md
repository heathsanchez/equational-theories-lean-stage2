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
The equality-chain implementation and its isolated official artifacts were
committed as `eab2902af7f876872e1576d31f0d6e91c1be6d21`.

Before cleanup, `df -h .` reported 268 MiB free, `.lake` used 7.1 GiB, and
`~/.elan` used 18 GiB. The following safe, reproducible data was removed:

- `~/.cache/mathlib` (806 MiB downloaded package cache);
- generated `pipeline/results/mathgraph.json` (12 KiB);
- unused Lean release candidates 4.27.0-rc1 and 4.30.0-rc1 (about 4.8 GiB).

The pinned 4.30.0-rc2 toolchain, current package checkouts, compiled
dependencies, accepted regressions, source, and Git history were retained.
After cleanup and all benchmarks, 5.9 GiB remains free; `.lake` is 7.1 GiB
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

## Bounded source-reentry pass

### Commits and frozen artifacts

This pass started at the authoritative equality-chain validation commit
`896e0633d7d013b7fbf910e12335bd55f85debad`; its implementation parent is
`eab2902af7f876872e1576d31f0d6e91c1be6d21`. The source-reentry
implementation is
`fc5ef032ba7cac61c17b6096afc953d995acdaa3`.

The 23,678-byte starting solver is preserved byte-for-byte at
`experiments/mathgraph/regressions/solver_896e063.py` with SHA-256
`e610a6505f1f7a48881a7bdbb6b36ba50152d5eb9b1054861f255537fc4078e0`.
The authoritative isolated baseline outputs remain:

| Artifact | SHA-256 |
|---|---|
| `sample_20_equality_chain.json` | `28755ecca76ed6c357f1b54607584031b7f48d91f65eb336807e431b2ead4b5c` |
| `sample_200_equality_chain.json` | `dc25ca21a26ec8a5e2dfa92d4ddc58a089b1b0ffdeeb2353a141fd27d469392c` |

The generalized regression runner verifies those hashes, uses a new temporary
problem and result file for every benchmark, checks exact IDs and duplicate
absence, preserves every frozen accepted ID and verdict, enforces the TRUE and
FALSE floors, rejects every non-`accepted` judge status, and requires zero LLM
calls.

### Algorithm, provenance, and replay

Generation zero remains the validated equality-chain search. A re-entry
generation collects bounded candidate arguments from equality endpoints,
their subterms, deterministic component representatives, target contexts,
terms connected to either target side, and terms matching a source-law side.
Terms created in the immediately preceding generation are ranked first.

Candidate substitutions are ranked only by structural information:

1. whether the instantiated edge joins different graph components;
2. whether either side is already connected to a target side;
3. whether it directly involves a target subterm;
4. structural tree distance to the target sides;
5. whether an instantiated side matches a source-law side;
6. total instantiated size and a deterministic textual tie-break.

Each generation reserves graph space for the next generation and for
congruence. It checks target connectivity after source instantiation and
congruence even when a limit or wall deadline has fired, then performs one
final prefix check before abstaining.

Every source-reentry node records the source orientation, full ordered
substitution, generation, instantiated sides, and the earlier derivation-node
IDs from which each derived argument originated. Congruence nodes inherit the
generation of their parent. Derived terms need no equality proof merely to be
universal source arguments; equality replacement remains explicit through
`Eq.symm`, `Eq.trans`, and `congrArg`.

Before Lean generation, the independent replay routine checks every source
instance and source-reentry substitution against the parsed source law,
validates term-origin IDs and subterm membership, and checks every symmetry,
transitivity, congruence, and reflexivity node without calling the search
methods. It then checks the final target endpoints. The existing explicit
`have`-based Lean compiler is reused.

The pass also fixed a deadline hole exposed by the growth-pathological
regression: Fin 2 evaluation now checks the hard deadline inside assignment
enumeration, rather than only between operation tables.

### Search configurations and promotion

Three preregistered configurations were evaluated on the development half:

| Configuration | Generations | Re-entry term size | New terms | Instances / generation | Final nodes / edges | Wall time |
|---|---:|---:|---:|---:|---:|---:|
| Light | 1 | 15 | 24 | 400 | 1,500 / 1,400 | 1 s |
| Medium | 2 | 15 | 32 | 1,000 | 4,000 / 3,600 | 3 s |
| Targeted | 2 | 15 | 32 target-connected only | 2,000 | 6,000 / 5,600 | 5 s |

All begin at the generation-zero term cap of 13. Initial graph reservations
are respectively 900/800, 2,200/1,800, and 3,000/2,400 nodes/edges.
Generation-zero source-attempt limits are 8,000, 18,000, and 24,000; source
edge limits are 600, 1,200, and 1,600. All use at most three congruence
rounds. The unchanged initial equality-chain and Fin 2 deadlines are 2 s and
1 s; generated TRUE certificates remain capped at 50,000 bytes.

Only medium produced a development gain. Light and targeted added no accepted
development row after medium, so production freezes medium alone. The tested
and promoted runtime order is:

```text
parse -> direct source instance -> initial equality chain -> Fin 2
      -> source re-entry medium -> abstain
```

Moving light before Fin 2 could not improve the development accepted set and
would run extra search on 35 already-solvable development FALSE rows, so it
was not promoted.

### Synthetic official regressions

The nine original equality-chain proxy/judge cases remain 9/9 accepted. The
new 11-case suite records:

| Requirement | Official result |
|---|---:|
| One re-entry generation | accepted TRUE |
| Two re-entry generations | accepted TRUE |
| Re-entry after congruence | accepted TRUE |
| Reversed source orientation | accepted TRUE |
| Both target sides converge to an intermediate | accepted TRUE |
| Collapse law after re-entry | accepted TRUE |
| Projection/absorption after re-entry | accepted TRUE |
| Two matched shape controls | 2 accepted FALSE |
| Growth-pathological source | timeout and abstain; zero judge calls |
| Complete prefix after expired deadline | accepted TRUE |

Thus the suite has eight accepted TRUE, two accepted FALSE, one bounded
timeout abstention, zero rejected judge calls, and zero LLM calls. The
independent expired-prefix replay produced a 1,192-byte certificate that the
official judge accepted.

### Content-hash development and holdout

`sample_200` was sorted by SHA-256 of
`equation1.strip() + "\0" + equation2.strip()`, with equation text as the
deterministic collision tie-break. The first 100 hashes form development and
the remaining 100 form holdout. IDs and answer labels do not enter the split.

The three-configuration exploratory development run selected medium. The
medium-only development run was then repeated, the choice frozen, and the
holdout run launched for the first time:

| Split | Frozen baseline TRUE / FALSE | Source-reentry TRUE / FALSE | Accepted gain | Total runtime |
|---|---:|---:|---:|---:|
| Development | 33 / 35 | 34 / 35 | +1 TRUE | 138.54 s |
| Untouched holdout | 31 / 49 | 32 / 49 | +1 TRUE | 161.82 s |

Both gains use generation 2. The gain therefore generalized exactly once to
each half, with FALSE preservation and zero invalid judge outcomes.

### Final clean benchmarks

| Metric | `sample_20` | `sample_200` |
|---|---:|---:|
| Accepted TRUE | 1 | 66 |
| Accepted FALSE | 8 | 84 |
| Unresolved | 11 | 50 |
| Incorrect / incomplete / malformed / unparsed | 0 / 0 / 0 / 0 | 0 / 0 / 0 / 0 |
| Direct-instance TRUE hits | 0 | 57 |
| Equality-chain TRUE hits | 1 | 7 |
| Source-reentry generation-1 hits | 0 | 0 |
| Source-reentry generation-2 hits | 0 | 2 |
| Fin 2 FALSE hits | 8 | 84 |
| LLM calls | 0 | 0 |
| Median runtime | 0.365 s | 1.385 s |
| Maximum runtime | 12.13 s | 11.94 s |
| Total runtime | 31.59 s | 281.24 s |
| Largest certificate | 664 bytes | 1,146 bytes |

The final solver is 45,493 bytes, below the 500,000-byte intake limit. Full
`sample_200` accepted score increases from 148 to 150: +2 TRUE, no FALSE
loss, and no rejected judge attempt. The full runtime increases by 44.10 s
(18.6%) from the 237.14 s equality-chain run. Cold Lean startup makes
single-run maximum and `sample_20` totals noisier than local search cost.

The two promoted proof DAGs contain 4 and 8 compiled equality nodes.
Generation/source-instance counts for the development gain are
`0:1200, 1:275, 2:42`; the holdout gain uses
`0:1200, 1:420, 2:330`. The largest search recorded for either accepted gain
has 3,034 equality nodes, and the largest accepted certificate is 1,146
bytes.

### Failure phenotype movement

The two gains remove one formerly one-sided target case and one case where
both target sides entered but remained disconnected. Therefore the recorded
primary one-sided bucket moves from 21 to 20 of the remaining unresolved TRUE
population. A stricter exact-side audit, run identically on both engines,
moves from 28 to 27. No still-unresolved case changes exact entry phenotype:
the movement is from the two solved cases, not relabeling.

The 34 remaining unresolved TRUE rows under the strict final audit are:

| Structural phenotype | Count |
|---|---:|
| Only left target side enters graph | 27 |
| Both enter but remain disconnected | 5 |
| Neither target side enters graph | 2 |
| Mathematical connection but extraction failure | 0 |
| Replay succeeds but Lean rejects | 0 |

One row records instance-budget exhaustion; there are no timeout, certificate
size, replay, extraction, or Lean-rejection failures in the final public
results. The dominant remaining obstruction is still one-sided target
reachability.

### Official gates and disk

After all benchmarks, the unmodified Solo harness is 66/66 green with every
challenger check passing. The unmodified Marathon harness is 25 passed,
0 failed. Its first invocation again hit the execution sandbox's loopback
bind restriction; the unchanged command passed with localhost permission.

After temporary benchmark cleanup, `df -h /Users/heath` reports 8.0 GiB free.

## Next highest-leverage experiment

Add a bounded, goal-directed contextual-overlap/narrowing constructor. It
should derive and rank small critical overlaps of the single source law only
when they introduce the missing target side or join a target-connected
component, while retaining the same proof-DAG replay and content-hash
promotion discipline. This is the next reusable TRUE route before broad
critical-pair completion or higher-order finite model search.

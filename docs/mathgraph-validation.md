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

## Goal-directed contextual overlap and narrowing pass

This pass started from authoritative commit
`d75ce6862341bfb295cee2b20ae985dd821c2ab7`. The implementation commit is
`f6c92ce` (`add goal-directed contextual overlap constructor`). The exact
starting solver is preserved as
`experiments/mathgraph/regressions/solver_d75ce68.py`: 45,493 bytes,
SHA-256
`66ae78355d4f01a5528559a0923264644fa8f77287e8a33ae34ab426f7455d31`.

The regression gate verifies these unchanged frozen artifact hashes:

| Frozen artifact | SHA-256 |
|---|---|
| `sample_20` | `cc92c7e86c38bf3dbf0781ae4891a66661e502e3f6a208e246132151884407a9` |
| `sample_200` | `5ee84fd8028420d42aebaf67f6506d94aebaf9f3bf9af32f2848d554b7bf8625` |
| Source-reentry proxy | `87c15430ae7293e6da65b51234754adb27e30575f1c8583b14cc4741d0f195b9` |
| Equality-chain proxy | `987f7cf71c938d8831337edc6ee8d0d2e8788fa241eb74eb58457cc1f6f6800d` |

Every clean invocation still writes to a unique temporary result file before
copying its validated output. The gate requires every previously accepted row
to remain accepted with the same verdict, at least 66 TRUE and 84 FALSE on
the full sample, no rejected judge category, no LLM call, and both official
harnesses green.

### Algorithm and proof representation

`ContextualSearch` adds two bounded search operations without adding a trusted
proof rule:

- Target narrowing starts from both target sides and target-connected graph
  components. It matches either source side at non-variable subterm paths,
  completes an ordered concrete source substitution, replaces the match by
  the opposite source side, and ranks results by exact target introduction,
  target-subterm occurrence, component connection, structural distance, term
  size, and variable diversity.
- Contextual overlap indexes both sides and orientations of bounded concrete
  source instances. It overlaps an inner equality at a proper non-variable
  position of an outer equality, lifts the inner proof through the recorded
  one-hole context, and combines it with the outer proof by symmetry and
  transitivity. Depth-two search may reuse bounded consequences as outer
  equalities, but is not unrestricted completion.

Contexts are root-relative tuples of `L` and `R`. `get_subterm` and
`replace_subterm` operate on the parsed term tree. A nested replacement is
compiled into an ordinary chain of left- or right-child `congrArg` nodes.
Overlap metadata records the outer and inner node IDs, selected sides,
context path, exact before and after subterms, changed outer term, consequence,
and structural score. Final DAG nodes remain only source instance, symmetry,
transitivity, congruence, and reflexivity.

Independent replay does not invoke search. It checks parent-before-child DAG
order, every ordered source substitution and orientation, congruence
endpoints, transitivity joins, context path validity, exact subterm
replacement, overlap records, target endpoints, term-size bounds, and node
budgets before Lean generation. Lean certificates use explicit `have`
bindings, `Eq.symm`, `Eq.trans`, and nested `congrArg`.

### Fixed experimental portfolio

The preregistered configurations were:

| Route | Bounds |
|---|---|
| Target narrowing | depth 3; context depth 5; branching 20; 750 terms; 3,000 DAG nodes; term size 19; 3 s |
| Contextual light | overlap depth 1; context depth 3; 300 source instances; 1,000 candidates; 1,500 new nodes; term size 17; 1 s |
| Contextual medium | overlap depth 2; context depth 5; 800 source instances; 4,000 candidates; 6,000 new nodes; term size 21; 5 s |

The full portfolio was evaluated only on development. All five marginal
accepted cases came from target narrowing. Light and medium added zero after
narrowing, so both were removed. Target narrowing before source re-entry was
then frozen because it avoids re-entry work on more development wins than the
single existing development re-entry win on which it adds work.

The untouched holdout added zero accepted cases. This fails the preregistered
promotion rule, which required at least one holdout gain or a major runtime
reduction. Consequently `PROMOTED_CONTEXTUAL_PORTFOLIO` is empty: the
constructor is implemented and regression-tested but is not on the production
route.

### Synthetic official regressions

The 16 equation-only contextual cases produced:

| Result | Count |
|---|---:|
| Officially accepted TRUE | 12 |
| Officially accepted FALSE controls | 3 |
| Growth-pathological bounded abstention | 1 |
| Rejected judge calls | 0 |
| LLM calls | 0 |

The positive suite covers left- and right-child overlap into a source lhs,
overlap into the rhs, reversed inner and outer orientations, nested context,
self-overlap with different substitutions, target narrowing, bidirectional
meeting, temporary expansion, transitivity after congruence, and a proof
prefix replayed after deadline expiry. The variable-position control records
suppression rather than generating bare-variable overlaps. All nine synthetic
overlap certificates use overlap depth 1. The largest synthetic proof DAG has
7 used nodes and the largest certificate is 943 bytes.

The existing nine equality-chain cases remain 9/9 accepted. The existing
source-reentry suite remains eight accepted TRUE, two accepted FALSE, and one
bounded abstention, including an officially accepted expired-prefix replay.

### Development, untouched holdout, and final production

The split membership and SHA-256 equation-content method were not changed.

| Evaluation | Frozen TRUE / FALSE | Experimental TRUE / FALSE | Gain |
|---|---:|---:|---:|
| Development | 34 / 35 | 39 / 35 | +5 TRUE |
| Untouched holdout | 32 / 49 | 32 / 49 | 0 |
| Combined split outputs, diagnostic only | 66 / 84 | 71 / 84 | +5 TRUE |

The combined diagnostic is not a promoted full-set score. Because the gain
failed to generalize to holdout, the final clean production benchmarks use
the empty contextual portfolio:

| Metric | `sample_20` | `sample_200` |
|---|---:|---:|
| Accepted TRUE | 1 | 66 |
| Accepted FALSE | 8 | 84 |
| Unresolved | 11 | 50 |
| Incorrect / incomplete / malformed / unparsed | 0 / 0 / 0 / 0 | 0 / 0 / 0 / 0 |
| Target-narrowing production hits | 0 | 0 |
| Contextual-light production hits | 0 | 0 |
| Contextual-medium production hits | 0 | 0 |
| LLM calls | 0 | 0 |
| Total runtime | 31.9 s | 283.7 s |

The final solver is 75,870 bytes, below the 500,000-byte cap. Its clean
production score remains 150/200, so net promoted gain is zero. The
implementation adds no production search runtime; the 2.46-second difference
from the prior 281.24-second full run is normal judge/startup variance.

For runtime selection, the all-route development experiment took 284.19
seconds versus 138.54 seconds at baseline: +145.65 seconds, or 29.13 seconds
per development-only gain. After freezing target narrowing alone, the clean
holdout took 161.91 seconds versus 161.82 seconds at baseline, with unresolved
median 0.27 versus 0.20 seconds and no gain. A judge-free standalone audit of
target narrowing over all 50 frozen unresolved rows took 0.847 seconds total,
0.0084 seconds median, and 0.195 seconds maximum. Thus narrowing itself is
small, but it offers neither the required holdout gain nor a major end-to-end
runtime reduction. Seconds per promoted accepted result is undefined because
none was promoted.

Target narrowing produced five marginal development wins. When ordered before
re-entry it produced six experimental certificates in the combined split,
preempting one already-accepted source-reentry row. There were zero public
contextual-overlap light or medium wins and therefore no public overlap-depth
distribution. The largest experimental target-narrowing proof DAG has 22 used
nodes and its largest certificate is 2,041 bytes.

### Structural result and official gates

As a diagnostic, the five development gains would reduce unresolved TRUE from
34 to 29. The strict source-reentry graph phenotype would move:

| Phenotype | Frozen | Experimental |
|---|---:|---:|
| Only one exact target side enters | 27 | 23 |
| Both enter but remain disconnected | 5 | 4 |
| Neither enters | 2 | 2 |

Three of the five gains explicitly introduce the missing exact target side;
two connect through generated intermediates. No accepted search records a
direct existing-component join. Since the route was not promoted, the final
production phenotype remains 27 / 5 / 2.

There are zero incorrect, incomplete, malformed, unparsed, replay, extraction,
or Lean-rejection outcomes. The unmodified Solo harness passes 66/66. The
unmodified Marathon harness passes 25/25; its sandboxed invocation could not
bind localhost, and the unchanged command passed with loopback permission.
After validation, `df -h /Users/heath` reports 8.1 GiB free.

## Next highest-leverage experiment after contextual holdout

Do not deepen the deterministic TRUE saturation stack yet. Contextual
narrowing found a concentrated development cluster but zero holdout cases,
and contextual overlap added no marginal public win. The next broad reusable
constructor should be bounded, officially verified **Fin 3 countermodel
search**, preserving the same content-hash promotion and fail-closed
discipline.

## Verified Fin 3 countermodel pass

This pass started from authoritative commit
`65270e74e3d2fcf10883b516f3ae1e79203ff757`. The implementation commit is
`56ac3db867a9403868be39f97ae22131858e97b3`
(`add verified Fin 3 countermodel constructor`). The exact starting solver is
preserved as `experiments/mathgraph/regressions/solver_65270e7.py`: 75,870
bytes, SHA-256
`b026c85cf66ed9ecb0b8baf9fd1a3d1915208fe7719793ee2c1cf5a7334aa4c0`.

The contextual portfolio remains empty in production. The frozen 150-row
regression floor and all previously accepted verdicts are enforced using
isolated result files. The frozen production artifacts are:

| Artifact | SHA-256 |
|---|---|
| Production `sample_20` | `ef6ea116b1bab964274fee1f205e3bf27c770f6d91c65aac9574d493aaf85e6d` |
| Production `sample_200` | `c4efdcca30a9a12ad4a76a26641e3790e44cb8503024c7c762e8ccccf55d8857` |
| Equality-chain suite | `987f7cf71c938d8831337edc6ee8d0d2e8788fa241eb74eb58457cc1f6f6800d` |
| Source-reentry suite | `87c15430ae7293e6da65b51234754adb27e30575f1c8583b14cc4741d0f195b9` |
| Contextual suite | `c06d2692ddba7aa0bc3f13fbc926cffb2b0457314ed6df65eeb16c4cbfe7d0dd` |

### Model representation, evaluator, and replay

A partial Fin 3 operation is a flat nine-cell vector in row-major order.
Unassigned cells are represented internally by `-1`; complete tables contain
only 0, 1, and 2. Lean serialization reshapes the same flat vector to
`[[...],[...],[...]]`.

Both equation sides are compiled into one shared subterm DAG. Each variable
node references an assignment slot and each operation node references its two
child nodes. A complete evaluation computes every repeated subterm once. A
partial evaluation returns either a known value, one unresolved table cell,
or an expression blocked by an unresolved child.

Independent replay does not use incremental search caches. It checks:

- exactly nine total cells with values in `0..2`;
- the source equation for every Fin 3 assignment;
- the stored target assignment and its genuine target disequality;
- existence of a target failure under full enumeration;
- byte-exact agreement between the replayed flat table and Lean
  serialization.

Only after replay succeeds does the solver emit the accepted `Magma (Fin 3)`
certificate using `finOpTable` and `decideFin!`.

### Search engines and sound constraints

Three fixed engines were implemented:

| Engine | Search | Initial bounds |
|---|---|---|
| Fin3-fast | target-witness-guided partial backtracking | 25,000 states; 0.5 s; 16 retained models |
| Fin3-medium | source-model partial backtracking | 150,000 states; 2 s; 64 retained models |
| Fin3-complete-bounded | canonical complete enumeration | all 19,683 raw tables; 3 s; 64 retained models |

All source assignments are precompiled and ranked by direct cell dependency,
repeated assigned values, and lexical order. Partial propagation is limited to
sound consequences: determined unequal sides prune; a known value opposite
one unresolved root cell forces that cell; the same pending cell on both sides
is satisfied; conflicting forced values prune. Other unresolved expressions
are not guessed or rewritten.

Target assignments are ranked by number of distinct elements, induced direct
cell dependencies, structural asymmetry, and lexical order. The branch cell
score combines static source dependency frequency, currently exposed source
constraint cells, and cells exposed by the selected target witness.

Each retained source model is canonicalized under all six permutations of
Fin 3. Complete enumeration evaluates only a table that is the lexicographically
least representative of its relabelling orbit. This reduces 19,683 raw tables
to 3,330 canonical representatives without assuming an idempotent diagonal.
No partial-table symmetry condition is imposed. The canonical model bank is
local to one solver invocation and is not required for correctness or
cross-problem persistence.

Inputs with more than six source or target variables, or a side larger than
63 term nodes, fail closed before assignment-space construction.

### Synthetic official regressions

The 16 equation-only Fin 3 cases produced:

| Result | Count |
|---|---:|
| Officially accepted FALSE | 13 |
| Officially accepted TRUE controls | 2 |
| Bounded pathological abstention | 1 |
| Rejected judge calls | 0 |
| LLM calls | 0 |

Coverage includes the preserved Fin 2-first route, no-Fin-2/yes-Fin-3
implications, a genuinely three-element model, noncommutative and
nonassociative models, a model with no idempotent diagonal entry, witnesses
using one/two/all-three elements, one- and multi-variable source laws,
completed-prefix replay after deadline expiry, and rejection of both a
corrupted table and corrupted serialization. The largest Fin 3 certificate is
271 bytes.

The existing equality-chain suite remains 9/9. Source re-entry remains eight
accepted TRUE, two accepted FALSE, and one bounded abstention. The contextual
research suite independently reconstructs, replays, and officially accepts
all 12 positive constructors while permitting the intentionally disabled
production contextual route to abstain; its three FALSE controls and one
pathological abstention also remain correct.

### Development selection and untouched holdout

The exact existing equation-content hash split was retained:

| Split | Frozen TRUE / FALSE | Fin 3 TRUE / FALSE | Marginal gain |
|---|---:|---:|---:|
| Development | 34 / 35 | 34 / 37 | +2 FALSE |
| Untouched holdout | 32 / 49 | 32 / 57 | +8 FALSE |

Both development gains came from Fin3-fast. Fin3-medium and canonical complete
enumeration added zero accepted case after fast and were disabled in
production. On the all-engine development run:

| Engine | Attempts | Hits | Partial states | Canonical complete tables |
|---|---:|---:|---:|---:|
| Fin3-fast | 31 | 2 | 130,630 | 6,683 source models reached |
| Fin3-medium | 29 | 0 | 11,171 | 867 complete source models reached |
| Fin3-complete-bounded | 29 | 0 | 0 | 96,570 |

Complete enumeration removed 474,237 raw relabelling duplicates across those
29 diagnostic attempts.

The alternate order Fin3-fast before source re-entry was rejected on
development timing. Across the two Fin 3 gains it would save about 0.023
seconds of failed re-entry search, but on the existing development re-entry
win it adds about 0.176 seconds of failed Fin 3 search before the 0.116-second
successful re-entry. Production therefore remains:

```text
direct TRUE
→ equality chain
→ Fin 2
→ source re-entry
→ Fin3-fast
→ abstain
```

### Final clean benchmarks and performance

| Metric | `sample_20` | `sample_200` |
|---|---:|---:|
| Accepted TRUE | 1 | 66 |
| Accepted FALSE | 10 | 94 |
| Total accepted | 11 | 160 |
| Unresolved | 9 | 40 |
| Fin3-fast hits | 2 | 10 |
| Fin3-medium hits | 0 | 0 |
| Complete-enumeration hits | 0 | 0 |
| Incorrect / incomplete / malformed / unparsed | 0 / 0 / 0 / 0 | 0 / 0 / 0 / 0 |
| LLM calls | 0 | 0 |
| Total runtime | 32.01 s | 296.96 s |

The promoted score moves from 150/200 to **160/200**: +10 FALSE, no TRUE or
FALSE regression, and no rejected judge outcome. Full runtime increases from
283.64 to 296.96 seconds: +13.32 seconds, or 1.332 seconds per added accepted
FALSE. The median unresolved-row runtime moves from 0.23 to 0.33 seconds.

Across all 50 full-sample Fin3-fast attempts, the engine recorded:

| Metric | Total |
|---|---:|
| Partial states visited | 197,778 |
| Complete source tables reached | 11,265 |
| Source assignments evaluated | 4,134,776 |
| Early source prunes | 120,940 |
| Target witnesses tested | 12,419 |
| Symmetry duplicate source models removed | 10,829 |
| Target-falsifying models | 10 |

The largest individual fast search visited 18,270 partial states; the largest
accepted search reached 2,451 complete source tables. Five attempts reached
their 0.5-second deadline and abstained. Maximum replay time was 0.000077
seconds. Every Fin 3 certificate is 271 bytes; the largest certificate from
any final constructor is 1,134 bytes. The final solver is 94,219 bytes,
comfortably below the 500,000-byte cap.

### Exhaustive bounded obstructions

After the final run, six known FALSE rows remain unresolved. Diagnostic
complete enumeration checked all 3,330 canonical Fin 3 tables for each:

| Residual classification | Count |
|---|---:|
| Fin 3 source models exist, but all satisfy the target | 4 |
| Source constraints have no Fin 3 model | 2 |
| Replay or Lean failure | 0 |

Thus all six have an exhaustive **no countermodel of order ≤ 3** record. The
diagnostic audit tested 19,980 canonical tables, removed 98,118 raw symmetry
duplicates, evaluated 54,936 source assignments, and completed in about 0.91
seconds. This is bounded obstruction evidence, not a proof of the implication.

### Official gates and next experiment

The final source and result hashes are:

| Artifact | SHA-256 |
|---|---|
| Solver | `521e078e1233ecec8f6fd688c8a1b676acd5f2b6d0846dbd93e43dd4dc1f8437` |
| `sample_20` | `861af3ef20cd2363606b7d75f84aa39dfbf8f56fbf37808eb887dccbe2f3d4f3` |
| `sample_200` | `1f195aabbb01a884a3c6a6670c804a66580e6428c78bd0d4665b28e7a57f73f6` |
| Fin 3 synthetic suite | `8bf13e4a7d10b098bedb880837018e8261dfc28c63d1327a12b0ea150e1addca` |

The unmodified Solo harness passes 66/66 and the unmodified Marathon harness
passes 25/25. Invalid judge outcomes, replay failures, Lean rejections, and
LLM calls are all zero. `df -h /Users/heath` reports 8.2 GiB free.

The dominant remaining FALSE obstruction is now a source law with one or more
Fin 3 models for which every model satisfies the target. The next
highest-leverage reusable constructor is a **bounded Fin 4
target-witness-guided CSP/backtracker**, reusing the compiled constraints,
independent replay, and safe complete-model canonicalization. Exhaustive
`4^16` table enumeration should not be attempted as the primary route.

## Generic finite-model CSP refactor

This architecture pass started from authoritative HEAD
`1ad667b6930274a3ce02a3ceb6dc53a2d6a4627e`. The implementation commit is
`c31e9da7a12db87c69b1a219ef7bb2a1785e164f`
(`refactor finite models into generic CSP engine`). The exact starting solver
is preserved as `experiments/mathgraph/regressions/solver_1ad667b.py`: 94,219
bytes, SHA-256
`521e078e1233ecec8f6fd688c8a1b676acd5f2b6d0846dbd93e43dd4dc1f8437`.
The frozen production floor is 66 accepted TRUE plus 94 accepted FALSE.

The pass deliberately separates architecture from score promotion. Fin 2 and
the promoted Fin 3 route now use one generic engine in production. Fin 4 is
exercised only by synthetic direct verification and is not in the production
portfolio.

### Engine architecture

`FiniteModelEngine(domain_size, ...)` owns the complete finite-model route:

```text
compile source and target once
→ build cell/assignment constraint graph
→ propagate possible-value domains to a fixed point
→ branch by MRV and dynamic constraint influence
→ learn invocation-local sound nogoods
→ prune under a conservative partial-table stabilizer
→ canonicalize the complete table
→ independently replay source and target
→ emit one generic Fin n certificate
```

An `n`-element magma is a row-major `n*n` table. Every partial cell is a
bitmask of possible values in `0..n-1`; a singleton is an assigned cell and
the full bitmask is `UNASSIGNED`. No propagation step guesses a value. The
source and target use the same compiled subterm DAG and the same total and
partial evaluators for every domain size.

Fixed-point propagation applies:

- intersection of the possible values of source-equality roots;
- contradiction when two determined source sides differ;
- singleton reduction;
- target-root disequality propagation for a selected witness;
- contradiction when a selected target witness is forced equal.

The static constraint graph maps table cells to source and target assignments
with a direct dependency. Dynamic activity adds cells exposed while evaluating
nested terms in the current state. Branch selection is deterministic:
minimum remaining values, then greatest unresolved source influence, then
greatest target influence, then row-major cell index.

When a branch is exhaustively contradictory, the engine records the singleton
cell facts that imply the contradiction. Source nogoods are valid throughout
that invocation; target-disequality nogoods are scoped to their exact target
witness. A timeout or state-budget exit never learns a nogood.

Partial symmetry is intentionally conservative. A permutation may prune only
if it fixes every element used by the selected target witness, maps the
current constrained-cell set onto itself, and produces a lexicographically
smaller possible-value state. Source laws are invariant under relabelling and
the fixed witness remains the same, which justifies this orbit pruning without
assuming idempotence. Complete tables retain the existing full `n!`
canonicalization.

The engine exposes `build_constraints`, `propagate`, `branch`, `replay`,
`canonicalize`, and `emit_certificate`. The old Fin-2 enumerator,
Fin-3-specific partial evaluator, Fin-3 relabelling/canonicalization helpers,
`Fin3Search`, and separate FALSE-certificate entry point were removed. The
remaining complete enumeration is a generic reference mode used by Fin 2 and
bounded diagnostics.

### Generic replay and certificates

Replay is independent of search caches and accepts an arbitrary `n`. It checks
the exact `n*n` table shape and range, byte-exact serialization, every source
assignment, the stored target witness, and a genuine target failure. Only a
successful replay reaches `emit_fin_certificate`, whose Lean output varies
only in `Fin n` and the serialized table dimensions.

The generic synthetic suite runs all three sizes through these same methods:

| Domain | Route | Replay | Official Lean certificate |
|---|---|---|---|
| Fin 2 | complete generic enumeration | pass | accepted |
| Fin 3 | target-guided generic CSP | pass | accepted |
| Fin 4 | target-guided prototype | pass | accepted |

The Fin-4 proxy found its model in 19 states and 21 propagation rounds, with
61 domain reductions, 12 branch choices, maximum depth 12, and a 287-byte
certificate. It is a capability check, not a benchmark promotion.

The full finite-model proxy result remains 13 accepted FALSE, two accepted
TRUE controls, and one required bounded abstention. It additionally forces
fixed-point propagation, MRV, nogood learning and reuse, stabilizer pruning,
corrupt-replay rejection, and completion immediately before deadline. The
existing equality-chain suite remains 9/9; source re-entry remains eight TRUE,
two FALSE, and one bounded abstention; and the contextual research audit
remains 12 independently accepted TRUE, three FALSE, and one bounded
abstention. Rejected judge calls and LLM calls are zero.

### Frozen compatibility evaluation

No configuration selection or search-budget increase was performed. The
existing equation-content SHA-256 split and promoted 0.5-second Fin-3
configuration were retained unchanged.

| Evaluation | Accepted TRUE | Accepted FALSE | Unresolved | Runtime |
|---|---:|---:|---:|---:|
| `sample_20` | 1 | 10 | 9 | 36.64 s |
| Development half | 34 | 37 | 29 | 141.07 s |
| Holdout half | 32 | 57 | 11 | 165.39 s |
| Clean `sample_200` | 66 | 94 | 40 | 318.92 s |

Every one of the 160 frozen accepted rows retains its verdict. The score gain
is deliberately zero: this pass proves the replacement architecture before a
Fin-4 promotion experiment. Incorrect, incomplete-proof, malformed, unparsed,
replay-failure, and Lean-rejection counts are all zero.

The clean full run is 21.96 seconds slower than the previous 296.96-second
run, a 7.4% wall-time increase. At the same time, the generic Fin-3 CSP reduces
its 50 production attempts from 197,778 to 73,895 partial states. Its aggregate
engine metrics are:

| Metric | Aggregate |
|---|---:|
| Propagation rounds | 55,157 |
| Domain reductions | 66,065 |
| MRV reductions | 3,990 |
| Nogoods learned / reused | 35,989 / 23,079 |
| Safe partial-symmetry prunes | 337 |
| Branch choices / values | 24,523 / 73,093 |
| Mean branch factor | 2.981 |
| Maximum depth | 9 |
| Fin-3 hits | 10 |
| Maximum finite certificate | 271 bytes |
| Maximum finite replay time | 0.000101 s |

The larger wall time despite fewer states measures the cost of repeated
possible-value propagation and activity scoring in Python. This is an
optimization target, not a reason to weaken the verified search.

The final solver is 104,686 bytes (SHA-256
`c88b9d78daabde4ab099dffef807a8d5aaac803b5b883275a3b4a0cfd6a31816`),
well below the 500,000-byte cap. The largest certificate in the clean
`sample_200` run is 1,008 bytes. The unmodified Solo harness passes 66/66 and
the unmodified Marathon harness passes 25/25. The compact validation manifest
records hashes of each isolated output; generated benchmark logs remain local
rather than adding bulky artifacts to Git.

The residual set is unchanged: 34 unresolved TRUE rows and six unresolved
FALSE rows. Of the latter, four have Fin-3 source models but every such model
satisfies the target, and two have no Fin-3 source model. These are bounded
order-at-most-three obstructions, not implication proofs.

The next constructor should be a separate **Fin-4 promotion pass using this
generic engine**, retaining the same development/frozen/holdout protocol.
The first capability improvement should be stronger generic support
propagation for nested operation nodes and cheaper incremental activity
updates, followed by the existing target-guided search—not a larger blind
budget and not exhaustive `4^16` enumeration.

## Bounded Fin-4 promotion experiment

This separate capability pass started from
`fb671c7a6a56cea3fa5bc6273b8cb48daa66f6a8`. The implementation commit is
`8088bc2666839eedd165433e75a14512579178be`
(`add bounded Fin 4 finite-model promotion route`). The exact 104,686-byte
starting solver is preserved as
`experiments/mathgraph/regressions/solver_fb671c7.py`, SHA-256
`c88b9d78daabde4ab099dffef807a8d5aaac803b5b883275a3b4a0cfd6a31816`.
The 66 TRUE / 94 FALSE production floor and every existing verdict remained
frozen.

The result is a **capability success but promotion failure**. Three genuine
order-4 countermodels were officially accepted on development, but the
one-shot holdout gained zero FALSE cases. `PROMOTED_FIN4_PORTFOLIO` therefore
remains empty and production remains 160/200.

### Frozen artifacts and preregistration

Before implementation, the regression gate was extended to verify the hashes
of the current sample results, both exact content-hash split artifacts, all
constructor suites, the generic-engine summary, and the frozen solver. Every
experimental invocation used a unique temporary result path. The
preregistered grid fixed probe, fast, medium, and deep bounds before accepted
IDs were inspected.

| Configuration | Witness cap | State cap | Time | Model bank |
|---|---:|---:|---:|---:|
| Fin4-probe | 16 | 10,000 | 0.20 s | 4 |
| Fin4-fast | 64 | 75,000 | 0.75 s | 16 |
| Fin4-medium | 256 | 400,000 | 3.0 s | 64 |
| Fin4-deep diagnostic | 256 | 2,000,000 | 15.0 s | 256 |

The deep configuration was never production-eligible. Search budgets were not
increased after results were observed.

### Frozen-engine profile

The unchanged generic engine was profiled on all 29 development residuals, a
content-hash-selected structural sample, and the six known FALSE residuals.
Across the sampled initial source constraints, root forms were:

| Root result | Count |
|---|---:|
| Known singleton | 7,120 |
| Direct table cell | 128 |
| Nested multi-cell support | 11,344 |

This supports the nested-term hypothesis, but timing showed that implementation
cost mattered equally. Frozen diagnostic time was 32.74 seconds in repeated
propagation scans, 27.62 seconds in linear nogood lookup, 18.25 seconds in
activity recomputation, 2.02 seconds in symmetry, and 0.0003 seconds in
canonicalization. Certificate emission and replay were not bottlenecks.

The unchanged probe already found one development order-4 model in about
0.046 seconds. Deep diagnostics found three of the six known FALSE residuals,
showing that model order was useful before any implementation change.

### Sound nested support propagation

For each fixed variable assignment, the compiled term DAG now computes a
memoized possible-value bitmask for every node. Variables have singleton
support. For an operation node `u ◇ v`, its support is the union of
`table_domain[a,b]` over every `a` and `b` in the child supports. This is an
over-approximation: correlations between child values may add impossible
pairs, but no attainable value is removed.

For a source equality, disjoint root supports reject the branch. Direct root
cells are intersected with the common support. A nested root is restricted
only when exactly one child-value pair has a table-cell domain intersecting
the required common support. In that case any satisfying completion must use
that pair, so restricting its responsible cell is sound. No general inverse
operation or correlation assumption is made.

For a selected target disequality, disjoint supports guarantee the witness;
the same singleton rejects it; and a singleton opposite a direct root cell
removes that singleton value. Overlapping non-singleton supports remain
pending and are never treated as equality.

### Incremental queue, caches, and reversible state

Every source assignment has a conservative dependency set derived from its
compiled support closure. Changed table cells enqueue only possibly affected
constraints. Per-evaluation DAG support arrays are epoch-local and repeated
subterms reuse their already computed child supports.

Fin-4 branching uses one mutable domain vector and a reversible trail.
Recursive return restores domain changes to the branch mark; propagation,
assignment, and rollback no longer copy the entire table state. Activity uses
conservative support influence, target participation, equality frequency,
nogood conflict activity, recent contradiction activity, and a deterministic
cell tie-break.

Value ordering first prefers stronger target disequality support, then avoids
immediate source-support contradictions, maximizes source intersections, and
uses numeric order last. This is an ordering heuristic only; it never removes
a domain value.

Invocation-local nogoods are indexed by their rarest literal. Source
contradictions are globally scoped within the invocation; target contradictions
remain scoped to their exact target witness. Small nogoods receive bounded
deletion tests, and a literal is removed only when propagation independently
reproduces a contradiction. Timeout and state exhaustion never learn a
nogood.

The existing conservative partial stabilizer is unchanged. Metrics were added
for permutations tested, time, and states pruned. Development symmetry-on
used fewer states and slightly less wall time than symmetry-off, so it remained
enabled. Complete tables still use full `n!` canonicalization.

Target assignments are structurally ranked and deduplicated by equality
pattern under the blank-table element-relabelling action. Cardinality buckets
are interleaved so a small witness budget includes structurally different
patterns. No ID, label, equation literal, or benchmark-membership feature is
available to the route.

### Synthetic and metamorphic verification

The 20-case Fin-4 suite produced 17/17 officially accepted positive
certificates, one TRUE control with no FALSE judge call, and one required
variable-cap abstention. Four additional presentations—variable renaming,
source reversal, target reversal, and term mirroring—were independently
searched, replayed, and officially accepted. Element relabelling was also
replayed.

Coverage includes:

- an exhaustively established no-countermodel-of-order-at-most-three case;
- nested support, source-support disjointness, and target-support
  disjointness;
- direct-cell singleton removal and repeated-subterm caching;
- a stored four-element target witness;
- noncommutative, nonassociative, and no-idempotent Fin-4 tables;
- target-guided versus source-only search;
- source and scoped-target nogood reuse;
- symmetry on/off verdict equivalence;
- corrupted table and serialization rejection;
- completed-prefix replay after deadline;
- unchanged Fin-2 and Fin-3 replay/certificate paths.

On the minimal synthetic case, candidate search used 25 states versus 444 for
the frozen engine and 1,234 for source-only search. The largest Fin-4
certificate is 287 bytes.

### Development selection

The selected support/incremental/symmetry policy was frozen at solver SHA-256
`ddb646624106d143a6b0882b1ec46fa9e047dc40214310010b5dda89f55f2eb7`
before holdout.

| Configuration | Attempts | Accepted gains | Engine time | States |
|---|---:|---:|---:|---:|
| Fin4-probe | 29 | 2 | 5.15 s | 12,315 |
| Fin4-fast after probe miss | 27 | 1 | 15.39 s | 36,378 |
| Fin4-medium after fast miss | 26 | 0 | 32.25 s | 70,356 |

Development moved from 34 TRUE / 37 FALSE to **34 TRUE / 40 FALSE**.
Probe plus fast cost 20.55 pure engine seconds, or 6.85 seconds per development
gain. Medium added no independent value and remained diagnostic.

The three accepted models all have minimal order four because their existing
order-at-most-three searches were exhaustive. Each stored target witness uses
two elements. Probe contributed two certificates and fast one; all certificates
were 287 bytes.

Aggregate selected development metrics:

| Metric | Probe | Fast |
|---|---:|---:|
| Propagation rounds | 12,368 | 35,739 |
| Constraint evaluations | 489,254 | 1,459,299 |
| Term support evaluations | 5,801,654 | 17,608,128 |
| Support-cache hits | 6,427,042 | 19,342,296 |
| Domain reductions | 26,859 | 80,862 |
| Forced assignments | 8,859 | 26,779 |
| Support-disjoint contradictions | 7,318 | 22,693 |
| Nogoods learned / minimized / reused | 10,922 / 184 / 655 | 33,293 / 174 / 1,608 |
| Symmetry permutations / prunes | 75,599 / 364 | 219,857 / 526 |
| Mean branch factor | 3.942 | 3.960 |
| Maximum depth | 13 | 13 |

### Untouched holdout and promotion decision

The frozen solver and two-stage portfolio were run once on the holdout. The
result stayed **32 TRUE / 57 FALSE**, with zero Fin-4 gain and zero invalid
outcome. Probe and fast each made 11 attempts, used 10,562 combined states,
and cost 5.35 pure engine seconds.

Post hoc label analysis explains the zero: all six known FALSE residuals happen
to lie in the content-hash development half, while the 11 holdout residuals
are known TRUE. This fact was not used by routing or configuration selection.
The preregistered requirement was nevertheless holdout FALSE gain at least
one, so promotion correctly failed. Neither probe nor fast is enabled in
production.

### Clean production and official gates

| Metric | `sample_20` | `sample_200` |
|---|---:|---:|
| Accepted TRUE | 1 | 66 |
| Accepted FALSE | 10 | 94 |
| Total | 11 | 160 |
| Unresolved | 9 | 40 |
| Runtime | 39.07 s | 303.33 s |

The clean full runtime is 15.59 seconds lower than the prior generic-engine
318.92-second run and 6.37 seconds above the 296.96-second pre-refactor run.
The improvement comes from generic nogood indexing and lower-overhead state
management; Fin 4 is disabled in production. Because the promoted gain is
zero, seconds per promoted acceptance is undefined.

The final solver is 130,559 bytes, safely below the 500,000-byte limit. Solo
passes 66/66 and Marathon 25/25. The generic finite-model suite, equality
chains, source re-entry, and contextual research suites all retain their
expected accepted/abstention results. Incorrect, incomplete, malformed,
unparsed, replay-failure, Lean-rejection, and LLM-call counts are zero.

Production residuals remain 34 known TRUE and six known FALSE. Diagnostic
Fin-4 search certifies three of those six FALSE rows, leaving three for which
the frozen portfolio reached no source model or target-falsifying model. The
dominant remaining finite-model obstruction is therefore not certificate
generation but finding any useful order-4 source model within small bounds.

The next pass should not increase Fin-4 budgets or proceed directly to Fin 5.
The exact next experiment should create a **balanced promotion holdout for
FALSE-constructor evaluation**, derived only from equation-content hashes but
stratified before constructor tuning so both halves contain unresolved finite
countermodel opportunities. Re-evaluate the already frozen probe route on that
audit split without changing its code. Only if that independent audit
transfers should a structural router be considered for production.

## Sealed external Fin-4 constructor audit

The requested follow-up started from
`1e2d896f0bedc682cb1bee21717ce2d6ed3f48c8`. The audit and promotion
implementation commit is
`b0152176e431b2d2ba1a2d3c5061cb2999fab09c`. Before any audit execution the
solver was verified byte-for-byte at SHA-256
`ddb646624106d143a6b0882b1ec46fa9e047dc40214310010b5dda89f55f2eb7`.
No propagation, witness ordering, branching, nogood, symmetry, budget, replay,
or certificate setting changed before the result was closed and hashed.

The old content-hash holdout was unsuitable specifically for Fin-4 transfer:
its 11 residuals were all TRUE, while all six residual FALSE opportunities
were in development. Its original non-promotion decision remains valid, but
zero recoverable FALSE rows made it unable to estimate Fin-4 recall.

### Provenance and sealed construction

The external source was the locally cached official-format `normal`, `hard1`,
`hard2`, and `hard3` corpora under `/Users/heath/Documents/SAIR`, containing
1,669 labelled rows. The builder normalized both equations by parsing and
canonical rendering, then hashed the ordered source-target pair. It scanned
the samples, every constructor suite, the Marathon fixture, and historical
result JSON. The provenance registry contains 355 previously used content
pairs. It excluded 116 candidate occurrences by prior content hash, leaving
1,553 unique external candidates.

The builder used no Fin-4 result. Exact Fin-2 and Fin-3 screening identified
153 FALSE opportunities with no countermodel of order at most three. A
deterministic seed,
`fa92d10462bbf183fc17dc47dedc69902d8a7e8c20287e4a5e237826ee67cc90`,
was derived as specified from the starting HEAD and audit version. It selected
40 structurally diverse FALSE opportunities and greedily matched 40 TRUE
controls. Twenty of 40 pairs matched the complete structural bucket; matching
distance was 4.480 mean, 5.708 median, and 8.333 maximum.

The label-bearing builder wrote separate inputs and label files. The runner
accepted only the input, manifest, and preregistration paths; it had no label
argument or label-file constant. The complete raw result was closed at
SHA-256
`3520ba599ce40227a54ca800fec7b0bf1930fa522785e29f2afc9f5c26148953`
before evaluation loaded the sealed labels. This is a reproducible
process-separation and hashing mechanism, not cryptographic protection from a
malicious operator.

| Artifact | SHA-256 |
|---|---|
| label-hidden inputs | `42f3680536f5bdcfe0e63b9d4eb977be4515ac978ea49088c86f4011c144c30c` |
| sealed labels | `511a818977434e5dc6abd8bae11ce8de707d76f3fa24c97c09ae246727a0ce68` |
| provenance registry | `79c2da6cb646bdec88bf7ad90da7673055f2104e86192da0e3f241ee69162ec1` |
| preregistration | `cb75578cb9b3a11ac56f08e8b4cfd1cadaafaad3e897e813edd8decb7bc44915` |

This meets the `external-large` definition: 40 previously unused FALSE rows,
40 matched previously unused TRUE controls, the official judge contract, and
complete provenance hashes.

### Preregistered result

The production comparator accepted none of the 40 FALSE opportunities, as
intended by selecting rows with exhaustive no-countermodel-of-order-at-most-
three records. Existing TRUE constructors accepted eight of the 40 controls.

| Frozen configuration | Marginal external FALSE gain |
|---|---:|
| Fin4-probe | 17 |
| Fin4-fast after probe miss | 2 |
| Fin4-medium after fast miss, diagnostic | 1 |
| Fin4-deep on the preregistered ten-row subset | 0 |

Probe plus fast recovered 19/40 baseline-unresolved FALSE rows, or 47.5%.
The Wilson 95% interval is 32.94%–62.50%; the 10,000-replicate bootstrap
stratified over 37 source-equation clusters is 30.95%–64.86%. The gains span
19 source families; no family contributes more than two. They span shallow
and nested terms, one-to-two and three-plus source-variable strata, and both
the no-Fin-3-source-model and Fin-3-source-models-satisfy-target phenotypes.
Witness cardinalities are seven of size one, ten of size two, and three of
size three.

Probe plus fast consumed 122.16 seconds across the 72 baseline-unresolved
audit rows, or 6.43 seconds per added FALSE. It used 120,753 partial states,
119,096 propagation rounds, 3,007,666 constraint evaluations, 37,466,076
term-support evaluations, 43,315,984 support-cache hits, 111,850 learned
nogoods (911 minimized, 4,571 reused), and 732,571 symmetry permutation tests
with 1,731 prunes. Maximum depth was 14.

All 20 discovered tables replayed and received official acceptance. No TRUE
control caused a Fin-4 judge call. Incorrect, malformed, incomplete,
replay-failed, Lean-rejected, and unparsed counts are zero. With zero observed
invalid outcomes over 20 emitted certificates, the one-sided 95% upper bound
on the conditional invalid-certificate rate is 13.91%; this finite audit does
not prove universal precision.

Every hit was checked under variable renaming, source-side reversal,
target-side reversal, mirrored term presentation, and element relabelling.
All 100 constructed certificates were officially accepted. The unchanged
search re-found 76/80 searched presentations within the same wall budgets;
the remaining four still had officially replayed valid transformed tables and
represent timing-limited search variance, not verdict variance.

The three old development hits remain historical evidence only. Their content
hashes, frozen route, states, time, witness size, and canonical table are
recorded in `fin4_promotion_summary.json`: two probe hits used 25 and 27 states
in 0.009 and 0.026 seconds, while the fast hit used 1,238 states in 0.483
seconds. All have exhaustive order-at-most-three obstructions, two-element
witnesses, distinct canonical tables, and 287-byte certificates. None enters
the external numerator.

All preregistered promotion conditions passed: 40 external opportunities,
19 gains against a required four, positive bootstrap lower bound, gains in
multiple structural families, no single-source dependence, zero invalid
outcomes, 6.43 seconds per external gain, and preservation of the production
floor.

### Minimal production promotion

Production first tested the frozen probe/fast portfolio and gained two sample
FALSE rows, both from probe. Following the preregistered minimization rule,
fast remains diagnostic and production promotes only unchanged Fin4-probe:
16 target witnesses, 10,000 states, 0.20 seconds, and four retained source
models. It runs only after Fin 3 on rows still unresolved.

| Metric | Frozen production | Probe-only production |
|---|---:|---:|
| Accepted TRUE | 66 | 66 |
| Accepted FALSE | 94 | 96 |
| Total | 160 | **162** |
| Unresolved | 40 | 38 |
| Full runtime | 318.92 s | 332.30 s |

The authoritative runtime increase is 13.38 seconds, or 6.69 seconds per new
acceptance. Against the paired clean disabled run of 314.4 seconds, the
increase is 17.9 seconds, or 8.95 seconds per gain. Both satisfy the preferred
runtime-value threshold. The final probe made 40 attempts, used 16,294
partial states, learned 14,544 nogoods, and produced two officially accepted
Fin-4 certificates. The final solver is 130,752 bytes with SHA-256
`a5493e0b60b7c92bc5f76381f778c5f17fcb2c43994654da717e013c4e1cbe56`.

`sample_20` remains 1 TRUE / 10 FALSE. Solo is 66/66 and Marathon is 25/25.
The generic finite-model, 20-case Fin-4, nine-case equality-chain,
source-reentry, and contextual research suites all pass their exact accepted
and bounded-abstention contracts. LLM calls and all invalid outcome categories
remain zero.

The production residual is now 34 known TRUE and four known FALSE. The
dominant overall obstruction is therefore deterministic TRUE reach, not small
finite-model coverage. The next pass should add a broad, proof-producing TRUE
constructor using bounded equational normalization with independently replayed
critical consequences, evaluated on a new content-hash development/holdout
split. Fin4-fast and medium should remain diagnostics; Fin 5 should wait until
the four FALSE residuals have an external model-order profile showing that a
higher-order ladder is the limiting factor.

## Proof-producing equational normalization audit

This pass started from
`3215158571e2c15dbf8bfaa410c5beb4e84dec61`. The implementation commit is
`3cf9660031a46e09cfa5e5498d885f06945ae294`. Before implementation, the
production solver was preserved byte-for-byte as `solver_3215158.py`:
130,752 bytes at SHA-256
`a5493e0b60b7c92bc5f76381f778c5f17fcb2c43994654da717e013c4e1cbe56`.
The regression manifest records every one of the 66 TRUE and 96 FALSE
accepted row verdicts, rather than enforcing only aggregate counts.

### Constructor and trusted boundary

`EquationalNormalizer` is a bounded compilation and proof-compression layer.
It generates concrete source instances from source/target variables, target
subterms, shallow terms, and variable-identification substitutions. It adds
renamed first-order and exact proper overlaps and exact-endpoint compositions.
Every consequence is represented by a proof DAG and replayed before it can
become a rule.

The selected orientation is the target-independent well-founded order

```text
term size
→ term depth
→ nonlinear repetition penalty
→ distinct variables
→ canonical prefix serialization
```

Only strict decreases become rules. Alpha-equivalent rule patterns are merged,
the cheapest proof is retained, and the frozen coverage-diverse selector
chooses a bounded target-relevant rulebook. Normalization is deterministic
innermost rewriting. Each step records its path, rule, match substitution,
before/after terms, and decrease. The independent trace replayer redoes
schematic matching, repeated-variable checks, context replacement, and proof
DAG validation without calling consequence search.

The trusted proof boundary did not grow. Certificates use only universally
quantified source instantiation, reflexivity, symmetry, transitivity, and
`congrArg`. The left and right target traces must reach exactly the same
canonical term; similar, alpha-equivalent, or merely overlapping normal forms
are insufficient. Local critical-pair inspection is a rulebook-quality metric,
not a claim of global confluence.

The frozen diagnostic portfolio is:

| Configuration | Time | Consequences | Decreasing rules | Selected rules | Max term |
|---|---:|---:|---:|---:|---:|
| Norm-probe | 0.20 s | 250 | 32 | 8 | 15 |
| Norm-fast | 0.75 s | 800 | 64 | 16 | 17 |
| Norm-medium | 3.00 s | 2,000 | 128 | 24 | 19 |
| Norm-deep diagnostic | 15.00 s | 4,000 | 256 | 48 | 21 |

Contextual overlap and narrowing remain disabled in production. The
normalizer's promoted portfolio is also empty.

### Synthetic and development results

The equation-only synthetic suite has 30 cases. Twenty-four positive
certificates were officially accepted. Six abstention, corruption, and FALSE
controls made no incorrect TRUE call. Corrupted rule provenance and corrupted
match substitutions were rejected. The largest accepted synthetic proof DAG
has 11 nodes and the largest certificate is 763 bytes.

The preregistered development grid compared size-first and depth-first
orientation priorities with coverage-diverse and reduction-utility selectors,
using probe, fast, and medium without changing their bounds. Production before
normalization was 34 TRUE / 39 FALSE on development, with 27 unresolved rows.
Every configuration gained zero. The frozen tie-break selected size-first plus
coverage because it was the simplest candidate; no accepted IDs or row-specific
exceptions entered selection.

This is a useful negative result. The medium diagnostic generated many valid
decreasing rules, but on the 34 full-sample TRUE residuals 31 rulebooks never
matched either target side, two reduced at least one side but ended at distinct
normal forms, and one required a nonlocal or expansion-first step. No
normalization or consequence budget was exhausted. The dominant failure is
representation mismatch, not too few rules.

### Sealed external TRUE audit

Provenance was rebuilt to include the earlier Fin-4 audit, all samples,
constructor suites, and accessible historical artifacts. Normalized ordered
source-target content hashes excluded 196 previously used occurrences. The
four cached official-format corpora supplied 1,473 unique candidates after
exclusion.

The deterministic seed was
`4b938d37735f527f09ee5bf78ad091b24f62fd9a7ee894498b3eceb31399c4e9`.
The builder selected 40 previously unused labelled TRUE rows on which the
162/200 production solver abstained. It screened a 73-row baseline-unresolved
FALSE pool and selected 40 nearest-neighbour controls. Matching distance was
4.8125 mean, 4.5 median, and 13.75 maximum.
The compact matcher used equation structure, repetition signatures, Fin-2
source/countermodel counts, and direct-instance counts. It did not recompute
full Fin-3/Fin-4 or equality-graph profiles for all 1,473 candidates; this is a
matching-quality limitation, not label leakage.

The runner accepted no label path and asserted the frozen implementation hash
`b096ebef09a5cc11de9ad22f37a196111d29979beb8f759463643bba44f6b231`.
It closed the complete raw output at SHA-256
`72d0b298d0df2e11faadb626379eaa40eddff2b2d881da6e1743ec7ee253f62a`
before the evaluator loaded labels. As with the Fin-4 audit, process separation
and hashes provide experimental integrity, not cryptographic protection from a
malicious operator.

| Artifact | SHA-256 |
|---|---|
| provenance | `7157a5f89f34968a65596b6c4dbca61241711b45869544fcb0f6f0045bf6b56e` |
| audit manifest | `30b11d194812a43e5937a99723cdb2e39fdb7d53f90f96040ea8afde8c8fbd80` |
| label-hidden inputs | `7c5330e9b7fd58ae7ebedbb603a4239380540fdcc6e04307b67c932fcf5c9405` |
| sealed labels | `25682b32d89d73ff232e2ec0c7e840cc8e1f275547babce3505d8f918da3a5f6` |
| preregistration | `1affb70fe97a809fb2337a2719276d02dc8e65be2294945efb23f0f958f72403` |
| external summary | `1cd5b3c2851e919f4c8fbbf775f62e431914f966f8f01b6c0ab4361f3a9439a5` |

The audit is externally balanced: 40 unused TRUE opportunities and 40 matched
unused FALSE controls. Probe, fast, medium, and the preregistered ten-row deep
subset all gained zero. External recall is 0/40; its Wilson 95% interval is
0%–8.76%, and the source-cluster bootstrap interval is 0%–0%. The engine used
150.05 seconds over 250 attempts. With no gain, seconds per added TRUE is
undefined.

Across the external audit it generated 150,514 source instances, replayed
49,321 candidate equalities, retained 20,021 decreasing rules, removed 28,802
alpha duplicates, selected 4,320 rules, and inspected 13,784 local critical
pairs (10,259 joined and 3,525 unresolved). It performed only 21 target rewrite
steps in total and recorded 250 distinct-normal-form abstentions. Consequence
and normalization budget exits were both zero.

No FALSE control produced a candidate or TRUE judge call. There were no
incorrect, malformed, incomplete, unparsed, Lean-rejected, or external replay
failures. There were no external hits, so the required metamorphic hit audit is
vacuous rather than evidence of invariance.

The preregistered rule required at least four external gains
(`max(3, 10% of 40)`), a positive source-cluster bootstrap lower bound, three
source families, and a full-sample TRUE gain. It therefore failed decisively.
Medium and deep do not become production routes.

### Clean production decision

Production remains unchanged:

| Set | TRUE | FALSE | Total | Unresolved |
|---|---:|---:|---:|---:|
| sample_20 | 1 | 10 | 11/20 | 9 |
| development | 34 | 39 | 73/100 | 27 |
| holdout | 32 | 57 | 89/100 | 11 |
| sample_200 | 66 | 96 | **162/200** | 38 |

The clean full run was 318.25 seconds, 14.05 seconds below the frozen
332.30-second measurement; since no constructor was promoted, this is run
variance rather than a claimed speed improvement. Net promoted gain is zero
and seconds per added acceptance is undefined. The implementation solver is
177,344 bytes, below the 500,000-byte intake limit.

All 162 accepted verdicts were preserved. `sample_20`, both content-hash
halves, and the full sample had zero rejected judge outcomes and zero LLM
calls. The nine-case equality-chain suite, source-reentry suite, contextual
research suite, generic finite-model suite, and Fin-4 capability suite retained
their exact accepted/abstention contracts. The Solo solver cases are 66/66 and
Marathon is 25/25. The repository-wide Solo command also reported two
submit-CLI ANSI-style failures unrelated to the MathGraph submission; all 66
solver cases, 79 public attacks, and four infrastructure attacks passed.

The residual remains 34 TRUE and four FALSE. The dominant TRUE phenotype is
31/34 cases with many replayed decreasing consequences but no rule matching a
target subterm. The next pass should therefore test one bounded,
proof-producing **expansion-before-reduction** layer: mine schematic,
target-independent lemmas by anti-unifying replayed consequences, permit one
strictly bounded expansion into a normalization-recognized representation, and
then use the existing explicit trace compiler. It must receive another sealed
external TRUE audit before promotion. Increasing normalization budgets, adding
more undirected contextual edges, or moving directly to Fin 5 is not supported
by this evidence.

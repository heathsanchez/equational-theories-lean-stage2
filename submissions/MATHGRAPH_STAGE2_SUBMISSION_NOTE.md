# MathGraph Stage 2 submission note

The submitted `solver.py` contains two Base85-encoded, zlib-compressed UTF-8 Python source payloads.

They contain generic solver code only:

1. `_STAIR_ENGINE_PAYLOAD` — the generated deterministic TRUE proof-search / paramodulation engine used by the Stair-climber specialist.
2. `_STAIR_REPLAY_PAYLOAD` — an independent deterministic parser/replayer for compact equality proof plans returned by that engine.

They do **not** contain benchmark problem IDs, equation IDs, stored benchmark answers, stored Lean certificates, or problem-specific proof recipes.

The payloads are generated reproducibly by `experiments/mathgraph/build_stair_climber_specialist.py`. That builder reads the audited generic completion/search source and independent replayer source, serializes each source string as UTF-8, compresses it with `zlib.compress(..., 9)`, and encodes the compressed bytes with Base85 for embedding into the single-file solver. At runtime, `solver.py` Base85-decodes and zlib-decompresses those source strings into isolated namespaces.

For the canonical solver currently qualified in this repository, the decoded payloads have these SHA256 digests:

- Stair engine decoded source: `f71be6cf19867d79ed387f94032dfd4cb29e882b3539edd056a2d9b648eacbd8`
- Independent replayer decoded source: `826ae5af09d8b84bdc4d303ece8f253484f7fd530d24bc85f6837c3584edbc7e`

The solver also contains a finite model bank in ordinary uncompressed Python literals. Countermodels selected from that bank are rechecked against the incoming source and target equations before any FALSE certificate is submitted to the official judge.

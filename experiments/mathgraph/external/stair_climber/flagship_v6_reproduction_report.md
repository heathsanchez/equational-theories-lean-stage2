# Flagship-v6 reproduction report

## Result

The published single-file solver was reproduced byte-for-byte from the
downloaded `build.py` and its audited inputs.

- Published SHA-256:
  `48a782d566a556e8b9e66ec64d85dab181ce231d01c6663c26c9f553886ee1b8`
- Reproduced SHA-256:
  `48a782d566a556e8b9e66ec64d85dab181ce231d01c6663c26c9f553886ee1b8`
- Size: 371,057 bytes
- Stage 2 size limit: 500,000 bytes
- Reproduction status: exact

The build script was inspected before execution. It performs deterministic
source splicing and file IO; it does not invoke a shell, network service,
external prover, or LLM.

## Runtime dependencies

The resulting solver is a single Python file using the Python standard library
and the normal Stage 2 solver protocol. The isolated paramodulation search is
pure Python. It translates successful searches into congruence proof plans and
then Lean certificates.

The full flagship is not suitable for wholesale integration into MathGraph:
one countermodel stage performs public equation-ID lookup, and the released-800
first-candidate audit exposed 31 incorrect TRUE attempts on FALSE rows before
judge feedback. Those attempts are fail-closed under the real judge, but they
are unnecessary risk and cost.

## Published run record

The downloaded `v6run_stats.json` reports 1,641/1,669 solved in 27,942.32
seconds. The downloaded `v6_diff_vs_v5.json` records 28 gains, no losses, and
the same solver SHA-256.

## Licence audit

No `LICENSE` or `COPYING` file was present inside the downloaded artifact
folders. The parent Stage 2 repository is Apache-2.0. The inventory records
this distinction explicitly. Integration is limited to general
equation-driven machinery and finite table values; no certificate lookup,
problem ID, equation ID, content hash, or expected label is imported.

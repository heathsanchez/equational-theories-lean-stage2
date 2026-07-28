#!/usr/bin/env python3
"""Build a deterministic, compact paramodulator-control handoff archive."""

from __future__ import annotations

import gzip
import hashlib
import io
import json
import tarfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "colab/mathgraph_paramodulator_control_bundle.tar.gz"
MANIFEST = ROOT / "colab/experiment_bundle_manifest.json"


def selected_files():
    explicit = [
        "submissions/mathgraph/solver.py",
        "colab/data/six_residuals.json",
        "colab/data/smoke_normal_0158.json",
        "requirements-lock.txt",
        "lean-toolchain",
        "environment_manifest.json",
        "lakefile.lean",
        "lake-manifest.json",
        "experiments/mathgraph/audit_stair_climber_components.py",
        "judge/__init__.py",
        "judge/verify.py",
        "judge/JudgeMagma/Magma.lean",
        "judge/JudgeDecide/DecideBang.lean",
        "judge/JudgeFinOp/MemoFinOp.lean",
        "judge/JudgeSupport/Inspect.lean",
        "pipeline/__init__.py",
        "pipeline/proxy.py",
    ]
    files = {ROOT / path for path in explicit}
    control = ROOT / "experiments/mathgraph/paramodulator_control"
    for path in control.iterdir():
        if path.is_file() and path.suffix in {".py", ".json", ".md"}:
            files.add(path)
    for path in [
        ROOT / "colab/bootstrap_mathgraph.py",
        ROOT / "colab/run_frozen_baseline.sh",
        ROOT / "colab/run_continuation_experiment.sh",
        ROOT / "colab/README.md",
    ]:
        files.add(path)
    return sorted(files, key=lambda path: path.relative_to(ROOT).as_posix())


def main():
    files = selected_files()
    missing = [path for path in files if not path.is_file()]
    if missing:
        raise SystemExit(f"missing bundle inputs: {missing}")
    records = []
    for path in files:
        data = path.read_bytes()
        records.append({
            "path": path.relative_to(ROOT).as_posix(),
            "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest(),
        })
    manifest = {
        "schema": "mathgraph.compact-experiment-bundle.v1",
        "excluded": [
            "caches and __pycache__",
            "Lean build products and .lake",
            "old ATP outputs",
            "sealed label files",
            "unrelated experiment artifacts",
            "credentials"
        ],
        "files": records,
    }
    MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n")
    files = sorted(
        {*files, MANIFEST},
        key=lambda path: path.relative_to(ROOT).as_posix(),
    )
    with OUTPUT.open("wb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as zipped:
            with tarfile.open(fileobj=zipped, mode="w") as archive:
                for path in files:
                    data = path.read_bytes()
                    info = tarfile.TarInfo(path.relative_to(ROOT).as_posix())
                    info.size = len(data)
                    info.mode = 0o755 if path.suffix in {".py", ".sh"} else 0o644
                    info.mtime = 0
                    info.uid = info.gid = 0
                    info.uname = info.gname = ""
                    archive.addfile(info, io.BytesIO(data))
    print(hashlib.sha256(OUTPUT.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()

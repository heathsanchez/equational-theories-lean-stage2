#!/usr/bin/env python3
"""Fail-closed Colab bootstrap for the frozen MathGraph research snapshot."""

from __future__ import annotations

import argparse
import hashlib
import os
import subprocess
import sys
from pathlib import Path


REPOSITORY = "https://github.com/heathsanchez/equational-theories-lean-stage2.git"
BRANCH = "mathgraph/context-calculus-research"
# Updated by the final metadata commit to the immutable handoff commit.
PINNED_COMMIT = "8b09788b4c3ad4e09203f26c891055d4a5d9b7eb"
SOLVER_SHA256 = "fc402fae046096d99a8c01a6848bc4030d282c7f4a90ff5e9c26c3c8d8833fe1"
SOLVER_BYTES = 313240


def run(command, *, cwd=None, env=None):
    print("+", " ".join(map(str, command)), flush=True)
    subprocess.run(
        [str(value) for value in command],
        cwd=cwd,
        env=env,
        check=True,
    )


def output(command, *, cwd=None, env=None):
    return subprocess.check_output(
        [str(value) for value in command],
        cwd=cwd,
        env=env,
        text=True,
    ).strip()


def verify_solver(root):
    solver = root / "submissions/mathgraph/solver.py"
    digest = hashlib.sha256(solver.read_bytes()).hexdigest()
    size = solver.stat().st_size
    if digest != SOLVER_SHA256 or size != SOLVER_BYTES:
        raise RuntimeError(
            f"frozen solver mismatch: sha256={digest}, bytes={size}"
        )
    print(f"Frozen solver verified: {digest}, {size} bytes")


def clone_exact(target):
    if target.exists():
        if not (target / ".git").is_dir():
            raise RuntimeError(f"{target} exists but is not a Git checkout")
        remote = output(["git", "remote", "get-url", "origin"], cwd=target)
        if remote.rstrip("/") != REPOSITORY.rstrip("/"):
            raise RuntimeError(f"unexpected origin: {remote}")
        run(["git", "fetch", "origin", BRANCH], cwd=target)
    else:
        run(
            [
                "git",
                "clone",
                "--branch",
                BRANCH,
                "--single-branch",
                REPOSITORY,
                target,
            ]
        )
    run(["git", "checkout", "--detach", PINNED_COMMIT], cwd=target)
    actual = output(["git", "rev-parse", "HEAD"], cwd=target)
    if actual != PINNED_COMMIT:
        raise RuntimeError(f"checkout mismatch: {actual}")
    if output(["git", "status", "--porcelain"], cwd=target):
        raise RuntimeError("exact checkout is unexpectedly dirty")


def install_environment(root):
    home = Path.home()
    elan = home / ".elan/bin/elan"
    if not elan.exists():
        installer = Path("/tmp/mathgraph-elan-init.sh")
        run(
            [
                "curl",
                "-fsSL",
                "https://raw.githubusercontent.com/leanprover/elan/master/"
                "elan-init.sh",
                "-o",
                installer,
            ]
        )
        run(["sh", installer, "-y", "--default-toolchain", "none"])
    env = dict(os.environ)
    env["PATH"] = f"{home / '.elan/bin'}:{env.get('PATH', '')}"
    toolchain = (root / "lean-toolchain").read_text().strip()
    installed = output([elan, "toolchain", "list"], env=env).splitlines()
    if not any(line.split()[0] == toolchain for line in installed):
        run([elan, "toolchain", "install", toolchain], env=env)
    run([elan, "override", "set", toolchain], cwd=root, env=env)
    run(
        [
            sys.executable,
            "-m",
            "pip",
            "install",
            "--disable-pip-version-check",
            "-r",
            root / "requirements-lock.txt",
        ],
        cwd=root,
        env=env,
    )
    run([home / ".elan/bin/lake", "exe", "cache", "get"], cwd=root, env=env)
    run(
        [
            home / ".elan/bin/lake",
            "build",
            "JudgeMagma.Magma",
            "JudgeDecide.DecideBang",
            "JudgeFinOp.MemoFinOp",
            "JudgeSupport.Inspect",
        ],
        cwd=root,
        env=env,
    )
    return env


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repo-dir",
        type=Path,
        default=Path("/content/mathgraph-stage2"),
    )
    parser.add_argument("--skip-clone", action="store_true")
    parser.add_argument("--skip-install", action="store_true")
    parser.add_argument("--no-smoke", action="store_true")
    args = parser.parse_args()

    root = args.repo_dir.resolve()
    if args.skip_clone:
        if not (root / ".git").is_dir():
            raise RuntimeError("--skip-clone requires an existing checkout")
    else:
        clone_exact(root)
    verify_solver(root)
    env = dict(os.environ)
    env["PATH"] = f"{Path.home() / '.elan/bin'}:{env.get('PATH', '')}"
    env["PYTHON"] = sys.executable
    if not args.skip_install:
        env = install_environment(root)
    if not args.no_smoke:
        run(["bash", root / "colab/run_frozen_baseline.sh"], cwd=root, env=env)
    print("PASS")


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)

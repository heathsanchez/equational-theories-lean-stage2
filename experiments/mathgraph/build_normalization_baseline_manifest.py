#!/usr/bin/env python3
"""Compact an isolated 162/200 result into the normalization regression floor."""

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--sample200", type=Path, required=True)
    parser.add_argument("--sample20", type=Path, required=True)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    sample200 = json.loads(args.sample200.read_text())
    sample20 = json.loads(args.sample20.read_text())
    accepted200 = {
        row["id"]: row["verdict"] for row in sample200 if row.get("solved")
    }
    accepted20 = {
        row["id"]: row["verdict"] for row in sample20 if row.get("solved")
    }
    assert Counter(accepted200.values()) == {"true": 66, "false": 96}
    assert Counter(accepted20.values()) == {"true": 1, "false": 10}
    args.output.write_text(json.dumps({
        "authoritative_head": "3215158571e2c15dbf8bfaa410c5beb4e84dec61",
        "production_solver_sha256": sha256(args.solver),
        "sample_20_result_sha256": sha256(args.sample20),
        "sample_200_result_sha256": sha256(args.sample200),
        "sample_20_accepted": accepted20,
        "sample_200_accepted": accepted200,
        "sample_20_counts": {"true": 1, "false": 10},
        "sample_200_counts": {"true": 66, "false": 96},
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

"""Build deterministic cleanroom search-budget variants for held-out ablation."""

from __future__ import annotations

import argparse
from pathlib import Path


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f"expected one occurrence of {old!r}, found {text.count(old)}")
    return text.replace(old, new, 1)


def widen_proof(text, seconds):
    replacements = {
        'COMPACT_SUPERPOSITION_FAST = {\n    "seconds": 1.5,':
            f'COMPACT_SUPERPOSITION_FAST = {{\n    "seconds": {seconds},',
        '    "maximum_term_size": 55,\n    "maximum_replay_term_size": 240,':
            '    "maximum_term_size": 70,\n    "maximum_replay_term_size": 300,',
        '    "maximum_depth": 12,\n    "maximum_rules": 256,':
            '    "maximum_depth": 16,\n    "maximum_rules": 512,',
        '    "maximum_rounds": 24,\n    "new_clauses_per_round": 256,':
            '    "maximum_rounds": 64,\n    "new_clauses_per_round": 512,',
        '    "maximum_clauses": 5000,\n    "normalization_steps": 160,\n'
        '    "maximum_proof_nodes": 30000,':
            '    "maximum_clauses": 25000,\n    "normalization_steps": 256,\n'
            '    "maximum_proof_nodes": 100000,',
    }
    for old, new in replacements.items():
        text = replace_once(text, old, new)
    return text


def proof_deep(text):
    text = widen_proof(text, "10.0")
    # The ablation measures only the widened TRUE constructor. Avoid spending
    # Fin-5 time after a miss; this generated file is never a submission.
    marker = "    # BridgeIR is a TRUE-side representation constructor."
    text = replace_once(text, marker, "    return\n\n" + marker)
    return text


def proof_wide(text):
    text = proof_deep(text)
    replacements = {
        '    "maximum_term_size": 70,\n    "maximum_replay_term_size": 300,':
            '    "maximum_term_size": 90,\n    "maximum_replay_term_size": 420,',
        '    "maximum_depth": 16,\n    "maximum_rules": 512,':
            '    "maximum_depth": 20,\n    "maximum_rules": 900,',
        '    "maximum_rounds": 64,\n    "new_clauses_per_round": 512,':
            '    "maximum_rounds": 96,\n    "new_clauses_per_round": 900,',
        '    "maximum_clauses": 25000,\n    "normalization_steps": 256,\n'
        '    "maximum_proof_nodes": 100000,':
            '    "maximum_clauses": 60000,\n    "normalization_steps": 384,\n'
            '    "maximum_proof_nodes": 180000,',
        'COMPACT_SUPERPOSITION_FAST = {\n    "seconds": 10.0,':
            'COMPACT_SUPERPOSITION_FAST = {\n    "seconds": 25.0,',
    }
    for old, new in replacements.items():
        text = replace_once(text, old, new)
    return text


def proof_wide_balanced(text):
    text = proof_wide(text)
    return replace_once(
        text,
        'COMPACT_SUPERPOSITION_FAST = {\n    "seconds": 25.0,',
        'COMPACT_SUPERPOSITION_FAST = {\n    "seconds": 5.0,',
    )


def proof_balanced(text):
    text = widen_proof(text, "5.0")
    marker = "    # BridgeIR is a TRUE-side representation constructor."
    return replace_once(text, marker, "    return\n\n" + marker)


def proof_precision(text):
    marker = "    # BridgeIR is a TRUE-side representation constructor."
    return replace_once(text, marker, "    return\n\n" + marker)


def local_repair(text, salt):
    text = replace_once(
        text, "    for configuration in PROMOTED_FIN5_PORTFOLIO:\n",
        "    for configuration in ():\n",
    )
    text = replace_once(text, "        for _ in range(500):\n",
                        "        for _ in range(2000):\n")
    text = replace_once(
        text, "    local_seconds = min(4.0, max(0.1, timeout / 30.0))\n",
        "    local_seconds = min(30.0, max(0.1, timeout / 30.0))\n",
    )
    old_seed = '''        local_seed = sum(
            map(ord, problem.get("equation1", "") + problem.get("equation2", ""))
        )
'''
    new_seed = (
        "        local_seed = deterministic_model_seed(source, target, 5) ^ "
        + str(salt) + "\n"
    )
    text = replace_once(text, old_seed, new_seed)
    marker = "    # A tiny equation-blind bank of crossed-coordinate finite geometries."
    return replace_once(text, marker, "    return\n\n" + marker)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument(
        "--families", choices=("all", "proof", "local"), default="all"
    )
    args = parser.parse_args()
    base = args.base.read_text(encoding="utf-8")
    variants = {}
    if args.families in ("all", "proof"):
        variants.update({
            "coverage_balanced": widen_proof(base, "5.0"),
            "proof_balanced": proof_balanced(base),
            "proof_precision": proof_precision(base),
            "proof_deep": proof_deep(base),
            "proof_wide": proof_wide(base),
            "proof_wide_balanced": proof_wide_balanced(base),
        })
    if args.families in ("all", "local"):
        for index, salt in enumerate((0, 0x9E3779B97F4A7C15, 0xD1B54A32D192ED03, 0x94D049BB133111EB)):
            variants[f"local_repair_{index}"] = local_repair(base, salt)
    for name, text in variants.items():
        path = args.output_dir / name / "solver.py"
        compile(text, str(path), "exec")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        print(path)


if __name__ == "__main__":
    main()

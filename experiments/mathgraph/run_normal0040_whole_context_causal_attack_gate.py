#!/usr/bin/env python3
"""Frozen whole-context causal attack derived from the earlier causal harness.

The derivation is intentionally textual and assertion-guarded: it changes only
(1) protocol/result/schema labels, (2) the two host terms supplied to lifted_item,
and (3) decision labels. All search, class construction, candidate limits,
isolation, theorem geometry, and ablation code remain byte-for-byte inherited.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "run_normal0040_common_specialization_causal_attack_gate.py"
text = SRC.read_text()

repls = [
    (
        "normal0040-common-specialization-causal-attack-v1.json';OUT=ROOT/'experiments/mathgraph/results/normal0040-common-specialization-causal-attack-gate.json",
        "normal0040-whole-context-causal-attack-v1.json';OUT=ROOT/'experiments/mathgraph/results/normal0040-whole-context-causal-attack-gate.json",
    ),
    (
        "la=rou.lifted_item(m,selfm,source,target,ta,a['path'],a['side'],sa,f'ca-{i}-{j}-L')\n       lb=rou.lifted_item(m,selfm,source,target,tb,b['path'],b['side'],sb,f'ca-{i}-{j}-R')",
        "hta=apply_theta(m,ta,theta);htb=apply_theta(m,tb,theta)\n       la=rou.lifted_item(m,selfm,source,target,hta,a['path'],a['side'],sa,f'wcca-{i}-{j}-L')\n       lb=rou.lifted_item(m,selfm,source,target,htb,b['path'],b['side'],sb,f'wcca-{i}-{j}-R')",
    ),
    (
        "decision='REPRESENTATION_RESCUE_NO_CAUSAL_ATTACHMENT'",
        "decision='WHOLE_CONTEXT_REPLAY_VALID_NO_CAUSAL_ATTACHMENT'",
    ),
    (
        "decision='NO_REPLAYABLE_SPECIALIZATION'",
        "decision='NO_REPLAYABLE_WHOLE_CONTEXT_PAIR'",
    ),
    (
        "mathgraph.normal0040-common-specialization-causal-attack.v1",
        "mathgraph.normal0040-whole-context-causal-attack.v1",
    ),
]

for old, new in repls:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"frozen derivation mismatch: expected exactly one occurrence, got {count}: {old[:80]!r}")
    text = text.replace(old, new)

# Execute using the original file path so its ROOT calculation remains unchanged.
ns = {"__name__": "__main__", "__file__": str(SRC)}
exec(compile(text, str(SRC), "exec"), ns, ns)

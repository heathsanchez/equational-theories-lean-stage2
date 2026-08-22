#!/usr/bin/env python3
"""Normal-0040 transfer of the frozen bidirectional contextual residual-cut gate.

Uses the existing residual-cut implementation unchanged except for selecting
`evaluation_normal_0040` from the normal split. This is a representation
transfer test, not a new inference rule. Every generated edge remains replay-
verified from the original source law by the imported gate.
"""
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE / 'run_residual_cut_bidirectional_context_bfs_gate.py'
spec = importlib.util.spec_from_file_location('base_normal0040_bidir', BASE)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)

base.RID = 'evaluation_normal_0040'

# The upstream gate hard-codes evaluation_order5 only at dataset retrieval.
# Replace main with the same algorithm while temporarily wrapping load_dataset
# so its requested config is redirected to evaluation_normal.
_orig_load_dataset = base.load_dataset
def _load_dataset(path, config, *args, **kwargs):
    return _orig_load_dataset(path, 'evaluation_normal', *args, **kwargs)
base.load_dataset = _load_dataset

if __name__ == '__main__':
    base.OUT = HERE / 'results' / 'normal0040-bidirectional-context-gate.json'
    base.main()

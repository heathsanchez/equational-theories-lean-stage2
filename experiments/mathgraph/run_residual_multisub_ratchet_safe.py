#!/usr/bin/env python3
import json, runpy, traceback
from pathlib import Path
OUT=Path(__file__).resolve().parent/'results/residual-multisub-ratchet-gate.json'
try:
    runpy.run_path(str(Path(__file__).with_name('run_residual_multisub_ratchet_gate.py')), run_name='__main__')
except BaseException as e:
    OUT.parent.mkdir(parents=True, exist_ok=True)
    payload={'schema':'mathgraph.residual-multisub-ratchet.error.v1','status':'ERROR','error':repr(e),'traceback':traceback.format_exc()}
    OUT.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    print(json.dumps(payload,indent=2,sort_keys=True))
    raise

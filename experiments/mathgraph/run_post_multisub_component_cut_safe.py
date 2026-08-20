#!/usr/bin/env python3
import json,runpy,traceback
from pathlib import Path
OUT=Path(__file__).resolve().parent/'results/post-multisub-component-cut-gate.json'
try:
 runpy.run_path(str(Path(__file__).with_name('run_post_multisub_component_cut_gate.py')),run_name='__main__')
except BaseException as e:
 OUT.parent.mkdir(parents=True,exist_ok=True)
 p={'schema':'mathgraph.post-multisub-component-cut.error.v1','status':'ERROR','error':repr(e),'traceback':traceback.format_exc()}
 OUT.write_text(json.dumps(p,indent=2,sort_keys=True)+'\n');print(json.dumps(p,indent=2,sort_keys=True));raise

#!/usr/bin/env python3
import argparse, importlib.util, json, re, urllib.request
from pathlib import Path
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'
def load_helper():
    p=Path(__file__).with_name('run_normal0040_alpha_helpers.py')
    s=importlib.util.spec_from_file_location('h196',p); h=importlib.util.module_from_spec(s); s.loader.exec_module(h); return h
def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input'); ap.add_argument('--output',required=True); a=ap.parse_args()
    h=load_helper(); proof=next(r['proof'] for r in json.load(urllib.request.urlopen(TRACE_URL))['rows'] if r['id']==RID)
    rec={}
    for block in h.fof_blocks(proof):
        q=h.parse_fof(block)
        if not q: continue
        fid,kind,formula,tail=q; joined=','.join(tail)
        m=re.search(r'inference\(([^,\]]+).*?\[([^\]]*)\]\)\s*$', joined)
        if m:
            parents=[x.strip() for x in m.group(2).split(',') if x.strip().startswith('f')]
            rec[fid]={'inference':m.group(1),'parents':parents,'formula':formula}
    t=rec.get('f196'); out={'id':RID,'f196':t,'parents':{p:rec.get(p) for p in (t or {}).get('parents',[])}}
    Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('NORMAL0040_F196_PARENT_AUDIT',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()

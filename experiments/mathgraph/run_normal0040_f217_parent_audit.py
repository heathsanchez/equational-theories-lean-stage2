#!/usr/bin/env python3
import argparse, json, re, urllib.request
from pathlib import Path
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'; RID='evaluation_normal_0040'
def fof_blocks(text):
 out=[]; cur=[]; bal=0
 for line in text.splitlines():
  if not cur and not line.lstrip().startswith('fof('): continue
  cur.append(line); bal += line.count('(')-line.count(')')
  if cur and bal==0:
   out.append('\n'.join(cur)); cur=[]
 return out
def main():
 ap=argparse.ArgumentParser(); ap.add_argument('--input'); ap.add_argument('--output',required=True); a=ap.parse_args()
 rows=json.load(urllib.request.urlopen(TRACE_URL))['rows']; proof=next(x['proof'] for x in rows if x['id']==RID)
 wanted={'f217'}; rec={}
 for b in fof_blocks(proof):
  m=re.match(r'fof\((f\d+),\s*([^,]+),',b,re.S)
  if not m: continue
  fid=m.group(1)
  if fid not in wanted: continue
  mi=re.search(r'inference\(([^,\]]+).*?\[\s*(f\d+)\s*,\s*(f\d+)\s*\]',b,re.S)
  parents=list(mi.groups()[1:]) if mi else []
  inf=mi.group(1) if mi else ''
  rec[fid]={'inference':inf,'parents':parents,'block':b}
 out={'id':RID,'f217':rec.get('f217')}
 Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2)+'\n'); print('NORMAL0040_F217_PARENT_AUDIT',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()

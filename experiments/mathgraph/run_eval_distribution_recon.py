import csv, json, os, re, subprocess
from collections import Counter, defaultdict
from pathlib import Path

ROOT=Path('.')
OUT=Path('experiments/mathgraph/results/eval-distribution-recon.json')
SPLITS=('normal','hard1','hard2','hard3')
TEXT_EXT={'.md','.txt','.py','.json','.jsonl','.csv','.yaml','.yml','.lean','.toml'}
SKIP={'.git','.lake','lake-packages','node_modules','__pycache__'}


def files():
    for p in ROOT.rglob('*'):
        if not p.is_file() or any(x in SKIP for x in p.parts): continue
        yield p


def txt(p,limit=2_000_000):
    try:
        if p.stat().st_size>limit:return ''
        return p.read_text(errors='ignore')
    except Exception:return ''


def split_hits():
    rows=[]
    for p in files():
        low=str(p).lower(); t=''
        path_hits=[s for s in SPLITS if s in low]
        if p.suffix.lower() in TEXT_EXT: t=txt(p)
        content_hits=[s for s in SPLITS if re.search(r'(?<![a-z0-9])'+re.escape(s)+r'(?![a-z0-9])',t,re.I)] if t else []
        if path_hits or content_hits:
            rows.append({'path':str(p),'size':p.stat().st_size,'path_hits':path_hits,'content_hits':content_hits,'ext':p.suffix.lower()})
    return rows


def candidate_inventory():
    pats=('problem','selected','split','eval','test','hard','normal','benchmark','dataset')
    out=[]
    for p in files():
        low=str(p).lower()
        if any(x in low for x in pats):
            out.append({'path':str(p),'size':p.stat().st_size,'ext':p.suffix.lower()})
    return sorted(out,key=lambda r:(r['path']))[:2000]


def schema_probe(paths):
    out=[]
    for rec in paths:
        p=Path(rec['path']); ext=p.suffix.lower()
        try:
            if ext=='.csv':
                with p.open(newline='',errors='ignore') as f:
                    r=csv.reader(f); hdr=next(r,[]); n=sum(1 for _ in r)
                out.append({'path':str(p),'kind':'csv','headers':hdr,'rows':n})
            elif ext in ('.json','.jsonl'):
                if ext=='.json':
                    obj=json.loads(txt(p));
                    if isinstance(obj,list):
                        keys=sorted({k for x in obj[:100] if isinstance(x,dict) for k in x})
                        out.append({'path':str(p),'kind':'json-list','rows':len(obj),'keys':keys})
                    elif isinstance(obj,dict):
                        out.append({'path':str(p),'kind':'json-dict','keys':sorted(obj.keys())[:200]})
                else:
                    rows=[]
                    for line in txt(p).splitlines()[:5000]:
                        try: rows.append(json.loads(line))
                        except: pass
                    keys=sorted({k for x in rows[:100] if isinstance(x,dict) for k in x})
                    out.append({'path':str(p),'kind':'jsonl','rows_scanned':len(rows),'keys':keys})
        except Exception as e:
            out.append({'path':str(p),'error':type(e).__name__+': '+str(e)})
    return out


def doc_evidence():
    out=[]
    terms=re.compile(r'.{0,140}\b(normal|hard1|hard2|hard3|evaluation|held[- ]?out|selected problems|test set|distribution)\b.{0,220}',re.I)
    for p in files():
        if p.suffix.lower() not in {'.md','.txt','.py','.yaml','.yml'}: continue
        t=txt(p)
        ms=[]
        for m in terms.finditer(t):
            s=' '.join(m.group(0).split())
            if s not in ms: ms.append(s)
            if len(ms)>=20:break
        if ms: out.append({'path':str(p),'snippets':ms})
    return out[:200]


def history():
    try:
        cmd=['git','log','--all','--date=iso','--pretty=format:@@%H|%ad|%s','--name-status']
        s=subprocess.check_output(cmd,text=True,errors='ignore',timeout=60)
    except Exception as e:return {'error':str(e)}
    commits=[]; cur=None
    matcher=re.compile(r'(hard1|hard2|hard3|normal|selected|problem|eval|split|dataset)',re.I)
    for line in s.splitlines():
        if line.startswith('@@'):
            if cur and (matcher.search(cur['subject']) or cur['files']): commits.append(cur)
            bits=line[2:].split('|',2); cur={'sha':bits[0],'date':bits[1] if len(bits)>1 else '', 'subject':bits[2] if len(bits)>2 else '', 'files':[]}
        elif cur and matcher.search(line): cur['files'].append(line)
    if cur and (matcher.search(cur['subject']) or cur['files']): commits.append(cur)
    return {'matching_commits':commits[:300],'count':len(commits)}


def existing_audits():
    rows=[]
    for p in Path('experiments/mathgraph/results').glob('*.json') if Path('experiments/mathgraph/results').exists() else []:
        low=p.name.lower()
        if any(k in low for k in ('800','audit','solver','official','transfer','residual')):
            try:
                o=json.loads(txt(p)); rows.append({'path':str(p),'schema':o.get('schema') if isinstance(o,dict) else None,'top_keys':sorted(o.keys())[:80] if isinstance(o,dict) else [],'size':p.stat().st_size})
            except: pass
    return rows


def main():
    hits=split_hits(); inv=candidate_inventory(); probe=schema_probe(hits+inv)
    report={
      'schema':'mathgraph.eval-distribution-recon.v1',
      'split_hits':hits,
      'split_hit_counts':{s:sum(s in r['path_hits'] or s in r['content_hits'] for r in hits) for s in SPLITS},
      'candidate_inventory':inv,
      'schema_probe':probe,
      'documentation_evidence':doc_evidence(),
      'history':history(),
      'existing_audits':existing_audits(),
    }
    # A strict readiness signal for the next pseudo-hidden test: we need at least
    # one machine-readable candidate dataset/split artifact or explicit split refs.
    report['pseudo_hidden_ready']=bool(hits) and any(x.get('kind') in ('csv','json-list','jsonl') for x in probe)
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print('EVAL_RECON_SUMMARY',json.dumps({'split_hit_counts':report['split_hit_counts'],'candidate_files':len(inv),'schemas':len(probe),'history_matches':report['history'].get('count'),'existing_audits':len(report['existing_audits']),'pseudo_hidden_ready':report['pseudo_hidden_ready']},sort_keys=True),flush=True)

if __name__=='__main__': main()

import contextlib, hashlib, importlib.util, io, json, math, os, re, sys, time, urllib.parse, urllib.request
from collections import Counter, defaultdict
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'experiments/mathgraph/results/stage1-distribution-etp-gate.json'
SOLVER=ROOT/'submissions/mathgraph/solver.py'
HF='SAIRfoundation/equational-theories-selected-problems'
LOCAL=('normal','hard1','hard2','hard3')
TIMEOUT=2.0
N_PER_CATEGORY=24

INSERT_AFTER='''    if compact_recipe is not None and finish_compact_superposition_candidate(\n        source, target, compact_search, compact_recipe\n    ):\n        return\n'''
RETRY='''\n    retry_seconds = min(0.15, max(0.05, timeout / 10.0))\n    try:\n        retry_search = CompactSuperposition(sys.modules[__name__], source, target, time.monotonic()+retry_seconds, compact_limits)\n        retry_recipe = retry_search.solve()\n    except (KeyError, IndexError, MemoryError, RecursionError, TypeError, ValueError):\n        retry_recipe = None\n    if retry_recipe is not None and finish_compact_superposition_candidate(source, target, retry_search, retry_recipe):\n        return\n'''

def get_json(url):
    req=urllib.request.Request(url,headers={'User-Agent':'mathgraph-stage2-prep/1'})
    with urllib.request.urlopen(req,timeout=30) as r: return json.load(r)

def discover_hf_splits():
    q=urllib.parse.urlencode({'dataset':HF})
    data=get_json('https://datasets-server.huggingface.co/splits?'+q)
    names=[]
    for x in data.get('splits',[]):
        n=x.get('split')
        if n and any(k in n.lower() for k in ('normal','hard','order5')): names.append(n)
    pref=['evaluation_normal','evaluation_hard','evaluation_extra_hard','evaluation_order5']
    ordered=[x for x in pref if x in names]+[x for x in names if x not in pref]
    return ordered

def fetch_split(name):
    rows=[]; off=0
    while True:
        q=urllib.parse.urlencode({'dataset':HF,'config':'default','split':name,'offset':off,'length':100})
        d=get_json('https://datasets-server.huggingface.co/rows?'+q)
        batch=[x.get('row',{}) for x in d.get('rows',[])]
        rows.extend(batch)
        if len(batch)<100: break
        off+=len(batch)
        if off>=5000: break
    return rows

def norm_answer(v):
    if isinstance(v,bool): return v
    if isinstance(v,(int,float)): return bool(v)
    return str(v).strip().lower() in ('true','1','yes','t')

def pick(row,*names):
    for n in names:
        if n in row: return row[n]
    return None

def feature(row):
    e1=str(pick(row,'equation1','eq1','lhs','source') or '')
    e2=str(pick(row,'equation2','eq2','rhs','target') or '')
    a=norm_answer(pick(row,'answer','label','implication','is_true'))
    ids=(pick(row,'eq1_id','source_id','lhs_id'),pick(row,'eq2_id','target_id','rhs_id'))
    return {'answer':a,'eq1_id':ids[0],'eq2_id':ids[1],'len1':len(e1),'len2':len(e2),'vars1':len(set(re.findall(r'\b[x-z]\b',e1))),'vars2':len(set(re.findall(r'\b[x-z]\b',e2))),'equation1':e1,'equation2':e2}

def summarize(rows):
    fs=[feature(r) for r in rows]
    return {'n':len(fs),'true':sum(x['answer'] for x in fs),'false':sum(not x['answer'] for x in fs),'true_rate':sum(x['answer'] for x in fs)/len(fs) if fs else None,
            'mean_len1':sum(x['len1'] for x in fs)/len(fs) if fs else None,'mean_len2':sum(x['len2'] for x in fs)/len(fs) if fs else None,
            'unique_sources':len(set(str(x['eq1_id']) for x in fs if x['eq1_id'] is not None)),
            'top_sources':Counter(str(x['eq1_id']) for x in fs if x['eq1_id'] is not None).most_common(10)}

def candidate_path():
    text=SOLVER.read_text()
    if text.count(INSERT_AFTER)!=1: raise RuntimeError('compact insertion point changed')
    p=ROOT/'experiments/mathgraph/_solver_stage1dist_candidate.py'
    p.write_text(text.replace(INSERT_AFTER,INSERT_AFTER+RETRY,1))
    return p

def load_solver(path):
    spec=importlib.util.spec_from_file_location('mg_stage1dist_candidate',path); m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

def local_rows():
    out=[]
    for s in LOCAL:
        p=ROOT/f'examples/problems/{s}.jsonl'
        for line in p.read_text().splitlines():
            if line.strip(): out.append(dict(json.loads(line),_split=s))
    return out

def pair_key(r): return (str(r.get('equation1','')).replace(' ',''),str(r.get('equation2','')).replace(' ',''))
def stable(r): return hashlib.sha256((r.get('id','')+'|'+r.get('_split','')).encode()).hexdigest()

def build_sample(hf_rows,local):
    public_pairs={pair_key(r) for rows in hf_rows.values() for r in rows}
    clean=[r for r in local if pair_key(r) not in public_pairs]
    category_map={'evaluation_normal':'normal','evaluation_hard':'hard1','evaluation_extra_hard':'hard3','evaluation_order5':'hard2'}
    chosen=[]
    for cat,rows in hf_rows.items():
        if cat not in category_map: continue
        target_rate=summarize(rows)['true_rate'] or .5
        pool=[r for r in clean if r['_split']==category_map[cat]]
        nt=round(N_PER_CATEGORY*target_rate); nf=N_PER_CATEGORY-nt
        for ans,n in ((True,nt),(False,nf)):
            xs=sorted([r for r in pool if bool(r.get('answer')) is ans],key=stable)[:n]
            chosen += [dict(r,_category=cat) for r in xs]
    return chosen

def run_case(mod,row):
    cap=[]
    def judge(v,c): cap.append((v,len(c.encode()) if isinstance(c,str) else None)); return {'status':'accepted'}
    oldj,olds=mod.judge,sys.stdin; err=None; start=time.monotonic(); stderr=io.StringIO()
    startup={'problem':{'id':row['id'],'equation1':row['equation1'],'equation2':row['equation2']},'budget':{'timeout_seconds':TIMEOUT,'max_code_length':100000,'max_false_cert_bytes':20000}}
    try:
        mod.judge=judge; sys.stdin=io.StringIO(json.dumps(startup)+'\n')
        with contextlib.redirect_stdout(io.StringIO()),contextlib.redirect_stderr(stderr): mod.run_solo()
    except Exception as e: err=f'{type(e).__name__}: {e}'
    finally: mod.judge,sys.stdin=oldj,olds
    route=None
    for line in stderr.getvalue().splitlines():
        if line.startswith('MATHGRAPH_METRICS '):
            try:
                x=json.loads(line.split(' ',1)[1])
                if x.get('found') is True: route=x.get('portfolio') or x.get('route') or route
            except: pass
    v=cap[0][0] if cap else None; exp='true' if row['answer'] else 'false'
    return {'id':row['id'],'category':row['_category'],'split':row['_split'],'expected':exp,'verdict':v,'correct':v==exp,'answered':v in ('true','false'),'wrong':v is not None and v!=exp,'seconds':time.monotonic()-start,'route':route,'error':err}

def main():
    splits=discover_hf_splits(); hf={s:fetch_split(s) for s in splits}
    print('STAGE1_SPLITS',json.dumps({s:len(v) for s,v in hf.items()},sort_keys=True),flush=True)
    dist={s:summarize(v) for s,v in hf.items()}; print('STAGE1_DIST',json.dumps(dist,sort_keys=True),flush=True)
    sample=build_sample(hf,local_rows()); print('PSEUDO_PRIVATE_N',len(sample),flush=True)
    cp=candidate_path(); mod=load_solver(cp); results=[]
    for r in sample:
        z=run_case(mod,r); results.append(z); print('STAGE1_MATCHED_CASE '+json.dumps(z,sort_keys=True),flush=True)
    bycat={}
    for c in sorted(set(r['category'] for r in results)):
        xs=[r for r in results if r['category']==c]; bycat[c]={'n':len(xs),'answered':sum(r['answered'] for r in xs),'correct':sum(r['correct'] for r in xs),'wrong':sum(r['wrong'] for r in xs),'coverage':sum(r['answered'] for r in xs)/len(xs) if xs else None}
    summary={'schema':'mathgraph.stage1-distribution-etp-gate.v1','official_constraints':{'python':'3.11-slim','cpu_vcpu':2,'memory_mb':2048,'tmp_mb':64,'solver_bytes_max':500000,'judge_code_bytes_max':100000,'false_code_bytes_max':20000,'lean':'4.32.2','mathlib':'4.32.2'},'stage1_distribution':dist,'pseudo_private':{'n':len(results),'answered':sum(r['answered'] for r in results),'correct':sum(r['correct'] for r in results),'wrong':sum(r['wrong'] for r in results),'by_category':bycat,'failures':[r for r in results if not r['correct']]}}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n'); print('STAGE1_ETP_SUMMARY '+json.dumps(summary,sort_keys=True),flush=True)
    cp.unlink(missing_ok=True)
    if summary['pseudo_private']['wrong'] or any(r['error'] for r in results): raise SystemExit('wrong answer or execution error')
if __name__=='__main__': main()

# trigger: stage1-distribution-etp-gate-v1

import contextlib, importlib.util, io, json, subprocess, sys, tempfile, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
COMMIT='211414fdcc48f7f76f1d4043ae9d3d7e0aa376f8'
SOLVER='submissions/mathgraph/solver.py'
RESIDUAL_IDS={'hard2_0021','hard1_0005','hard1_0017','hard2_0107','hard3_0199','hard2_0165','hard1_0067','hard3_0208','hard3_0197'}
TIMEOUT=3600.0
OUT=ROOT/'experiments/mathgraph/results/residual-796-official-budget.json'

def get_solver():
    return subprocess.check_output(['git','show',f'{COMMIT}:{SOLVER}'],cwd=ROOT,text=True)

def load(path):
    spec=importlib.util.spec_from_file_location('mg796official',path)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

def rows():
    out=[]
    for split in ('hard1','hard2','hard3'):
        p=ROOT/f'examples/problems/{split}.jsonl'
        for line in p.read_text().splitlines():
            if not line.strip(): continue
            r=json.loads(line)
            if r.get('id') in RESIDUAL_IDS:
                r['_split']=split; out.append(r)
    found={r['id'] for r in out}
    if found != RESIDUAL_IDS: raise RuntimeError(f'missing residual ids: {sorted(RESIDUAL_IDS-found)}')
    return sorted(out,key=lambda r:r['id'])

def run_case(mod,row):
    calls=[]; stderr=io.StringIO(); stdout=io.StringIO(); oldj,olds=mod.judge,sys.stdin
    def judge(v,c): calls.append((v,len(c.encode()) if isinstance(c,str) else None)); return {'status':'accepted'}
    startup={'problem':{'id':row['id'],'equation1':row['equation1'],'equation2':row['equation2']},'budget':{'timeout_seconds':TIMEOUT,'max_code_length':100000,'max_false_cert_bytes':20000}}
    st=time.monotonic(); err=None
    try:
        mod.judge=judge; sys.stdin=io.StringIO(json.dumps(startup)+'\n')
        with contextlib.redirect_stdout(stdout),contextlib.redirect_stderr(stderr): mod.run_solo()
    except Exception as e: err=f'{type(e).__name__}: {e}'
    finally: mod.judge,sys.stdin=oldj,olds
    exp='true' if row['answer'] else 'false'; verdict=calls[0][0] if calls else None; route=None; metrics=[]
    for line in stderr.getvalue().splitlines():
        if line.startswith('MATHGRAPH_METRICS '):
            try:
                x=json.loads(line.split(' ',1)[1]); metrics.append(x)
                if x.get('found') is True: route=x.get('portfolio') or x.get('route') or x.get('name') or route
            except Exception: pass
    return {'id':row['id'],'split':row['_split'],'expected':exp,'verdict':verdict,'correct':verdict==exp,'answered':verdict in ('true','false'),'wrong':verdict is not None and verdict!=exp,'route':route,'code_bytes':calls[0][1] if calls else None,'seconds':time.monotonic()-st,'error':err,'metrics':metrics}

def main():
    with tempfile.TemporaryDirectory() as td:
        p=Path(td)/'solver796.py'; text=get_solver(); p.write_text(text); mod=load(p)
        print('SOLVER_BYTES',len(text.encode()),flush=True)
        results=[]
        for r in rows():
            z=run_case(mod,r); results.append(z); print('RESIDUAL_CASE',json.dumps(z,sort_keys=True),flush=True)
    payload={'schema':'mathgraph.residual-796-official-budget.v1','solver_commit':COMMIT,'timeout_seconds':TIMEOUT,'results':results,'summary':{'correct':sum(x['correct'] for x in results),'answered':sum(x['answered'] for x in results),'wrong':sum(x['wrong'] for x in results),'remaining':[x['id'] for x in results if not x['correct']]}}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    print('RESIDUAL_SUMMARY',json.dumps(payload['summary'],sort_keys=True),flush=True)
    if any(x['wrong'] or x['error'] for x in results): raise SystemExit('FAIL wrong/error')
if __name__=='__main__': main()

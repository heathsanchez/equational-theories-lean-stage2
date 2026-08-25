import contextlib, hashlib, importlib.util, io, json, re, subprocess, sys, tempfile, time
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'experiments/mathgraph/results/final-lineage-tournament.json'
BASE_794 = '9ea235dc3a55ac01b42033db656f9d82e6083345'
GIVEN_796 = '211414fdcc48f7f76f1d4043ae9d3d7e0aa376f8'
SOLVER_PATH = 'submissions/mathgraph/solver.py'
SPLITS = ('normal','hard1','hard2','hard3')
PER_CLASS = 12
TIMEOUT = 2.0

INSERT_AFTER = '''    if compact_recipe is not None and finish_compact_superposition_candidate(\n        source, target, compact_search, compact_recipe\n    ):\n        return\n'''
RETRY = '''\n    # Fresh-state compact retry; independently replayed before judging.\n    retry_seconds = min(0.15, max(0.05, timeout / 10.0))\n    try:\n        retry_search = CompactSuperposition(\n            sys.modules[__name__], source, target,\n            time.monotonic() + retry_seconds, compact_limits,\n        )\n        retry_recipe = retry_search.solve()\n    except (KeyError, IndexError, MemoryError, RecursionError, TypeError, ValueError):\n        retry_recipe = None\n    if retry_recipe is not None and finish_compact_superposition_candidate(\n        source, target, retry_search, retry_recipe\n    ):\n        return\n'''

FAST_BLOCK = '''COMPACT_SUPERPOSITION_FAST = {
    "seconds": 5.0,
    "maximum_term_size": 90,
    "maximum_replay_term_size": 420,
    "maximum_depth": 20,
    "maximum_rules": 900,
    "maximum_rounds": 96,
    "new_clauses_per_round": 900,
    "maximum_clauses": 60000,
    "normalization_steps": 384,
    "maximum_proof_nodes": 180000,
}'''

def git_show(commit):
    return subprocess.check_output(['git','show',f'{commit}:{SOLVER_PATH}'], cwd=ROOT, text=True)

def add_retry(text):
    if RETRY.strip() in text:
        return text
    if text.count(INSERT_AFTER) != 1:
        raise RuntimeError('compact retry insertion point not unique')
    return text.replace(INSERT_AFTER, INSERT_AFTER + RETRY, 1)

def strengthen_budgets(text):
    # Reproduce the bounded deterministic changes seen in solver 4.py.
    pat = r'COMPACT_SUPERPOSITION_FAST\s*=\s*\{.*?\n\}'
    text2, n = re.subn(pat, FAST_BLOCK, text, count=1, flags=re.S)
    if n != 1:
        raise RuntimeError('COMPACT_SUPERPOSITION_FAST block not found')
    # Raise only the local Fin-5 opportunity budget and add a second deterministic seed.
    text2, nsec = re.subn(r'local_seconds\s*=\s*min\([^\n]+\)', 'local_seconds = min(30.0, max(0.1, timeout / 30.0))', text2, count=1)
    if nsec != 1:
        raise RuntimeError('Fin5 local_seconds not found')
    old = 'for seed_index, seed_salt in enumerate((0,)):'
    new = 'for seed_index, seed_salt in enumerate((0, 0x94D049BB133111EB)):'
    if old in text2:
        text2 = text2.replace(old, new, 1)
    return text2

def build_arms(tmp):
    a = git_show(BASE_794)
    b = git_show(GIVEN_796)
    arms = {
        'A_794_exact': a,
        'B_796_given_clause': b,
        'C_794_plus_retry': add_retry(a),
        'D_796_plus_retry': add_retry(b),
        'E_796_retry_stronger_budgets': strengthen_budgets(add_retry(b)),
    }
    paths = {}
    for name,text in arms.items():
        p = tmp / f'{name}.py'; p.write_text(text, encoding='utf-8'); paths[name]=p
        print('ARM_BUILD', name, len(text.encode()), hashlib.sha256(text.encode()).hexdigest(), flush=True)
    return paths

def stable(row):
    return hashlib.sha256((row['id']+'|'+row['_split']).encode()).hexdigest()

def sample_rows():
    out=[]
    for split in SPLITS:
        rows=[json.loads(x) for x in (ROOT/f'examples/problems/{split}.jsonl').read_text().splitlines() if x.strip()]
        for ans in (True,False):
            xs=sorted([r for r in rows if bool(r.get('answer')) is ans], key=lambda r: hashlib.sha256(r['id'].encode()).hexdigest())[:PER_CLASS]
            out += [dict(r,_split=split) for r in xs]
    out=sorted(out,key=stable)
    if len(out)!=96: raise RuntimeError(f'expected 96 cases, got {len(out)}')
    return out

def load_solver(path,name):
    spec=importlib.util.spec_from_file_location('mg_'+name,path)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

def run_case(mod,row):
    captured=[]
    def fake_judge(v,c):
        captured.append((v,len(c.encode()) if isinstance(c,str) else None)); return {'status':'accepted'}
    oldj,olds=mod.judge,sys.stdin; err=None; stderr=io.StringIO(); st=time.monotonic()
    startup={'problem':{'id':row['id'],'equation1':row['equation1'],'equation2':row['equation2']},'budget':{'timeout_seconds':TIMEOUT,'max_code_length':100000,'max_false_cert_bytes':20000}}
    try:
        mod.judge=fake_judge; sys.stdin=io.StringIO(json.dumps(startup)+'\n')
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(stderr): mod.run_solo()
    except Exception as e: err=f'{type(e).__name__}: {e}'
    finally: mod.judge,sys.stdin=oldj,olds
    v=captured[0][0] if captured else None; exp='true' if row['answer'] else 'false'; route=None
    for line in stderr.getvalue().splitlines():
        if line.startswith('MATHGRAPH_METRICS '):
            try:
                x=json.loads(line.split(' ',1)[1]);
                if x.get('found') is True: route=x.get('portfolio') or x.get('route') or x.get('name') or route
            except Exception: pass
    return {'id':row['id'],'split':row['_split'],'expected':exp,'verdict':v,'answered':v in ('true','false'),'correct':v==exp,'wrong':v is not None and v!=exp,'seconds':time.monotonic()-st,'code_bytes':captured[0][1] if captured else None,'route':route,'error':err}

def main():
    rows=sample_rows(); all_results={}
    with tempfile.TemporaryDirectory() as td:
        paths=build_arms(Path(td))
        for name,path in paths.items():
            mod=load_solver(path,name); rs=[]
            for row in rows:
                z=run_case(mod,row); rs.append(z)
                print('TOURNAMENT_CASE',json.dumps({'arm':name,**z},sort_keys=True),flush=True)
            all_results[name]=rs
    summary={}
    for name,rs in all_results.items():
        by={}
        for s in SPLITS:
            xs=[r for r in rs if r['split']==s]; by[s]={'correct':sum(r['correct'] for r in xs),'answered':sum(r['answered'] for r in xs),'wrong':sum(r['wrong'] for r in xs)}
        summary[name]={'correct':sum(r['correct'] for r in rs),'answered':sum(r['answered'] for r in rs),'wrong':sum(r['wrong'] for r in rs),'seconds':sum(r['seconds'] for r in rs),'max_code_bytes':max((r['code_bytes'] or 0) for r in rs),'by_split':by,'misses':[r['id'] for r in rs if not r['correct']],'errors':[r for r in rs if r['error']]}
    ranking=sorted(summary,key=lambda n:(-summary[n]['correct'],summary[n]['wrong'],summary[n]['seconds']))
    payload={'schema':'mathgraph.final-lineage-tournament.v1','sample_n':len(rows),'timeout_per_case':TIMEOUT,'arms':summary,'ranking':ranking,'winner':ranking[0]}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(payload,indent=2,sort_keys=True)+'\n')
    print('TOURNAMENT_SUMMARY '+json.dumps(payload,sort_keys=True),flush=True)
    if any(v['wrong'] or v['errors'] for v in summary.values()): raise SystemExit('FAIL: wrong answer or arm error')

if __name__=='__main__': main()

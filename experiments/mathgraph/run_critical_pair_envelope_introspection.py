import importlib.util, inspect, json, subprocess, sys, tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
COMMIT='211414fdcc48f7f76f1d4043ae9d3d7e0aa376f8'
SOLVER='submissions/mathgraph/solver.py'
CASE='hard2_0107'

def load_solver():
    text=subprocess.check_output(['git','show',f'{COMMIT}:{SOLVER}'],cwd=ROOT,text=True)
    td=tempfile.TemporaryDirectory(); p=Path(td.name)/'solver796.py'; p.write_text(text)
    spec=importlib.util.spec_from_file_location('mg796cp',p); m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m)
    return td,m

def row():
    for split in ('hard1','hard2','hard3'):
        for line in (ROOT/f'examples/problems/{split}.jsonl').read_text().splitlines():
            if not line.strip(): continue
            r=json.loads(line)
            if r.get('id')==CASE: return r
    raise SystemExit('case not found')

def main():
    td,m=load_solver()
    try:
        r=row(); source=m.parse_equation(r['equation1']); target=m.parse_equation(r['equation2'])
        limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':5.0,'maximum_clauses':12000,'maximum_rules':1024,'maximum_depth':12})
        eng=m.TargetGroundedRefutation(source,target,__import__('time').monotonic()+5.0,limits)
        s=eng.search
        print('SEARCH_TYPE',type(s).__name__)
        print('CLAUSE_COUNT',len(s.clauses))
        for i,c in enumerate(s.clauses[:12]):
            data={}
            if hasattr(c,'__dict__'): data.update(c.__dict__)
            for name in ('lhs','rhs','positive','negative','kind','parents','cost','literal','literals'):
                if hasattr(c,name):
                    try: data[name]=getattr(c,name)
                    except Exception as e: data[name]=f'<ERR {e}>'
            print('CLAUSE',i,type(c).__name__,repr(data)[:5000])
        for obj,name in ((m.CompactSuperposition,'CompactSuperposition'),(type(s),'Search'),):
            for meth in ('critical_pair','search','infer','generate','add_clause'):
                if hasattr(obj,meth):
                    try:
                        print(f'SOURCE_{name}_{meth}_BEGIN')
                        print(inspect.getsource(getattr(obj,meth)))
                        print(f'SOURCE_{name}_{meth}_END')
                    except Exception as e:
                        print('SOURCE_FAIL',name,meth,repr(e))
        print('GIVEN_BEGIN')
        print(inspect.getsource(m._mg_given_clause_recipe))
        print('GIVEN_END')
    finally:
        td.cleanup()

if __name__=='__main__': main()

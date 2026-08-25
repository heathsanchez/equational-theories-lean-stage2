import importlib.util, inspect, subprocess, sys, tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
COMMIT='211414fdcc48f7f76f1d4043ae9d3d7e0aa376f8'
SOLVER='submissions/mathgraph/solver.py'
KEYS=('given','paramod','stair','superposition','model','fin5','selector','strategy','grounded')

def main():
    text=subprocess.check_output(['git','show',f'{COMMIT}:{SOLVER}'],cwd=ROOT,text=True)
    with tempfile.TemporaryDirectory() as td:
        p=Path(td)/'solver796.py'; p.write_text(text)
        spec=importlib.util.spec_from_file_location('mg796inspect',p)
        m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m)
        for name in sorted(dir(m)):
            low=name.lower()
            if any(k in low for k in KEYS):
                obj=getattr(m,name)
                kind=type(obj).__name__
                sig=''
                if callable(obj):
                    try: sig=str(inspect.signature(obj))
                    except Exception: pass
                print('SURFACE',name,kind,sig)
                if callable(obj) and any(k in low for k in ('given','paramod','stair')):
                    try:
                        src=inspect.getsource(obj)
                        print('SOURCE_BEGIN',name)
                        print(src[:12000])
                        print('SOURCE_END',name)
                    except Exception as e: print('SOURCE_ERR',name,e)
if __name__=='__main__': main()


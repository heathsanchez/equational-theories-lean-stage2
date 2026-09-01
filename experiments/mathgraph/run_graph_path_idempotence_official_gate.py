#!/usr/bin/env python3
import argparse, json, os, pathlib, re, subprocess, sys


def compact_certificate(code):
    out=[]
    for line in code.splitlines():
        m=re.match(r'^(\s*have\s+p\d+)\s+:\s+.*\s+:=\s+(.*)$',line)
        if m:
            out.append(m.group(1)+' := '+m.group(2))
        else:
            out.append(line)
    return '\n'.join(out)+'\n'


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--solver', required=True)
    ap.add_argument('--row', required=True)
    args=ap.parse_args()
    root=pathlib.Path(__file__).resolve().parents[2]
    probe=root/'experiments/mathgraph/source_only_graph_path_compiler_probe.py'
    p=subprocess.run([sys.executable,str(probe),'--solver',args.solver,'--row',args.row],text=True,capture_output=True)
    sys.stdout.write(p.stdout); sys.stderr.write(p.stderr)
    if p.returncode != 0:
        raise SystemExit(p.returncode)
    start='CERTIFICATE_BEGIN\n'; end='\nCERTIFICATE_END'
    if start not in p.stdout or end not in p.stdout:
        raise RuntimeError('compiler did not emit certificate markers')
    raw=p.stdout.split(start,1)[1].split(end,1)[0]+'\n'
    code=compact_certificate(raw)
    print('GRAPH_CERTIFICATE_COMPRESSION '+json.dumps({'raw_bytes':len(raw.encode()),'compact_bytes':len(code.encode()),'under_50000':len(code.encode())<=50000},sort_keys=True),flush=True)
    row=json.load(open(args.row))
    problem={
        'id':'mathgraph_graph_path_idempotence_0036',
        'eq1_id':int(row.get('eq1_id',0) or 0),
        'eq2_id':0,
        'equation1':row['equation1'],
        'equation2':'x = x * x',
    }
    answer=json.dumps({'verdict':'true','code':code})
    sys.path.insert(0,str(root))
    from judge.verify import verify_answer, JudgeConfig
    lean=pathlib.Path(os.environ['LEAN_BIN'])
    lake=pathlib.Path(os.environ['LAKE_BIN'])
    result=verify_answer(problem,answer,config=JudgeConfig(lake_bin=lake,lean_bin=lean))
    summary={k:v for k,v in result.items() if k not in ('stdout','stderr','code')}
    print('OFFICIAL_GRAPH_PATH_IDEMPOTENCE '+json.dumps(summary,sort_keys=True,default=str),flush=True)
    if result.get('stdout'): print('LEAN_STDOUT\n'+str(result['stdout']),flush=True)
    if result.get('stderr'): print('LEAN_STDERR\n'+str(result['stderr']),flush=True)
    out=root/'experiments/mathgraph/results/graph-path-idempotence-official-gate.json'
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps({'problem':problem,'result':result,'raw_certificate_bytes':len(raw.encode()),'certificate_bytes':len(code.encode())},sort_keys=True,default=str,indent=2))
    if result.get('status')!='accepted': raise SystemExit(2)

if __name__=='__main__': main()

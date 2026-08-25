#!/usr/bin/env python3
import importlib.util, json, subprocess, sys, tempfile, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
COMMIT='211414fdcc48f7f76f1d4043ae9d3d7e0aa376f8'
SOLVER='submissions/mathgraph/solver.py'
IDS={'hard1_0067','hard2_0107','hard3_0208'}


def load_solver():
    text=subprocess.check_output(['git','show',f'{COMMIT}:{SOLVER}'],cwd=ROOT,text=True)
    td=tempfile.TemporaryDirectory(); p=Path(td.name)/'solver796.py'; p.write_text(text)
    spec=importlib.util.spec_from_file_location('mg796orient',p)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m)
    return td,m


def rows():
    out=[]
    for split in ('hard1','hard2','hard3'):
        for line in (ROOT/f'examples/problems/{split}.jsonl').read_text().splitlines():
            if not line.strip(): continue
            r=json.loads(line)
            if r.get('id') in IDS: out.append(r)
    return sorted(out,key=lambda r:r['id'])


def swap(eq):
    return (eq[1],eq[0],eq[2])


def trial(m,r,name,source,target,seconds=15.0,max_given=1536):
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({
        'seconds':seconds,
        'maximum_term_size':90,
        'maximum_replay_term_size':320,
        'maximum_depth':18,
        'maximum_rules':1024,
        'maximum_rounds':96,
        'new_clauses_per_round':768,
        'maximum_clauses':24000,
        'normalization_steps':384,
        'maximum_proof_nodes':60000,
    })
    started=time.monotonic(); recipe=None; err=None; proof_nodes=None; code_bytes=None
    try:
        eng=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,limits)
        recipe=m._mg_given_clause_recipe(eng.search,maximum_given=max_given,focus_per_age=4)
        if recipe is not None:
            rr=eng.inline_recipe(recipe)
            comp=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+4.0,eng.search.limits)
            nodes,root=comp.compile(rr)
            if root is not None and (nodes[root].lhs,nodes[root].rhs)==target[:2] and m.replay_dag(source,nodes,root,maximum_term_size=limits['maximum_replay_term_size'],maximum_nodes=limits['maximum_proof_nodes']):
                code,proof_nodes=m.make_dag_certificate(target,nodes,root)
                code=m._mg_elide_have_types(code)
                code_bytes=len(code.encode())
    except Exception as e:
        err=f'{type(e).__name__}:{e}'
    return {
        'id':r['id'],'trial':name,'recipe_found':recipe is not None,
        'proof_replayed':proof_nodes is not None,'proof_nodes':proof_nodes,
        'code_bytes':code_bytes,'elapsed':time.monotonic()-started,'error':err,
    }


def main():
    td,m=load_solver(); results=[]
    try:
        for r in rows():
            src=m.parse_equation(r['equation1']); tgt=m.parse_equation(r['equation2'])
            variants=[
                ('base',src,tgt),
                ('source-swapped',swap(src),tgt),
                ('target-swapped',src,swap(tgt)),
                ('both-swapped',swap(src),swap(tgt)),
            ]
            for name,s,t in variants:
                rec=trial(m,r,name,s,t)
                results.append(rec)
                print('ORIENT',json.dumps(rec,sort_keys=True),flush=True)
        summary={
            'recipe_gains':sorted({x['id'] for x in results if x['trial']!='base' and x['recipe_found']}),
            'replayed_gains':sorted({x['id'] for x in results if x['trial']!='base' and x['proof_replayed']}),
        }
        print('ORIENT_SUMMARY',json.dumps(summary,sort_keys=True),flush=True)
    finally:
        td.cleanup()
    out=ROOT/'experiments/mathgraph/results/residual3-orientation-completion.json'
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps({'summary':summary,'results':results},indent=2,sort_keys=True)+'\n')

if __name__=='__main__': main()

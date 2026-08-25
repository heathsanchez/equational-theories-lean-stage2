#!/usr/bin/env python3
import importlib.util, json, subprocess, sys, tempfile, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
COMMIT='211414fdcc48f7f76f1d4043ae9d3d7e0aa376f8'
SOLVER='submissions/mathgraph/solver.py'
RATIOS=(5,6,7,8,10)
RESIDUAL_IDS=('hard1_0067','hard2_0107','hard3_0208')
PROTECTED_IDS=('hard1_0023','hard1_0027','hard1_0035','hard1_0040','hard1_0041','hard1_0046','hard1_0050','hard1_0052','hard1_0059')

def load_solver():
    text=subprocess.check_output(['git','show',f'{COMMIT}:{SOLVER}'],cwd=ROOT,text=True)
    td=tempfile.TemporaryDirectory(); p=Path(td.name)/'solver796.py'; p.write_text(text)
    spec=importlib.util.spec_from_file_location('mg796proofsweep',p)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m)
    return td,m

def rows():
    want=set(RESIDUAL_IDS)|set(PROTECTED_IDS); out={}
    for split in ('hard1','hard2','hard3'):
        p=ROOT/f'examples/problems/{split}.jsonl'
        for line in p.read_text().splitlines():
            if not line.strip(): continue
            r=json.loads(line)
            if r.get('id') in want: out[r['id']]=r
    return out

def one(m,r,ratio,seconds):
    source=m.parse_equation(r['equation1']); target=m.parse_equation(r['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({'seconds':seconds,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':512,'maximum_clauses':16000,'normalization_steps':384,'maximum_proof_nodes':60000})
    started=time.monotonic()
    eng=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,limits)
    recipe=m._mg_given_clause_recipe(eng.search,maximum_given=1024,focus_per_age=ratio)
    found=recipe is not None
    inline_ok=False; compile_ok=False; replay_ok=False; nodes_n=None
    err=None
    if found:
        try:
            rr=eng.inline_recipe(recipe); inline_ok=rr is not None
            compiler=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+4.0,eng.search.limits)
            compiled=compiler.compile(rr)
            if compiled is not None:
                nodes,root=compiled; nodes_n=len(nodes); compile_ok=True
                replay_ok=bool(m.replay_dag(source,nodes,root))
        except Exception as e:
            err=type(e).__name__+': '+str(e)
    return {'ratio':ratio,'recipe_found':found,'inline_ok':inline_ok,'compile_ok':compile_ok,'replay_ok':replay_ok,'proof_nodes':nodes_n,'seconds':round(time.monotonic()-started,4),'error':err}

def main():
    td,m=load_solver(); byid=rows(); out={'ratios':RATIOS,'residuals':[],'protected':[]}
    try:
        for rid in RESIDUAL_IDS:
            rec={'id':rid,'runs':{}}
            for ratio in RATIOS:
                rec['runs'][str(ratio)]=one(m,byid[rid],ratio,20.0)
            out['residuals'].append(rec); print('PROOF_SWEEP_RESIDUAL',json.dumps(rec,sort_keys=True),flush=True)
        for rid in PROTECTED_IDS:
            rec={'id':rid,'runs':{}}
            for ratio in RATIOS:
                rec['runs'][str(ratio)]=one(m,byid[rid],ratio,6.0)
            out['protected'].append(rec); print('PROOF_SWEEP_PROTECTED',json.dumps(rec,sort_keys=True),flush=True)
        summary={}
        for ratio in RATIOS:
            k=str(ratio)
            summary[k]={
                'residual_replay':sum(int(x['runs'][k]['replay_ok']) for x in out['residuals']),
                'residual_recipe':sum(int(x['runs'][k]['recipe_found']) for x in out['residuals']),
                'protected_replay':sum(int(x['runs'][k]['replay_ok']) for x in out['protected']),
                'protected_recipe':sum(int(x['runs'][k]['recipe_found']) for x in out['protected']),
                'protected_cases':len(out['protected']),
            }
        out['summary']=summary; print('PROOF_SWEEP_SUMMARY',json.dumps(summary,sort_keys=True),flush=True)
    finally: td.cleanup()
    p=ROOT/'experiments/mathgraph/results/residual3-fairness-proof-sweep.json'; p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')

if __name__=='__main__': main()

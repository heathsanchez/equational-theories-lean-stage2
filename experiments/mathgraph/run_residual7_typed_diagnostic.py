import importlib.util, json, subprocess, sys, tempfile, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
COMMIT='211414fdcc48f7f76f1d4043ae9d3d7e0aa376f8'
SOLVER='submissions/mathgraph/solver.py'
TRUE_IDS={'hard1_0067','hard2_0021','hard2_0107','hard3_0208'}
FALSE_IDS={'hard1_0005','hard1_0017','hard2_0165'}

def load_solver():
    text=subprocess.check_output(['git','show',f'{COMMIT}:{SOLVER}'],cwd=ROOT,text=True)
    td=tempfile.TemporaryDirectory(); p=Path(td.name)/'solver796.py'; p.write_text(text)
    spec=importlib.util.spec_from_file_location('mg796r7',p); m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m)
    return td,m

def rows(ids):
    out=[]
    for split in ('hard1','hard2','hard3'):
        for line in (ROOT/f'examples/problems/{split}.jsonl').read_text().splitlines():
            if not line.strip(): continue
            r=json.loads(line)
            if r.get('id') in ids: r['_split']=split; out.append(r)
    return sorted(out,key=lambda x:x['id'])

def parsed(m,r): return m.parse_equation(r['equation1']),m.parse_equation(r['equation2'])

def gc_trial(m,r,name,focus,max_given,seconds,term=65,depth=12,clauses=12000,newc=512):
    source,target=parsed(m,r); limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({'seconds':seconds,'maximum_term_size':term,'maximum_replay_term_size':300,'maximum_depth':depth,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':newc,'maximum_clauses':clauses,'normalization_steps':384,'maximum_proof_nodes':60000})
    st=time.monotonic(); found=False; proof_nodes=None; code_bytes=None; error=None
    try:
        eng=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,limits)
        recipe=m._mg_given_clause_recipe(eng.search,maximum_given=max_given,focus_per_age=focus)
        if recipe is not None:
            rr=eng.inline_recipe(recipe)
            comp=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+4.0,eng.search.limits)
            nodes,root=comp.compile(rr)
            if (nodes[root].lhs,nodes[root].rhs)==target[:2] and m.replay_dag(source,nodes,root,maximum_term_size=limits['maximum_replay_term_size'],maximum_nodes=limits['maximum_proof_nodes']):
                code,proof_nodes=m.make_dag_certificate(target,nodes,root); code=m._mg_elide_have_types(code); code_bytes=len(code.encode()); found=code_bytes<=100000
    except Exception as e: error=f'{type(e).__name__}:{e}'
    return {'kind':'true-gc','id':r['id'],'trial':name,'focus_per_age':focus,'max_given':max_given,'found':found,'proof_nodes':proof_nodes,'code_bytes':code_bytes,'seconds':time.monotonic()-st,'error':error}

def stair_trial(m,r,name,seconds,**kw):
    source,target=parsed(m,r); problem={'id':r['id'],'equation1':r['equation1'],'equation2':r['equation2']}; st=time.monotonic(); found=False; result_meta={}; error=None
    try:
        engine,replay=m._load_stair_specialist(); base=dict(max_clauses=8000,max_weight=36,max_term_size=30,pair_budget=300,timeout=seconds,translate=True,unordered=False,neg_bias=0,old_rules_first=False,tautology_prune=False,forward_subsumption=False); base.update(kw)
        args=engine['argparse'].Namespace(**base)
        res=engine['pm_solve_with_pruning_portfolio'](problem,args,deadline=time.time()+seconds)
        found=bool(res.get('status')=='proved' and res.get('plan_ok') and replay['replay_plan'](res['spec']))
        result_meta={'status':res.get('status'),'strategy':res.get('strategy'),'steps':res.get('total_steps'),'lemmas':res.get('n_lemmas'),'code_bytes':len(res.get('code','').encode()) if res.get('code') else None}
    except Exception as e: error=f'{type(e).__name__}:{e}'
    return {'kind':'true-stair','id':r['id'],'trial':name,'found':found,'seconds':time.monotonic()-st,'meta':result_meta,'error':error}

def false_trial(m,r,order,seconds,canonical_only=False):
    source,target=parsed(m,r); st=time.monotonic(); found=False; cert=None; err=None
    try:
        ans=m.find_finite_countermodel(order,source,target,time.monotonic()+seconds,canonical_only=canonical_only)
        if ans is not None:
            # Return shape is implementation-specific; successful construction is still independently replayed by production finish path.
            found=True; cert=str(type(ans).__name__)
    except Exception as e: err=f'{type(e).__name__}:{e}'
    return {'kind':'false-model','id':r['id'],'order':order,'seconds_budget':seconds,'canonical_only':canonical_only,'found':found,'answer_type':cert,'elapsed':time.monotonic()-st,'error':err}

def main():
    td,m=load_solver(); results=[]
    try:
        for r in rows(TRUE_IDS):
            trials=[('gc-age-heavy',1,1024,20,65,12,16000,512),('gc-balanced',2,1024,20,65,12,16000,512),('gc-current-wide',4,1024,20,65,12,16000,512),('gc-focus-heavy',8,1024,20,65,12,16000,512),('gc-deeper',4,1536,25,90,18,24000,768)]
            solved=False
            for t in trials:
                z=gc_trial(m,r,*t); results.append(z); print('DIAG',json.dumps(z,sort_keys=True),flush=True)
                if z['found']: solved=True; break
            if not solved:
                stair=[('stair-default-8s',dict()),('stair-old-rules',{'old_rules_first':True}),('stair-forward-subsumption',{'forward_subsumption':True}),('stair-neg-bias',{'neg_bias':2}),('stair-wide',{'max_clauses':16000,'max_weight':48,'max_term_size':40,'pair_budget':600})]
                for name,kw in stair:
                    z=stair_trial(m,r,name,8.0,**kw); results.append(z); print('DIAG',json.dumps(z,sort_keys=True),flush=True)
                    if z['found']: break
        for r in rows(FALSE_IDS):
            for order,sec,canon in ((3,5,False),(4,15,False),(5,30,False),(5,30,True)):
                z=false_trial(m,r,order,sec,canon); results.append(z); print('DIAG',json.dumps(z,sort_keys=True),flush=True)
                if z['found']: break
    finally: td.cleanup()
    summary={'true_solved':sorted({z['id'] for z in results if z['kind'].startswith('true-') and z.get('found')}),'false_solved':sorted({z['id'] for z in results if z['kind']=='false-model' and z.get('found')}),'results':len(results)}
    print('DIAG_SUMMARY',json.dumps(summary,sort_keys=True),flush=True)
    (ROOT/'experiments/mathgraph/results').mkdir(parents=True,exist_ok=True); (ROOT/'experiments/mathgraph/results/residual7-typed-diagnostic.json').write_text(json.dumps({'summary':summary,'results':results},indent=2,sort_keys=True)+'\n')
if __name__=='__main__': main()

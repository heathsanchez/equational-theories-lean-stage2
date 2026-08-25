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
    spec=importlib.util.spec_from_file_location('mg796proofsweep2',p)
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


def oriented_variants(m,c):
    if c.lhs==c.rhs:
        return (c,)
    return (c,m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))


def side_complete_recipe(m, search, ratio, maximum_given=1024):
    passive=list(search.clauses)
    active=[]
    age={id(c):i for i,c in enumerate(passive)}
    next_age=len(passive)
    given=0
    age_picks=0
    target_picks=0
    proposals_total=0
    accepted_total=0

    while passive and given < maximum_given and not search.expired():
        rules=[]
        for c in active:
            q=search.orient(c)
            if q is not None:
                rules.append(q)
        goal=search.target_proof(rules)
        if goal is not None:
            return goal, {'given':given,'age_picks':age_picks,'target_picks':target_picks,'proposals':proposals_total,'accepted':accepted_total}

        use_age=(given>0 and given % (ratio+1) == ratio)
        if use_age:
            idx=min(range(len(passive)),key=lambda i:age.get(id(passive[i]),10**18)); age_picks+=1
        else:
            idx=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18))); target_picks+=1
        selected=passive.pop(idx)
        selected=search.interreduce(selected,rules)
        active.append(selected)
        given+=1

        rules=[]
        for c in active:
            q=search.orient(c)
            if q is not None:
                rules.append(q)
        goal=search.target_proof(rules)
        if goal is not None:
            return goal, {'given':given,'age_picks':age_picks,'target_picks':target_picks,'proposals':proposals_total,'accepted':accepted_total}

        proposals=[]
        for oi,other in enumerate(active):
            for bo,bi,a,b in ((selected,other,given,oi),(other,selected,oi,given)):
                for oside,outer in enumerate(oriented_variants(m,bo)):
                    for iside,inner in enumerate(oriented_variants(m,bi)):
                        for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                            if search.expired(): break
                            q=search.critical_pair(outer,inner,a*2+oside,b*2+iside,path)
                            if q is None: continue
                            qr=search.interreduce(q,rules)
                            proposals.append((search.target_score(qr),qr))
        proposals_total += len(proposals)
        proposals.sort(key=lambda x:x[0])
        for _,q in proposals[:search.limits['new_clauses_per_round']]:
            if search.add_clause(q):
                passive.append(q); age[id(q)]=next_age; next_age+=1; accepted_total+=1

        # Preserve the exact validated diagnostic lifecycle: interreduce and
        # deduplicate passive clauses after each round.
        new=[]; seen=set()
        for c in passive:
            if search.expired(): break
            c=search.interreduce(c,rules)
            names={}; a=(m.alpha_canonical_term(c.lhs,names),m.alpha_canonical_term(c.rhs,names))
            names={}; b=(m.alpha_canonical_term(c.rhs,names),m.alpha_canonical_term(c.lhs,names))
            kk=min(a,b)
            if kk in seen: continue
            seen.add(kk); new.append(c)
        passive=new

    rules=[]
    for c in active:
        q=search.orient(c)
        if q is not None:
            rules.append(q)
    goal=search.target_proof(rules)
    return goal, {'given':given,'age_picks':age_picks,'target_picks':target_picks,'proposals':proposals_total,'accepted':accepted_total}


def one(m,r,ratio,seconds):
    source=m.parse_equation(r['equation1']); target=m.parse_equation(r['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({'seconds':seconds,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':512,'maximum_clauses':16000,'normalization_steps':384,'maximum_proof_nodes':60000})
    started=time.monotonic()
    eng=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,limits)
    recipe,stats=side_complete_recipe(m,eng.search,ratio,maximum_given=1024)
    found=recipe is not None
    inline_ok=False; compile_ok=False; replay_ok=False; nodes_n=None; err=None
    if found:
        try:
            rr=eng.inline_recipe(recipe); inline_ok=rr is not None
            if rr is not None:
                compiler=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+4.0,eng.search.limits)
                compiled=compiler.compile(rr)
                if compiled is not None:
                    nodes,root=compiled; nodes_n=len(nodes); compile_ok=True
                    replay_ok=bool(m.replay_dag(source,nodes,root))
        except Exception as e:
            err=type(e).__name__+': '+str(e)
    return {'ratio':ratio,'recipe_found':found,'inline_ok':inline_ok,'compile_ok':compile_ok,'replay_ok':replay_ok,'proof_nodes':nodes_n,'seconds':round(time.monotonic()-started,4),'error':err,**stats}


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
    finally:
        td.cleanup()
    p=ROOT/'experiments/mathgraph/results/residual3-fairness-proof-sweep.json'; p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')

if __name__=='__main__': main()

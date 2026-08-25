import importlib.util, json, subprocess, sys, tempfile, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
COMMIT='211414fdcc48f7f76f1d4043ae9d3d7e0aa376f8'
SOLVER='submissions/mathgraph/solver.py'
IDS={'hard1_0067','hard2_0107','hard3_0208'}

def load_solver():
    text=subprocess.check_output(['git','show',f'{COMMIT}:{SOLVER}'],cwd=ROOT,text=True)
    td=tempfile.TemporaryDirectory(); p=Path(td.name)/'solver796.py'; p.write_text(text)
    spec=importlib.util.spec_from_file_location('mg796side',p); m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m)
    return td,m

def rows():
    out=[]
    for split in ('hard1','hard2','hard3'):
        for line in (ROOT/f'examples/problems/{split}.jsonl').read_text().splitlines():
            if not line.strip(): continue
            r=json.loads(line)
            if r.get('id') in IDS: out.append(r)
    return sorted(out,key=lambda x:x['id'])

def oriented_variants(m,c):
    if c.lhs==c.rhs: return (c,)
    return (c,m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))

def side_complete_recipe(m,search,maximum_given=1024,focus_per_age=4):
    passive=list(search.clauses); active=[]
    age={id(c):i for i,c in enumerate(passive)}; next_age=len(passive); given=0
    side_attempts=0; side_nonnull=0
    while passive and given < maximum_given and not search.expired():
        rules=[]
        for clause in active:
            rule=search.orient(clause)
            if rule is not None: rules.append(rule)
        goal=search.target_proof(rules)
        if goal is not None: return goal,side_attempts,side_nonnull
        if given % (focus_per_age+1) == focus_per_age:
            index=min(range(len(passive)),key=lambda i:age.get(id(passive[i]),10**18))
        else:
            index=min(range(len(passive)),key=lambda i:(search.target_score(passive[i]),age.get(id(passive[i]),10**18)))
        selected=passive.pop(index)
        reduced=search.interreduce(selected,rules)
        if reduced.lhs != selected.lhs or reduced.rhs != selected.rhs:
            search.add_clause(reduced); selected=reduced
        active.append(selected); given+=1
        rules=[]
        for clause in active:
            rule=search.orient(clause)
            if rule is not None: rules.append(rule)
        goal=search.target_proof(rules)
        if goal is not None: return goal,side_attempts,side_nonnull
        proposals=[]
        for other_index,other in enumerate(active):
            for base_outer,base_inner,oi,ii in ((selected,other,given,other_index),(other,selected,other_index,given)):
                for oside,outer in enumerate(oriented_variants(m,base_outer)):
                    for iside,inner in enumerate(oriented_variants(m,base_inner)):
                        for path in m.nonvariable_positions(outer.lhs,maximum_depth=search.limits['maximum_depth'],include_root=True):
                            if search.expired(): break
                            side_attempts+=1
                            q=search.critical_pair(outer,inner,oi*2+oside,ii*2+iside,path)
                            if q is None: continue
                            side_nonnull+=1
                            q=search.interreduce(q,rules)
                            proposals.append((search.target_score(q),q))
        proposals.sort(key=lambda x:x[0])
        for _,q in proposals[:search.limits['new_clauses_per_round']]:
            if search.add_clause(q):
                search.superpositions+=1; passive.append(q); age[id(q)]=next_age; next_age+=1
        new_passive=[]; seen=set()
        for clause in passive:
            if search.expired(): break
            reduced=search.interreduce(clause,rules)
            if reduced.lhs != clause.lhs or reduced.rhs != clause.rhs:
                if search.add_clause(reduced):
                    age[id(reduced)]=age.get(id(clause),next_age); next_age+=1
                clause=reduced
            names={}; a=(m.alpha_canonical_term(clause.lhs,names),m.alpha_canonical_term(clause.rhs,names))
            names={}; b=(m.alpha_canonical_term(clause.rhs,names),m.alpha_canonical_term(clause.lhs,names)); k=min(a,b)
            if k in seen: continue
            seen.add(k); new_passive.append(clause)
        passive=new_passive
    rules=[]
    for clause in active:
        rule=search.orient(clause)
        if rule is not None: rules.append(rule)
    return search.target_proof(rules),side_attempts,side_nonnull

def trial(m,r,side_complete):
    source=m.parse_equation(r['equation1']); target=m.parse_equation(r['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({'seconds':20.0,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':512,'maximum_clauses':16000,'normalization_steps':384,'maximum_proof_nodes':60000})
    st=time.monotonic(); result={'id':r['id'],'mode':'side-complete' if side_complete else 'baseline','found':False,'replayed':False,'proof_nodes':None,'code_bytes':None,'elapsed':None,'side_attempts':0,'side_nonnull':0,'error':None}
    try:
        eng=m.TargetGroundedRefutation(source,target,time.monotonic()+20.0,limits)
        if side_complete:
            recipe,a,b=side_complete_recipe(m,eng.search,1024,4); result['side_attempts']=a; result['side_nonnull']=b
        else:
            recipe=m._mg_given_clause_recipe(eng.search,maximum_given=1024,focus_per_age=4)
        if recipe is not None:
            rr=eng.inline_recipe(recipe)
            comp=m.CompactSuperposition(m,eng.source,eng.target,time.monotonic()+4.0,eng.search.limits)
            nodes,root=comp.compile(rr)
            result['proof_nodes']=len(nodes)
            ok=((nodes[root].lhs,nodes[root].rhs)==target[:2] and m.replay_dag(source,nodes,root,maximum_term_size=limits['maximum_replay_term_size'],maximum_nodes=limits['maximum_proof_nodes']))
            result['replayed']=bool(ok)
            if ok:
                code,n=m.make_dag_certificate(target,nodes,root); code=m._mg_elide_have_types(code); result['code_bytes']=len(code.encode()); result['found']=result['code_bytes']<=100000
    except Exception as e:
        result['error']=f'{type(e).__name__}:{e}'
    result['elapsed']=time.monotonic()-st
    return result

def main():
    td,m=load_solver(); results=[]
    try:
        for r in rows():
            for mode in (False,True):
                z=trial(m,r,mode); results.append(z); print('SIDE',json.dumps(z,sort_keys=True),flush=True)
    finally: td.cleanup()
    gains=[z['id'] for z in results if z['mode']=='side-complete' and z['found']]
    summary={'gains':sorted(gains),'baseline_found':sorted(z['id'] for z in results if z['mode']=='baseline' and z['found']),'side_complete_found':sorted(z['id'] for z in results if z['mode']=='side-complete' and z['found'])}
    print('SIDE_SUMMARY',json.dumps(summary,sort_keys=True),flush=True)
    (ROOT/'experiments/mathgraph/results').mkdir(parents=True,exist_ok=True)
    (ROOT/'experiments/mathgraph/results/residual3-side-complete-superposition.json').write_text(json.dumps({'summary':summary,'results':results},indent=2,sort_keys=True)+'\n')

if __name__=='__main__': main()

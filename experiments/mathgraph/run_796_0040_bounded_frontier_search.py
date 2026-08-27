#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
from dataclasses import replace
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
from judge.verify import _resolve_config, verify_answer
SOLVER=ROOT/'submissions/mathgraph/solver.py'; RID='evaluation_normal_0040'

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path); mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod

def row_for(path):
    with open(path) as f:
        for line in f:
            r=json.loads(line)
            if r.get('id')==RID: return r
    raise RuntimeError('0040 not found')

def compact(m,code):
    if not hasattr(m,'_mg_elide_have_types'): return code
    before=code.splitlines(); after=m._mg_elide_have_types(code).splitlines()
    if len(before)!=len(after): return code
    for i,(a,b) in enumerate(zip(before,after)):
        if b.lstrip().startswith('have ') and b.rstrip().endswith(':= rfl') and ' : ' in a and ' := ' in a: after[i]=a
    return '\n'.join(after)+'\n'

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); ap.add_argument('--seconds',type=float,default=120); ap.add_argument('--batch',type=int,default=128); a=ap.parse_args()
    m=load(SOLVER,'mg_bounded_frontier'); row=row_for(a.input)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':a.seconds,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':128,'new_clauses_per_round':64,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})
    engine=m.TargetGroundedRefutation(source,target,time.monotonic()+a.seconds,limits); search=engine.search
    original_cp=search.critical_pair; expansion_calls=0; expansion_changed=0; flushes=0; enumerated=0
    def expand_term(t):
        if t[0]=='var' and t[1] in engine.reverse_constants: return expand_term(engine.reverse_constants[t[1]])
        if t[0]=='op': return ('op',expand_term(t[1]),expand_term(t[2]))
        return t
    def expand_recipe(r,cache=None):
        cache={} if cache is None else cache
        if id(r) in cache: return cache[id(r)]
        ps=tuple(expand_recipe(p,cache) for p in r.parents); data=r.data
        if r.kind=='source':
            sub,rev=data; data=(tuple((k,expand_term(v)) for k,v in sub),rev)
        elif r.kind=='instantiate': data=tuple((k,expand_term(v)) for k,v in data)
        elif r.kind=='congruence': data=(data[0],expand_term(data[1]))
        q=m.Recipe(expand_term(r.lhs),expand_term(r.rhs),r.kind,ps,data); cache[id(r)]=q; return q
    def cp(outer,inner,oi,ii,path):
        nonlocal expansion_calls, expansion_changed
        expansion_calls+=1; eo=expand_recipe(outer); ei=expand_recipe(inner)
        if (eo.lhs,eo.rhs,ei.lhs,ei.rhs)!=(outer.lhs,outer.rhs,inner.lhs,inner.rhs): expansion_changed+=1
        return original_cp(eo,ei,oi,ii,path)
    search.critical_pair=cp
    def flush(proposals):
        nonlocal flushes
        if not proposals: return 0
        flushes+=1; proposals.sort(key=lambda x:x[0]); added=0
        for _,p in proposals:
            if search.add_clause(p):
                search.superpositions+=1; added+=1
                if added>=limits['new_clauses_per_round']: break
        return added
    def bounded_solve():
        nonlocal enumerated
        for ri in range(limits['maximum_rounds']):
            search.rounds=ri+1; rules=search.rules(); goal=search.target_proof(rules)
            if goal is not None: return goal
            snapshot=rules; proposals=[]; round_added=0; restart=False
            for oi,outer in enumerate(snapshot):
                for ii,inner in enumerate(snapshot):
                    for path in m.nonvariable_positions(outer.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
                        if search.expired():
                            round_added += flush(proposals)
                            return search.target_proof(search.rules())
                        p=search.critical_pair(outer,inner,oi,ii,path)
                        if p is None: continue
                        p=search.interreduce(p,rules); proposals.append((search.target_score(p),p)); enumerated+=1
                        if len(proposals)>=a.batch:
                            round_added += flush(proposals); proposals=[]; restart=True; break
                    if restart: break
                if restart: break
            round_added += flush(proposals)
            goal=search.target_proof(search.rules())
            if goal is not None: return goal
            if not round_added or len(search.clauses)>=limits['maximum_clauses']: break
        return search.target_proof(search.rules())
    start=time.monotonic(); recipe=bounded_solve(); elapsed=time.monotonic()-start
    out={'id':RID,'found_recipe':bool(recipe),'seconds':elapsed,'batch':a.batch,'rounds':search.rounds,'clauses':len(search.clauses),'generated':search.generated,'superpositions':search.superpositions,'reductions':search.reductions,'enumerated':enumerated,'flushes':flushes,'expansion_calls':expansion_calls,'expansion_changed':expansion_changed,'target_hit':False,'replay':False,'proof_nodes':None,'certificate_bytes':None,'judge_status':None,'judge_error_code':None}
    if recipe is not None:
        rr=engine.inline_recipe(recipe)
        if (rr.lhs,rr.rhs)==(target[1],target[0]): rr=m.Recipe(rr.rhs,rr.lhs,'symmetry',(rr,))
        nodes,root=search.compile(rr); out['target_hit']=(nodes[root].lhs,nodes[root].rhs)==target[:2]
        out['replay']=bool(m.replay_dag(source,nodes,root,maximum_term_size=limits['maximum_replay_term_size'],maximum_nodes=limits['maximum_proof_nodes']))
        if out['target_hit'] and out['replay']:
            code,n=m.make_dag_certificate(target,nodes,root); code=compact(m,code); out['proof_nodes']=n; out['certificate_bytes']=len(code.encode())
            if out['certificate_bytes']<=100000:
                cfg=replace(_resolve_config(None),max_code_length=100000); res=verify_answer(row,json.dumps({'verdict':'true','code':code}),config=cfg); out['judge_status']=res.get('status'); out['judge_error_code']=res.get('error_code'); out['judge_message']=res.get('message')
    Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('BOUNDED_FRONTIER_SEARCH',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()

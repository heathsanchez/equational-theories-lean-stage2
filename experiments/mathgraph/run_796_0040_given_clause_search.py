#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
from dataclasses import replace
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0,str(ROOT))
from judge.verify import _resolve_config, verify_answer

SOLVER=ROOT/'submissions/mathgraph/solver.py'
RID='evaluation_normal_0040'

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

def row_for(path):
    with open(path) as f:
        for line in f:
            row=json.loads(line)
            if row.get('id')==RID:
                return row
    raise RuntimeError('0040 not found')

def compact(m,code):
    if not hasattr(m,'_mg_elide_have_types'):
        return code
    before=code.splitlines(); after=m._mg_elide_have_types(code).splitlines()
    if len(before)!=len(after):
        return code
    for i,(a,b) in enumerate(zip(before,after)):
        if b.lstrip().startswith('have ') and b.rstrip().endswith(':= rfl') and ' : ' in a and ' := ' in a:
            after[i]=a
    return '\n'.join(after)+'\n'

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--input',required=True)
    ap.add_argument('--output',required=True)
    ap.add_argument('--seconds',type=float,default=120.0)
    ap.add_argument('--keep',type=int,default=64)
    ap.add_argument('--partners',type=int,default=256)
    args=ap.parse_args()

    m=load(SOLVER,'mg_given_clause')
    row=row_for(args.input)
    source=m.parse_equation(row['equation1'])
    target=m.parse_equation(row['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE)
    limits.update({
        'seconds':args.seconds,
        'maximum_term_size':65,
        'maximum_replay_term_size':300,
        'maximum_depth':12,
        'maximum_rules':768,
        'maximum_rounds':100000,
        'new_clauses_per_round':args.keep,
        'maximum_clauses':12000,
        'normalization_steps':256,
        'maximum_proof_nodes':60000,
    })
    engine=m.TargetGroundedRefutation(source,target,time.monotonic()+args.seconds,limits)
    search=engine.search
    original_cp=search.critical_pair
    expansion_calls=0; expansion_changed=0; enumerated=0; given_steps=0
    partial_partner_scans=0; max_active=0

    def expand_term(t):
        if t[0]=='var' and t[1] in engine.reverse_constants:
            return expand_term(engine.reverse_constants[t[1]])
        if t[0]=='op':
            return ('op',expand_term(t[1]),expand_term(t[2]))
        return t

    def expand_recipe(r,cache=None):
        cache={} if cache is None else cache
        if id(r) in cache:
            return cache[id(r)]
        ps=tuple(expand_recipe(p,cache) for p in r.parents)
        data=r.data
        if r.kind=='source':
            sub,rev=data
            data=(tuple((k,expand_term(v)) for k,v in sub),rev)
        elif r.kind=='instantiate':
            data=tuple((k,expand_term(v)) for k,v in data)
        elif r.kind=='congruence':
            data=(data[0],expand_term(data[1]))
        q=m.Recipe(expand_term(r.lhs),expand_term(r.rhs),r.kind,ps,data)
        cache[id(r)]=q
        return q

    def cp(outer,inner,oi,ii,path):
        nonlocal expansion_calls, expansion_changed
        expansion_calls+=1
        eo=expand_recipe(outer); ei=expand_recipe(inner)
        if (eo.lhs,eo.rhs,ei.lhs,ei.rhs)!=(outer.lhs,outer.rhs,inner.lhs,inner.rhs):
            expansion_changed+=1
        return original_cp(eo,ei,oi,ii,path)
    search.critical_pair=cp

    def variants(clause):
        oriented=search.orient(clause)
        if oriented is not None:
            return [oriented]
        out=[]
        if clause.lhs[0]!='var':
            out.append(clause)
        if clause.rhs[0]!='var':
            out.append(m.Recipe(clause.rhs,clause.lhs,'symmetry',(clause,)))
        return out

    def rkey(r):
        return (search.alpha_signature(r.lhs,r.rhs), r.lhs, r.rhs)

    pending=[]; queued=set(); processed=set(); active=[]
    def enqueue(rule):
        key=rkey(rule)
        if key in processed or key in queued:
            return
        queued.add(key); pending.append(rule)
    for rule in search.rules():
        enqueue(rule)

    start=time.monotonic(); recipe=None
    while pending and not search.expired() and len(search.clauses)<limits['maximum_clauses']:
        pending.sort(key=search.target_score)
        given=pending.pop(0); gkey=rkey(given); queued.discard(gkey)
        if gkey in processed:
            continue
        processed.add(gkey); given_steps+=1
        current_rules=search.rules()
        goal=search.target_proof(current_rules)
        if goal is not None:
            recipe=goal; break

        partners=active[-args.partners:]
        if len(active)>len(partners):
            partial_partner_scans+=1
        pairings=[]
        for partner in partners:
            pairings.append((given,partner))
            if rkey(partner)!=gkey:
                pairings.append((partner,given))
        pairings.append((given,given))
        proposals=[]
        expired=False
        for oi,(outer,inner) in enumerate(pairings):
            if search.expired():
                expired=True; break
            for path in m.nonvariable_positions(outer.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
                if search.expired():
                    expired=True; break
                p=search.critical_pair(outer,inner,oi,oi+1,path)
                if p is None:
                    continue
                p=search.interreduce(p,current_rules)
                proposals.append((search.target_score(p),p)); enumerated+=1
            if expired:
                break
        proposals.sort(key=lambda x:x[0])
        added=0
        for _,p in proposals:
            before=len(search.clauses)
            if search.add_clause(p):
                search.superpositions+=1; added+=1
                for clause in search.clauses[before:]:
                    for rule in variants(clause):
                        enqueue(rule)
                if added>=args.keep:
                    break
        active.append(given); max_active=max(max_active,len(active))
        search.rounds=given_steps
        goal=search.target_proof(search.rules())
        if goal is not None:
            recipe=goal; break
        if expired:
            break

    if recipe is None:
        recipe=search.target_proof(search.rules())
    elapsed=time.monotonic()-start
    out={
        'id':RID,'found_recipe':bool(recipe),'seconds':elapsed,
        'given_steps':given_steps,'active_rules':len(active),'max_active':max_active,
        'pending_rules':len(pending),'processed_rule_keys':len(processed),
        'clauses':len(search.clauses),'generated':search.generated,
        'superpositions':search.superpositions,'reductions':search.reductions,
        'enumerated':enumerated,'expansion_calls':expansion_calls,
        'expansion_changed':expansion_changed,'partial_partner_scans':partial_partner_scans,
        'keep':args.keep,'partners':args.partners,
        'target_hit':False,'replay':False,'proof_nodes':None,
        'certificate_bytes':None,'judge_status':None,'judge_error_code':None,
    }
    if recipe is not None:
        rr=engine.inline_recipe(recipe)
        if (rr.lhs,rr.rhs)==(target[1],target[0]):
            rr=m.Recipe(rr.rhs,rr.lhs,'symmetry',(rr,))
        nodes,root=search.compile(rr)
        out['target_hit']=(nodes[root].lhs,nodes[root].rhs)==target[:2]
        out['replay']=bool(m.replay_dag(source,nodes,root,maximum_term_size=limits['maximum_replay_term_size'],maximum_nodes=limits['maximum_proof_nodes']))
        if out['target_hit'] and out['replay']:
            code,n=m.make_dag_certificate(target,nodes,root); code=compact(m,code)
            out['proof_nodes']=n; out['certificate_bytes']=len(code.encode())
            if out['certificate_bytes']<=100000:
                cfg=replace(_resolve_config(None),max_code_length=100000)
                res=verify_answer(row,json.dumps({'verdict':'true','code':code}),config=cfg)
                out['judge_status']=res.get('status'); out['judge_error_code']=res.get('error_code'); out['judge_message']=res.get('message')
    Path(args.output).parent.mkdir(parents=True,exist_ok=True)
    Path(args.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('GIVEN_CLAUSE_SEARCH',json.dumps(out,sort_keys=True),flush=True)

if __name__=='__main__':
    main()

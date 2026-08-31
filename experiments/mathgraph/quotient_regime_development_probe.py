#!/usr/bin/env python3
"""Test whether a new bounded-future quotient class develops into a stronger regime law.

The first stage discovers a strict reducer whose continuation signature is absent from a
bounded pre-repair quotient. Its alpha-canonical equation is then re-proved independently
from the original source, making the law portable. Finally a fixed problem-blind grammar
of small collapse schemas is searched with that derived law available. Every positive
must replay from the original source.
"""
import argparse, importlib.util, json, time


def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True)
    args=ap.parse_args(); m=load(args.solver); row=json.load(open(args.row)); source=m.parse_equation(row['equation1']); original_target=m.parse_equation(row['equation2'])
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':128,'new_clauses_per_round':64,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})

    def setup(target,seconds):
        limits=dict(base); limits['seconds']=seconds
        e=m.TargetGroundedRefutation(source,target,time.monotonic()+seconds,limits)
        return e,e.search

    def profile(q):
        lv=m.term_variables(q.lhs); rv=m.term_variables(q.rhs)
        for vside,other in ((q.lhs,q.rhs),(q.rhs,q.lhs)):
            if vside[0]=='var':
                d=vside[1]; ov=m.term_variables(other)
                if d not in ov:return (0,0,len(ov))
                return (1,len(ov-{d}),len(ov))
        if lv<rv:return (2,len(rv-lv),len(rv))
        if rv<lv:return (2,len(lv-rv),len(lv))
        return (3,len(lv|rv),len(lv|rv))

    e,s=setup(original_target,24.0)
    for _ in range(3):
        rules=s.rules(); snap=list(rules); props=[]
        for oi,o in enumerate(snap):
            for ii,i in enumerate(snap):
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    if s.expired():break
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None:continue
                    c=s.interreduce(c,rules); props.append((s.target_score(c),c))
                    if len(props)>=128:
                        props.sort(key=lambda x:x[0]); added=0
                        for _,q in props:
                            if s.add_clause(q):s.superpositions+=1; added+=1
                            if added>=64:break
                        props=[]; rules=s.rules()
                if s.expired():break
            if s.expired():break
        if props and not s.expired():
            props.sort(key=lambda x:x[0]); added=0
            for _,q in props:
                if s.add_clause(q):s.superpositions+=1; added+=1
                if added>=64:break
        if s.expired():break

    objects=sorted(s.clauses,key=s.target_score)[:192]; probes=objects[:32]
    def alpha_sig(q):return str(s.alpha_signature(q.lhs,q.rhs))
    def orient(q,r):return q if not r else m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
    def future(q):
        out=set()
        for pi,p in enumerate(probes):
            for first,second in ((q,p),(p,q)):
                for fr in (False,True):
                    aa=orient(first,fr)
                    for sr in (False,True):
                        bb=orient(second,sr)
                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=6,include_root=True):
                            c=s.critical_pair(aa,bb,0,pi,path)
                            if c is not None:out.add(alpha_sig(c))
        return frozenset(out)
    base_futures={future(q) for q in objects}
    source_profile=profile(m.Recipe(source[0],source[1],'reflexivity'))
    s.deadline=time.monotonic()+12.0; rules=s.rules(); seen=set(); candidates=[]
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired():break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None:continue
                c=s.interreduce(c,rules)
                names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(x.startswith('@') for x in names) or not profile(c)<source_profile:continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen:continue
                seen.add(key); ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=300,maximum_nodes=60000):continue
                fs=future(c)
                if fs not in base_futures:candidates.append((profile(c),m.term_size(c.lhs)+m.term_size(c.rhs),c.cost,c,fs))
            if s.expired():break
        if s.expired():break
    candidates.sort(key=lambda x:(x[0],x[1],x[2],m.render_term(x[3].lhs),m.render_term(x[3].rhs)))
    if not candidates:
        print('QUOTIENT_REGIME '+json.dumps({'id':row['id'],'new_class':False},sort_keys=True));return
    discovered=candidates[0][3]

    names={}
    def canon(t):
        if t[0]=='var':
            if t[1] not in names:names[t[1]]=chr(ord('x')+len(names))
            return ('var',names[t[1]])
        return ('op',canon(t[1]),canon(t[2]))
    cl,cr=canon(discovered.lhs),canon(discovered.rhs)
    cvars=tuple(dict.fromkeys(list(names.values())))
    canonical_goal=(cl,cr,cvars)

    ce,cs=setup(canonical_goal,75.0); cf=cs.solve(); portable=None; canonical_info={'found':cf is not None,'replay':False}
    if cf is not None:
        ci=ce.inline_recipe(cf)
        if (ci.lhs,ci.rhs)==(canonical_goal[1],canonical_goal[0]):ci=m.Recipe(ci.rhs,ci.lhs,'symmetry',(ci,))
        if (ci.lhs,ci.rhs)==canonical_goal[:2]:
            ns,r=cs.compile(ci); ok=m.replay_dag(source,ns,r,maximum_term_size=300,maximum_nodes=60000)
            canonical_info={'found':True,'replay':ok,'proof_nodes':len(ns)}
            if ok:
                def expand_term(t):
                    if t[0]=='var' and t[1] in ce.reverse_constants:return expand_term(ce.reverse_constants[t[1]])
                    if t[0]=='op':return ('op',expand_term(t[1]),expand_term(t[2]))
                    return t
                def expand_recipe(q,cache=None):
                    cache={} if cache is None else cache; k=id(q)
                    if k in cache:return cache[k]
                    ps=tuple(expand_recipe(p,cache) for p in q.parents); data=q.data
                    if q.kind=='source':
                        sub,rev=data; data=(tuple((k,expand_term(v)) for k,v in sub),rev)
                    elif q.kind=='instantiate':data=tuple((k,expand_term(v)) for k,v in data)
                    elif q.kind=='congruence':data=(data[0],expand_term(data[1]))
                    z=m.Recipe(expand_term(q.lhs),expand_term(q.rhs),q.kind,ps,data);cache[k]=z;return z
                portable=expand_recipe(ci)

    # Projection first: small-model diagnostics make it the highest-information generic schema,
    # while the vocabulary itself remains fixed and problem-blind.
    schemas=[('left-projection','x * y = x'),('idempotence','x * x = x'),('right-projection','x * y = y'),('carrier-collapse','x = y'),('left-absorb-right','x * (x * y) = x'),('left-absorb-left','x * (y * x) = x'),('right-absorb-right','(x * y) * x = x'),('right-absorb-left','(y * x) * x = x')]
    traces=[]; certified=[]
    if portable is not None:
        for name,text in schemas:
            goal=m.parse_equation(text); ge,gs=setup(goal,45.0); added=gs.add_clause(portable); t=time.monotonic(); found=gs.solve(); rec={'schema':name,'text':text,'added':bool(added),'found':found is not None,'elapsed':round(time.monotonic()-t,3),'replay':False}
            if found is not None:
                gi=ge.inline_recipe(found)
                if (gi.lhs,gi.rhs)==(goal[1],goal[0]):gi=m.Recipe(gi.rhs,gi.lhs,'symmetry',(gi,))
                if (gi.lhs,gi.rhs)==goal[:2]:
                    ns,r=gs.compile(gi); ok=m.replay_dag(source,ns,r,maximum_term_size=300,maximum_nodes=60000);rec['replay']=ok;rec['proof_nodes']=len(ns)
                    if ok:certified.append((name,gi,ge,gs))
            traces.append(rec)
            # A certified left projection is terminal for this source regime; no need to spend
            # budget on weaker alternatives before testing the original target.
            if name=='left-projection' and rec['replay']:
                break

    target_info={'found':False,'replay':False}
    if certified:
        te,ts=setup(original_target,120.0); added=0
        if portable is not None and ts.add_clause(portable):added+=1
        for _,law,_,_ in certified:
            if ts.add_clause(law):added+=1
        tf=ts.collapse_proof()
        if tf is None:tf=ts.target_proof(ts.rules())
        if tf is None:tf=ts.solve()
        target_info={'found':tf is not None,'replay':False,'added':added,'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses)}
        if tf is not None:
            ti=te.inline_recipe(tf)
            if (ti.lhs,ti.rhs)==(original_target[1],original_target[0]):ti=m.Recipe(ti.rhs,ti.lhs,'symmetry',(ti,))
            if (ti.lhs,ti.rhs)==original_target[:2]:
                ns,r=ts.compile(ti);target_info['replay']=m.replay_dag(source,ns,r,maximum_term_size=300,maximum_nodes=60000);target_info['proof_nodes']=len(ns)

    report={'id':row['id'],'new_class':True,'discovered':{'profile':list(profile(discovered)),'lhs':m.render_term(discovered.lhs),'rhs':m.render_term(discovered.rhs),'future_size':len(candidates[0][4])},'canonical':{'lhs':m.render_term(cl),'rhs':m.render_term(cr),**canonical_info},'schemas':traces,'certified_schemas':[x[0] for x in certified],'target':target_info}
    print('QUOTIENT_REGIME '+json.dumps(report,sort_keys=True),flush=True)

if __name__=='__main__':main()

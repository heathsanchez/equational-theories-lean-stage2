#!/usr/bin/env python3
"""Compile a novel future-quotient class through the proof-variable boundary.

A derived Recipe may mention standardized-apart/internal variables in its proof even when
its observable endpoint has lower support. CompactSuperposition.compile already projects
such variables onto in-scope target variables. This probe uses that verified compiler step
as the quotient-to-interface map, then tests whether the projected law develops a stronger
fixed collapse schema and closes the original target.
"""
import argparse, importlib.util, json, time


def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True)
    args=ap.parse_args(); m=load(args.solver); row=json.load(open(args.row)); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':128,'new_clauses_per_round':64,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})
    def setup(goal,seconds):
        lim=dict(base);lim['seconds']=seconds;e=m.TargetGroundedRefutation(source,goal,time.monotonic()+seconds,lim);return e,e.search
    def profile(q):
        lv=m.term_variables(q.lhs);rv=m.term_variables(q.rhs)
        for vs,other in ((q.lhs,q.rhs),(q.rhs,q.lhs)):
            if vs[0]=='var':
                d=vs[1];ov=m.term_variables(other)
                if d not in ov:return (0,0,len(ov))
                return (1,len(ov-{d}),len(ov))
        if lv<rv:return (2,len(rv-lv),len(rv))
        if rv<lv:return (2,len(lv-rv),len(lv))
        return (3,len(lv|rv),len(lv|rv))

    # Reconstruct the bounded pre-repair world and its fixed future quotient.
    e,s=setup(target,24.0)
    for _ in range(3):
        rules=s.rules();snap=list(rules);props=[]
        for oi,o in enumerate(snap):
            for ii,i in enumerate(snap):
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    if s.expired():break
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None:continue
                    c=s.interreduce(c,rules);props.append((s.target_score(c),c))
                    if len(props)>=128:
                        props.sort(key=lambda x:x[0]);added=0
                        for _,q in props:
                            if s.add_clause(q):s.superpositions+=1;added+=1
                            if added>=64:break
                        props=[];rules=s.rules()
                if s.expired():break
            if s.expired():break
        if props and not s.expired():
            props.sort(key=lambda x:x[0]);added=0
            for _,q in props:
                if s.add_clause(q):s.superpositions+=1;added+=1
                if added>=64:break
        if s.expired():break
    objects=sorted(s.clauses,key=s.target_score)[:192];probes=objects[:32]
    def alpha(q):return str(s.alpha_signature(q.lhs,q.rhs))
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
                            if c is not None:out.add(alpha(c))
        return frozenset(out)
    old={future(q) for q in objects};srcprof=profile(m.Recipe(source[0],source[1],'reflexivity'))
    s.deadline=time.monotonic()+12.0;rules=s.rules();seen=set();new=[]
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired():break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None:continue
                c=s.interreduce(c,rules);names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names) or not profile(c)<srcprof:continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen:continue
                seen.add(key);ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=300,maximum_nodes=60000):continue
                fs=future(c)
                if fs not in old:new.append((profile(c),m.term_size(c.lhs)+m.term_size(c.rhs),c.cost,c,fs))
            if s.expired():break
        if s.expired():break
    new.sort(key=lambda x:(x[0],x[1],x[2],m.render_term(x[3].lhs),m.render_term(x[3].rhs)))
    if not new:
        print('QUOTIENT_INTERFACE '+json.dumps({'id':row['id'],'new_class':False},sort_keys=True));return
    law=new[0][3]

    # Alpha-canonical endpoint for the observable interface.
    names={}
    def canon(t):
        if t[0]=='var':
            if t[1] not in names:names[t[1]]=chr(ord('x')+len(names))
            return ('var',names[t[1]])
        return ('op',canon(t[1]),canon(t[2]))
    cl,cr=canon(law.lhs),canon(law.rhs);goal=(cl,cr,tuple(dict.fromkeys(names.values())))

    # The new representation step: compile the original proof under the smaller
    # interface. compile() projects every internal/unobserved proof variable to an
    # in-scope goal variable. No theorem search is performed here.
    pe,ps=setup(goal,5.0);p_nodes,p_root=ps.compile(law)
    projected_ok=m.replay_dag(source,p_nodes,p_root,maximum_term_size=300,maximum_nodes=60000)
    projected_endpoint=(p_nodes[p_root].lhs,p_nodes[p_root].rhs) if projected_ok else (None,None)
    projected_exact=projected_endpoint==goal[:2] or projected_endpoint==(goal[1],goal[0])

    schemas=[('left-projection','x * y = x'),('idempotence','x * x = x'),('right-projection','x * y = y'),('carrier-collapse','x = y'),('left-absorb-right','x * (x * y) = x'),('left-absorb-left','x * (y * x) = x'),('right-absorb-right','(x * y) * x = x'),('right-absorb-left','(y * x) * x = x')]
    traces=[];cert=[]
    if projected_ok and projected_exact:
        for name,text in schemas:
            g=m.parse_equation(text);ge,gs=setup(g,45.0);added=gs.add_clause(law);found=gs.solve();rec={'schema':name,'added':bool(added),'found':found is not None,'replay':False}
            if found is not None:
                gi=ge.inline_recipe(found)
                if (gi.lhs,gi.rhs)==(g[1],g[0]):gi=m.Recipe(gi.rhs,gi.lhs,'symmetry',(gi,))
                if (gi.lhs,gi.rhs)==g[:2]:
                    ns,r=gs.compile(gi);ok=m.replay_dag(source,ns,r,maximum_term_size=300,maximum_nodes=60000);rec['replay']=ok;rec['proof_nodes']=len(ns)
                    if ok:cert.append((name,gi))
            traces.append(rec)
            if name=='left-projection' and rec['replay']:break

    target_info={'found':False,'replay':False}
    if cert:
        te,ts=setup(target,120.0);added=0
        if ts.add_clause(law):added+=1
        for _,q in cert:
            if ts.add_clause(q):added+=1
        tf=ts.collapse_proof()
        if tf is None:tf=ts.target_proof(ts.rules())
        if tf is None:tf=ts.solve()
        target_info={'found':tf is not None,'replay':False,'added':added,'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses)}
        if tf is not None:
            ti=te.inline_recipe(tf)
            if (ti.lhs,ti.rhs)==(target[1],target[0]):ti=m.Recipe(ti.rhs,ti.lhs,'symmetry',(ti,))
            if (ti.lhs,ti.rhs)==target[:2]:
                ns,r=ts.compile(ti);target_info['replay']=m.replay_dag(source,ns,r,maximum_term_size=300,maximum_nodes=60000);target_info['proof_nodes']=len(ns)

    report={'id':row['id'],'new_class':True,'law':{'lhs':m.render_term(law.lhs),'rhs':m.render_term(law.rhs),'profile':list(profile(law)),'future_size':len(new[0][4])},'projected':{'lhs':m.render_term(cl),'rhs':m.render_term(cr),'replay':projected_ok,'exact':projected_exact,'proof_nodes':len(p_nodes)},'schemas':traces,'certified':[x[0] for x in cert],'target':target_info}
    print('QUOTIENT_INTERFACE '+json.dumps(report,sort_keys=True),flush=True)

if __name__=='__main__':main()

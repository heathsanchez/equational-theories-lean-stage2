#!/usr/bin/env python3
"""Iterate future-quotient -> observable-interface development on one fresh residual.

Starts from the original source law, discovers a replay-certified consequence whose bounded
future signature is new, projects that consequence to the smallest observable alpha interface,
promotes the projected law, and repeats. Each promoted law must replay from the ORIGINAL source.
No benchmark IDs, fixed bridge laws, or target-specific schemas steer the iteration.
"""
import argparse, importlib.util, json, time


def load(path):
    spec = importlib.util.spec_from_file_location('mgsolver', path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); ap.add_argument('--generations',type=int,default=3)
    args=ap.parse_args(); m=load(args.solver); row=json.load(open(args.row))
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})

    def setup(goal, seconds):
        lim=dict(base); lim['seconds']=seconds
        e=m.TargetGroundedRefutation(source,goal,time.monotonic()+seconds,lim); return e,e.search

    def profile(q):
        lv=m.term_variables(q.lhs); rv=m.term_variables(q.rhs)
        for vs,other in ((q.lhs,q.rhs),(q.rhs,q.lhs)):
            if vs[0]=='var':
                d=vs[1]; ov=m.term_variables(other)
                if d not in ov:return (0,0,len(ov))
                return (1,len(ov-{d}),len(ov))
        if lv<rv:return (2,len(rv-lv),len(rv))
        if rv<lv:return (2,len(lv-rv),len(lv))
        return (3,len(lv|rv),len(lv|rv))

    def canon_recipe(q):
        names={}
        def canon(t):
            if t[0]=='var':
                if t[1] not in names:names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',canon(t[1]),canon(t[2]))
        return canon(q.lhs),canon(q.rhs),tuple(dict.fromkeys(names.values()))

    promoted=[]; trace=[]; seen_interfaces=set()
    current_goal=target

    for generation in range(1,args.generations+1):
        e,s=setup(current_goal,28.0)
        for q in promoted:s.add_clause(q)
        # Build bounded world from the current promoted interface.
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

        objects=sorted(s.clauses,key=s.target_score)[:192]; probes=objects[:32]
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
        old={future(q) for q in objects}
        baseline_profile=min([profile(q) for q in promoted],default=profile(m.Recipe(source[0],source[1],'reflexivity')))
        s.deadline=time.monotonic()+14.0; rules=s.rules(); seen=set(); candidates=[]
        for oi,o in enumerate(rules):
            for ii,i in enumerate(rules):
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    if s.expired():break
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None:continue
                    c=s.interreduce(c,rules); names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                    if c.lhs==c.rhs or any(v.startswith('@') for v in names):continue
                    key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                    if key in seen:continue
                    seen.add(key)
                    ns,r=s.compile(c)
                    if not m.replay_dag(source,ns,r,maximum_term_size=300,maximum_nodes=60000):continue
                    fs=future(c)
                    if fs in old:continue
                    cl,cr,cvars=canon_recipe(c); iface=(cl,cr,cvars)
                    rev=(cr,cl,cvars)
                    if iface in seen_interfaces or rev in seen_interfaces:continue
                    candidates.append((profile(c),m.term_size(c.lhs)+m.term_size(c.rhs),c.cost,-len(fs),c,fs,iface))
                if s.expired():break
            if s.expired():break
        candidates.sort(key=lambda x:(x[0],x[1],x[2],x[3],m.render_term(x[4].lhs),m.render_term(x[4].rhs)))
        if not candidates:
            trace.append({'generation':generation,'new_class':False,'clauses':len(s.clauses),'baseline_profile':list(baseline_profile)});break

        _,_,_,_,law,fs,iface=candidates[0]; cl,cr,cvars=iface; goal=(cl,cr,cvars)
        pe,ps=setup(goal,6.0); p_nodes,p_root=ps.compile(law)
        ok=m.replay_dag(source,p_nodes,p_root,maximum_term_size=300,maximum_nodes=60000)
        endpoint=(p_nodes[p_root].lhs,p_nodes[p_root].rhs) if ok else (None,None)
        exact=endpoint==goal[:2] or endpoint==(goal[1],goal[0])
        rec={'generation':generation,'new_class':True,'future_size':len(fs),'raw':{'lhs':m.render_term(law.lhs),'rhs':m.render_term(law.rhs),'profile':list(profile(law))},'projected':{'lhs':m.render_term(cl),'rhs':m.render_term(cr),'vars':list(cvars),'replay':bool(ok),'exact':bool(exact),'proof_nodes':len(p_nodes)}}
        trace.append(rec)
        if not (ok and exact):break
        # Preserve original proof-bearing recipe; the canonical endpoint is the observable interface.
        promoted.append(law); seen_interfaces.add(iface)
        current_goal=goal

        # After every successful representation change, test the original target immediately.
        te,ts=setup(target,90.0)
        for q in promoted:ts.add_clause(q)
        found=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve()
        target_rec={'after_generation':generation,'found':found is not None,'replay':False,'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses)}
        if found is not None:
            ti=te.inline_recipe(found)
            if (ti.lhs,ti.rhs)==(target[1],target[0]):ti=m.Recipe(ti.rhs,ti.lhs,'symmetry',(ti,))
            if (ti.lhs,ti.rhs)==target[:2]:
                ns,r=ts.compile(ti); target_rec['replay']=m.replay_dag(source,ns,r,maximum_term_size=300,maximum_nodes=60000); target_rec['proof_nodes']=len(ns)
        rec['target']=target_rec
        if target_rec['replay']:break

    print('RECURSIVE_QUOTIENT '+json.dumps({'id':row['id'],'generations':trace,'promoted':len(promoted)},sort_keys=True),flush=True)

if __name__=='__main__':main()

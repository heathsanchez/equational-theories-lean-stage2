#!/usr/bin/env python3
"""Iterate future-quotient development without requiring endpoint collapse.

A replay-certified novel future class is itself a valid relational interface even when
compilation does not collapse it to the alpha-canonical endpoint proposed by its raw
surface form. This probe carries the actual replayed compiled endpoint forward as the
next typed interface, while retaining the original proof-bearing Recipe as a promoted
source consequence. No benchmark IDs or target-specific bridge laws steer selection.
"""
import argparse, importlib.util, json, time


def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); ap.add_argument('--generations',type=int,default=3)
    args=ap.parse_args(); m=load(args.solver); row=json.load(open(args.row))
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})

    def setup(goal,seconds):
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

    def canon_pair(lhs,rhs):
        names={}
        def canon(t):
            if t[0]=='var':
                if t[1] not in names:names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',canon(t[1]),canon(t[2]))
        cl,cr=canon(lhs),canon(rhs)
        return cl,cr,tuple(dict.fromkeys(names.values()))

    promoted=[]; trace=[]; seen_interfaces=set(); current_goal=target
    for generation in range(1,args.generations+1):
        e,s=setup(current_goal,30.0)
        for q in promoted:s.add_clause(q)
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
                            props=[]; rules=s.rules()
                    if s.expired():break
                if s.expired():break
            if props and not s.expired():
                props.sort(key=lambda x:x[0]); added=0
                for _,q in props:
                    if s.add_clause(q):s.superpositions+=1;added+=1
                    if added>=64:break
            if s.expired():break

        objects=sorted(s.clauses,key=s.target_score)[:224]; probes=objects[:40]
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
        s.deadline=time.monotonic()+16.0; rules=s.rules(); seen=set(); candidates=[]
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
                    if not m.replay_dag(source,ns,r,maximum_term_size=320,maximum_nodes=70000):continue
                    fs=future(c)
                    if fs in old:continue
                    raw_iface=canon_pair(c.lhs,c.rhs)
                    if raw_iface in seen_interfaces or (raw_iface[1],raw_iface[0],raw_iface[2]) in seen_interfaces:continue
                    candidates.append((profile(c),m.term_size(c.lhs)+m.term_size(c.rhs),c.cost,-len(fs),c,fs,raw_iface))
                if s.expired():break
            if s.expired():break
        candidates.sort(key=lambda x:(x[0],x[1],x[2],x[3],m.render_term(x[4].lhs),m.render_term(x[4].rhs)))
        if not candidates:
            trace.append({'generation':generation,'new_class':False,'clauses':len(s.clauses)}); break

        _,_,_,_,law,fs,raw_iface=candidates[0]
        rg=(raw_iface[0],raw_iface[1],raw_iface[2]); pe,ps=setup(rg,7.0)
        p_nodes,p_root=ps.compile(law)
        ok=m.replay_dag(source,p_nodes,p_root,maximum_term_size=320,maximum_nodes=70000)
        endpoint=(p_nodes[p_root].lhs,p_nodes[p_root].rhs) if ok else (None,None)
        rec={'generation':generation,'new_class':True,'future_size':len(fs),'raw':{'lhs':m.render_term(law.lhs),'rhs':m.render_term(law.rhs),'profile':list(profile(law))},'compiled':{'replay':bool(ok),'proof_nodes':len(p_nodes)}}
        if not ok:
            trace.append(rec); break
        actual_iface=canon_pair(endpoint[0],endpoint[1])
        rec['compiled'].update({'lhs':m.render_term(endpoint[0]),'rhs':m.render_term(endpoint[1]),'interface_lhs':m.render_term(actual_iface[0]),'interface_rhs':m.render_term(actual_iface[1]),'vars':list(actual_iface[2]),'exact_raw':endpoint==rg[:2] or endpoint==(rg[1],rg[0])})
        trace.append(rec)
        if actual_iface in seen_interfaces or (actual_iface[1],actual_iface[0],actual_iface[2]) in seen_interfaces:
            rec['plateau']='compiled interface already represented'; break
        promoted.append(law); seen_interfaces.add(actual_iface)
        current_goal=(actual_iface[0],actual_iface[1],actual_iface[2])

        te,ts=setup(target,100.0)
        for q in promoted:ts.add_clause(q)
        found=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve()
        target_rec={'after_generation':generation,'found':found is not None,'replay':False,'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses)}
        if found is not None:
            ti=te.inline_recipe(found)
            if (ti.lhs,ti.rhs)==(target[1],target[0]):ti=m.Recipe(ti.rhs,ti.lhs,'symmetry',(ti,))
            if (ti.lhs,ti.rhs)==target[:2]:
                ns,r=ts.compile(ti);target_rec['replay']=m.replay_dag(source,ns,r,maximum_term_size=320,maximum_nodes=70000);target_rec['proof_nodes']=len(ns)
        rec['target']=target_rec
        if target_rec['replay']:break

    print('RELATIONAL_QUOTIENT '+json.dumps({'id':row['id'],'generations':trace,'promoted':len(promoted)},sort_keys=True),flush=True)

if __name__=='__main__':main()

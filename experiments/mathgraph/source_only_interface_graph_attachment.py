#!/usr/bin/env python3
import argparse, importlib.util, json, time

def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver', path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); a=ap.parse_args()
    m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); neutral=m.parse_equation('x = x'); target=m.parse_equation('x = x * x')
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})
    def setup(goal,sec):
        lim=dict(base); lim['seconds']=sec
        e=m.TargetGroundedRefutation(source,goal,time.monotonic()+sec,lim); return e,e.search
    def canon(lhs,rhs):
        names={}
        def f(t):
            if t[0]=='var':
                if t[1] not in names: names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',f(t[1]),f(t[2]))
        return f(lhs),f(rhs),tuple(dict.fromkeys(names.values()))
    def skey(s,q): return (m.term_size(q.lhs)+m.term_size(q.rhs),str(s.alpha_signature(q.lhs,q.rhs)),m.render_term(q.lhs),m.render_term(q.rhs))
    def is_target(q): return (q.lhs,q.rhs)==target[:2] or (q.rhs,q.lhs)==target[:2]
    def replay(q):
        ee,ss=setup(target,2.0); qq=ee.inline_recipe(q)
        if (qq.lhs,qq.rhs)==(target[1],target[0]): qq=m.Recipe(qq.rhs,qq.lhs,'symmetry',(qq,))
        if (qq.lhs,qq.rhs)!=target[:2]: return False,None
        nn,rr=ss.compile(qq); ok=m.replay_dag(source,nn,rr,maximum_term_size=320,maximum_nodes=70000); return ok,len(nn) if ok else None

    t0=time.monotonic(); e,s=setup(neutral,20.0); pre=[]
    for gen in range(1,4):
        rules=s.rules(); snap=list(rules); props=[]; proposed=0; stop=False
        for oi,o in enumerate(snap):
            if stop: break
            for ii,i in enumerate(snap):
                if stop: break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    c=s.interreduce(c,rules); props.append(c); proposed+=1
                    if proposed>=512: stop=True; break
        props.sort(key=lambda q:skey(s,q)); added=0
        for q in props:
            if s.add_clause(q): s.superpositions+=1; added+=1
            if added>=64: break
        pre.append({'generation':gen,'proposed':proposed,'added':added,'clauses':len(s.clauses)})

    seen=set(); recipes=[]; meta=[]; census=replayed=projected=0; rules=s.rules(); s.deadline=time.monotonic()+12.0
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired() or census>=176: break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None: continue
                c=s.interreduce(c,rules); names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names): continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen: continue
                seen.add(key); census+=1
                ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=320,maximum_nodes=70000): continue
                replayed+=1
                raw=canon(c.lhs,c.rhs); pe,ps=setup(raw,2.0); pn,pr=ps.compile(c)
                if not m.replay_dag(source,pn,pr,maximum_term_size=320,maximum_nodes=70000): continue
                projected+=1; ep=(pn[pr].lhs,pn[pr].rhs); act=canon(ep[0],ep[1])
                if act[2]!=('x',): continue
                recipes.append(c); meta.append({'lhs':m.render_term(act[0]),'rhs':m.render_term(act[1]),'proof_nodes':len(pn)})
            if s.expired() or census>=176: break
        if s.expired() or census>=176: break

    order=sorted(range(len(recipes)), key=lambda j:(m.term_size(recipes[j].lhs)+m.term_size(recipes[j].rhs), meta[j]['proof_nodes'], meta[j]['lhs'], meta[j]['rhs']))
    chosen=[]; sigs=set()
    for j in order:
        sig=str(s.alpha_signature(recipes[j].lhs,recipes[j].rhs))
        if sig in sigs: continue
        sigs.add(sig); chosen.append(j)
        if len(chosen)>=32: break
    nodes=[recipes[j] for j in chosen]

    ae,asrch=setup(target,30.0); graph_seen=set(); edges=0; exact=None; traces=[]; frontier=nodes; all_nodes=list(nodes); total_generated=0
    for gen in range(1,4):
        cand=[]; gen_generated=0
        # preserve recursion: each new frontier can interact with the original interfaces and the previous frontier.
        partners=(nodes + all_nodes[-32:])[:64]
        stop=False
        for ai,a0 in enumerate(frontier[:32]):
            if stop: break
            for bi,b0 in enumerate(partners):
                if stop: break
                for ra in (False,True):
                    a1=a0 if not ra else m.Recipe(a0.rhs,a0.lhs,'symmetry',(a0,))
                    for rb in (False,True):
                        b1=b0 if not rb else m.Recipe(b0.rhs,b0.lhs,'symmetry',(b0,))
                        for path in m.nonvariable_positions(a1.lhs,maximum_depth=10,include_root=True):
                            c=asrch.critical_pair(a1,b1,ai,bi,path)
                            if c is None: continue
                            c=asrch.interreduce(c,asrch.rules()); edges+=1
                            if c.lhs==c.rhs: continue
                            k=(asrch.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                            if k in graph_seen: continue
                            graph_seen.add(k); gen_generated+=1; total_generated+=1
                            if is_target(c):
                                ok,pn=replay(c)
                                if ok:
                                    exact={'generation':gen,'proof_nodes':pn,'lhs':m.render_term(c.lhs),'rhs':m.render_term(c.rhs)}; stop=True; break
                            cand.append(c)
                            if gen_generated>=4096: stop=True; break
                        if stop: break
                    if stop: break
        cand.sort(key=lambda q:(asrch.target_score(q),m.term_size(q.lhs)+m.term_size(q.rhs),m.render_term(q.lhs),m.render_term(q.rhs)))
        frontier=cand[:32]; all_nodes.extend(frontier)
        traces.append({'generation':gen,'children':len(cand),'frontier':len(frontier),'edges':edges,'generated_this_generation':gen_generated,'generated_total':total_generated,'best_target_score':asrch.target_score(frontier[0]) if frontier else None})
        if exact or not frontier: break

    out={'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'census':census,'replayed':replayed,'projected':projected,'interfaces':len(recipes),'chosen':len(nodes),'graph_trace':traces,'exact':exact,'recovered':exact is not None}
    print('SOURCE_ONLY_INTERFACE_GRAPH '+json.dumps(out,sort_keys=True),flush=True)
    if exact is None: raise SystemExit(2)
if __name__=='__main__': main()

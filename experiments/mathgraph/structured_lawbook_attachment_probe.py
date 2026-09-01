#!/usr/bin/env python3
import argparse, importlib.util, json, time

def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); ap.add_argument('--goal',choices=('actual','idempotence'),default='actual'); a=ap.parse_args()
    m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); actual=m.parse_equation(row['equation2']); target=actual if a.goal=='actual' else m.parse_equation('x = x * x'); neutral=m.parse_equation('x = x')
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})
    def setup(goal,sec):
        lim=dict(base); lim['seconds']=sec
        e=m.TargetGroundedRefutation(source,goal,time.monotonic()+sec,lim); return e,e.search
    def canon(lhs,rhs):
        names={}
        def f(t):
            if t[0]=='var':
                if t[1] not in names:names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',f(t[1]),f(t[2]))
        return f(lhs),f(rhs),tuple(dict.fromkeys(names.values()))
    def skey(s,q):
        return (m.term_size(q.lhs)+m.term_size(q.rhs),str(s.alpha_signature(q.lhs,q.rhs)),m.render_term(q.lhs),m.render_term(q.rhs))

    t0=time.monotonic(); e,s=setup(neutral,20.0); pre=[]
    for gen in range(1,4):
        rules=s.rules(); snap=list(rules); props=[]; proposed=0; stop=False
        for oi,o in enumerate(snap):
            if stop:break
            for ii,i in enumerate(snap):
                if stop:break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None:continue
                    c=s.interreduce(c,rules); props.append(c); proposed+=1
                    if proposed>=512:stop=True;break
        props.sort(key=lambda q:skey(s,q)); added=0
        for q in props:
            if s.add_clause(q):s.superpositions+=1;added+=1
            if added>=64:break
        pre.append({'generation':gen,'proposed':proposed,'added':added,'clauses':len(s.clauses)})

    seen=set(); recipes=[]; endpoints=[]; census=replayed=projected=0; rules=s.rules(); s.deadline=time.monotonic()+12.0
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired() or census>=176:break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None:continue
                c=s.interreduce(c,rules); names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names):continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen:continue
                seen.add(key);census+=1
                ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=320,maximum_nodes=70000):continue
                replayed+=1; raw=canon(c.lhs,c.rhs); pe,ps=setup(raw,2.0); pn,pr=ps.compile(c)
                if not m.replay_dag(source,pn,pr,maximum_term_size=320,maximum_nodes=70000):continue
                projected+=1; ep=(pn[pr].lhs,pn[pr].rhs); act=canon(ep[0],ep[1])
                if act[2]!=('x',):continue
                recipes.append(c); endpoints.append((act[0],act[1],len(pn)))
            if s.expired() or census>=176:break
        if s.expired() or census>=176:break

    te,ts=setup(target,24.0)
    uniq=[]; ukeys=set()
    # Add every replay-certified source-only interface once, ranked only at attachment time by target relevance.
    ranked=[]
    for q,ep in zip(recipes,endpoints):
        k=(ts.alpha_signature(ep[0],ep[1]),ep[0],ep[1])
        if k in ukeys:continue
        ukeys.add(k); ranked.append((ts.target_score(q), ep[2], q))
    ranked.sort(key=lambda z:(z[0],z[1]))
    for _,_,q in ranked:
        if ts.add_clause(q): uniq.append(q)
    direct=ts.collapse_proof() or ts.target_proof(ts.rules())
    trace=[]; found=direct
    frontier=list(uniq)
    # Preserve relations: expand only from the discovered interface frontier and its descendants.
    for gen in range(1,5):
        if found is not None or ts.expired():break
        rules=ts.rules(); props=[]; proposed=0; stop=False
        # Frontier x all current rules, both directions, is the attachment graph.
        for oi,o in enumerate(frontier):
            if stop:break
            for ii,i in enumerate(rules):
                if stop:break
                for aa,bb in ((o,i),(i,o)):
                    for path in m.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):
                        c=ts.critical_pair(aa,bb,oi,ii,path)
                        if c is None:continue
                        c=ts.interreduce(c,rules)
                        if c.lhs==c.rhs:continue
                        props.append((ts.target_score(c),m.term_size(c.lhs)+m.term_size(c.rhs),c)); proposed+=1
                        if proposed>=1024:stop=True;break
                    if stop:break
        props.sort(key=lambda x:(x[0],x[1]))
        nxt=[]; added=0
        for _,_,q in props:
            if ts.add_clause(q): ts.superpositions+=1; nxt.append(q); added+=1
            tq=ts.target_proof(ts.rules())
            if tq is not None: found=tq; break
            if added>=96:break
        trace.append({'generation':gen,'proposed':proposed,'added':added,'clauses':len(ts.clauses),'best_score':props[0][0] if props else None})
        frontier=nxt
        if not frontier:break
    if found is None: found=ts.collapse_proof() or ts.target_proof(ts.rules())
    replay=False; proof_nodes=None
    if found is not None:
        q=te.inline_recipe(found)
        if (q.lhs,q.rhs)==(target[1],target[0]):q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
        if (q.lhs,q.rhs)==target[:2]:
            nn,rr=ts.compile(q); replay=m.replay_dag(source,nn,rr,maximum_term_size=320,maximum_nodes=70000); proof_nodes=len(nn)
    result={'id':row['id'],'goal':a.goal,'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'census':census,'replayed':replayed,'projected':projected,'interfaces':len(uniq),'attachment_trace':trace,'found':found is not None,'replay':replay,'proof_nodes':proof_nodes}
    print('STRUCTURED_LAWBOOK_ATTACHMENT '+json.dumps(result,sort_keys=True),flush=True)
    if a.goal=='idempotence' and not replay:raise SystemExit(2)
if __name__=='__main__':main()

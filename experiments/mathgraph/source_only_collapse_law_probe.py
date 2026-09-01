#!/usr/bin/env python3
import argparse, importlib.util, json, time

def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); a=ap.parse_args()
    m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); neutral=m.parse_equation('x = x')
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})
    def setup(goal,sec):
        lim=dict(base);lim['seconds']=sec;e=m.TargetGroundedRefutation(source,goal,time.monotonic()+sec,lim);return e,e.search
    def canon(lhs,rhs):
        names={}
        def f(t):
            if t[0]=='var':
                if t[1] not in names:names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',f(t[1]),f(t[2]))
        return f(lhs),f(rhs),tuple(dict.fromkeys(names.values()))
    def skey(s,q):return (m.term_size(q.lhs)+m.term_size(q.rhs),str(s.alpha_signature(q.lhs,q.rhs)),m.render_term(q.lhs),m.render_term(q.rhs))
    t0=time.monotonic();e,s=setup(neutral,20.0);pre=[]
    for gen in range(1,4):
        rules=s.rules();snap=list(rules);props=[];proposed=0;stop=False
        for oi,o in enumerate(snap):
            if stop:break
            for ii,i in enumerate(snap):
                if stop:break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None:continue
                    c=s.interreduce(c,rules);props.append(c);proposed+=1
                    if proposed>=512:stop=True;break
        props.sort(key=lambda q:skey(s,q));added=0
        for q in props:
            if s.add_clause(q):s.superpositions+=1;added+=1
            if added>=64:break
        pre.append({'generation':gen,'proposed':proposed,'added':added,'clauses':len(s.clauses)})
    rules=s.rules();seen=set();census=replayed=projected=0;collapse=[];alllaws=[];s.deadline=time.monotonic()+12.0
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired() or census>=256:break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None:continue
                c=s.interreduce(c,rules);names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names):continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen:continue
                seen.add(key);census+=1
                ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=320,maximum_nodes=70000):continue
                replayed+=1;raw=canon(c.lhs,c.rhs);pe,ps=setup(raw,2.0);pn,pr=ps.compile(c)
                if not m.replay_dag(source,pn,pr,maximum_term_size=320,maximum_nodes=70000):continue
                projected+=1;ep=(pn[pr].lhs,pn[pr].rhs);act=canon(ep[0],ep[1]);lhs,rhs=act[0],act[1]
                rec={'lhs':m.render_term(lhs),'rhs':m.render_term(rhs),'vars_lhs':sorted(m.term_variables(lhs)),'vars_rhs':sorted(m.term_variables(rhs)),'proof_nodes':len(pn),'recipe':c}
                alllaws.append({k:v for k,v in rec.items() if k!='recipe'})
                lv=m.term_variables(lhs);rv=m.term_variables(rhs)
                collapses=(lhs[0]=='var' and lhs[1] not in rv) or (rhs[0]=='var' and rhs[1] not in lv)
                if collapses: collapse.append(rec)
            if s.expired() or census>=256:break
        if s.expired() or census>=256:break
    # Attachment test: any discovered collapse law is promoted as a proof-bearing clause and asked to close the actual target.
    closed=False;proof_nodes=None;chosen=None
    for rec in sorted(collapse,key=lambda z:(z['proof_nodes'],z['lhs'],z['rhs'])):
        te,ts=setup(target,3.0);ts.add_clause(rec['recipe']);q=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve()
        if q is None:continue
        q=te.inline_recipe(q)
        if (q.lhs,q.rhs)==(target[1],target[0]):q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
        if (q.lhs,q.rhs)!=target[:2]:continue
        nn,rr=ts.compile(q)
        if m.replay_dag(source,nn,rr,maximum_term_size=320,maximum_nodes=70000):
            closed=True;proof_nodes=len(nn);chosen={k:v for k,v in rec.items() if k!='recipe'};break
    out={'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'census':census,'replayed':replayed,'projected':projected,'collapse_laws':len(collapse),'closed_actual_target':closed,'proof_nodes':proof_nodes,'chosen':chosen,'sample_laws':alllaws[:24]}
    print('SOURCE_ONLY_COLLAPSE_LAW '+json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__':main()

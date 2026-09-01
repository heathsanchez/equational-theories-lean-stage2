#!/usr/bin/env python3
import argparse, importlib.util, json, time

def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); ap.add_argument('--solve-seconds',type=float,default=180.0); a=ap.parse_args()
    m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    base=dict(m.COMPACT_SUPERPOSITION_PROBE);base.update({'maximum_term_size':85,'maximum_replay_term_size':360,'maximum_depth':14,'maximum_rules':1024,'maximum_rounds':192,'new_clauses_per_round':96,'maximum_clauses':18000,'normalization_steps':384,'maximum_proof_nodes':90000})
    def setup(sec):
        lim=dict(base);lim['seconds']=sec;e=m.TargetGroundedRefutation(source,target,time.monotonic()+sec,lim);return e,e.search
    def canon(lhs,rhs):
        names={}
        def f(t):
            if t[0]=='var':
                if t[1] not in names:names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',f(t[1]),f(t[2]))
        return f(lhs),f(rhs),tuple(dict.fromkeys(names.values()))
    t0=time.monotonic();e,s=setup(20.0);pre=[]
    for gen in range(1,4):
        rules=s.rules();snap=list(rules);props=[];proposed=0;stop=False
        for oi,o in enumerate(snap):
            if stop:break
            for ii,i in enumerate(snap):
                if stop:break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None:continue
                    c=s.interreduce(c,rules);props.append((s.target_score(c),c));proposed+=1
                    if proposed>=512:stop=True;break
        props.sort(key=lambda x:x[0]);added=0
        for _,q in props:
            if s.add_clause(q):s.superpositions+=1;added+=1
            if added>=64:break
        pre.append({'generation':gen,'proposed':proposed,'added':added,'clauses':len(s.clauses)})
    rules=s.rules();seen=set();unary=[];census=replayed=0;s.deadline=time.monotonic()+12.0
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired() or census>=176:break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None:continue
                c=s.interreduce(c,rules);names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names):continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen:continue
                seen.add(key);census+=1
                ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=360,maximum_nodes=90000):continue
                replayed+=1;act=canon(c.lhs,c.rhs)
                if act[2]==('x',): unary.append((s.target_score(c),m.term_size(c.lhs)+m.term_size(c.rhs),len(ns),c,m.render_term(act[0]),m.render_term(act[1])))
            if s.expired() or census>=176:break
        if s.expired() or census>=176:break
    unary.sort(key=lambda z:(z[0],z[1],z[2],z[4],z[5]));uniq=[];keys=set()
    for rec in unary:
        k=(rec[4],rec[5])
        if k in keys:continue
        keys.add(k);uniq.append(rec)
    te,ts=setup(a.solve_seconds);added=0
    for rec in uniq[:64]:
        if ts.add_clause(rec[3]):added+=1
    q=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve();replay=False;proof_nodes=None;certificate_bytes=None
    if q is not None:
        q=te.inline_recipe(q)
        if (q.lhs,q.rhs)==(target[1],target[0]):q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
        if (q.lhs,q.rhs)==target[:2]:
            nn,rr=ts.compile(q);replay=m.replay_dag(source,nn,rr,maximum_term_size=360,maximum_nodes=90000);proof_nodes=len(nn)
            if replay:
                code,pnodes=m.make_dag_certificate(target,nn,rr);certificate_bytes=len(code.encode())
    sample=[{'lhs':z[4],'rhs':z[5],'score':z[0],'proof_nodes':z[2]} for z in uniq[:12]]
    print('TARGET_GUIDED_UNARY_PROMOTION '+json.dumps({'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'census':census,'replayed':replayed,'unary':len(uniq),'added':added,'sample':sample,'found':q is not None,'replay':replay,'proof_nodes':proof_nodes,'certificate_bytes':certificate_bytes,'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses)},sort_keys=True),flush=True)
    if replay: raise SystemExit(0)
if __name__=='__main__':main()

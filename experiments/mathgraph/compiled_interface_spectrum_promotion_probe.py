#!/usr/bin/env python3
import argparse, importlib.util, json, time

def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True)
    a=ap.parse_args(); m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})
    def setup(goal,seconds):
        lim=dict(base);lim['seconds']=seconds;e=m.TargetGroundedRefutation(source,goal,time.monotonic()+seconds,lim);return e,e.search
    def canon(lhs,rhs):
        names={}
        def f(t):
            if t[0]=='var':
                if t[1] not in names:names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',f(t[1]),f(t[2]))
        return f(lhs),f(rhs),tuple(dict.fromkeys(names.values()))
    def orient(q,r):return q if not r else m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
    e,s=setup(target,30.0)
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
    objects=sorted(s.clauses,key=s.target_score)[:224];probes=objects[:40]
    def alpha(q):return str(s.alpha_signature(q.lhs,q.rhs))
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
    old={future(q) for q in objects}; seen=set(); spectrum={}; census=replayed=projected=0; chosen=None; chosen_info=None
    x=('var','x'); xx=('op',x,x)
    s.deadline=time.monotonic()+55.0;rules=s.rules()
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                if s.expired():break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None:continue
                c=s.interreduce(c,rules);names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names):continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen:continue
                seen.add(key);census+=1
                ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=320,maximum_nodes=70000):continue
                replayed+=1;fs=future(c)
                if fs in old:continue
                raw=canon(c.lhs,c.rhs);pe,ps=setup(raw,5.0);pn,pr=ps.compile(c)
                if not m.replay_dag(source,pn,pr,maximum_term_size=320,maximum_nodes=70000):continue
                projected+=1;ep=(pn[pr].lhs,pn[pr].rhs);act=canon(ep[0],ep[1])
                if act[2]!=('x',):continue
                k=(m.render_term(act[0]),m.render_term(act[1]))
                rec={'lhs':k[0],'rhs':k[1],'future_size':len(fs),'proof_nodes':len(pn),'raw_lhs':m.render_term(c.lhs),'raw_rhs':m.render_term(c.rhs)}
                prev=spectrum.get(k)
                if prev is None or (rec['proof_nodes'],-rec['future_size'])<(prev['proof_nodes'],-prev['future_size']):spectrum[k]=rec
                if chosen is None and ((act[0],act[1])==(x,xx) or (act[0],act[1])==(xx,x)):
                    chosen=c; chosen_info=rec
            if s.expired():break
        if s.expired():break
    vals=sorted(spectrum.values(),key=lambda r:(m.term_size(m.parse_equation(r['lhs']+' = '+r['rhs'])[0])+m.term_size(m.parse_equation(r['lhs']+' = '+r['rhs'])[1]),-r['future_size'],r['lhs'],r['rhs']))[:40]
    target_rec={'found':False,'replay':False}
    if chosen is not None:
        te,ts=setup(target,300.0); added=ts.add_clause(chosen)
        tq=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve()
        target_rec={'found':tq is not None,'replay':False,'added':bool(added),'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses)}
        if tq is not None:
            q=te.inline_recipe(tq)
            if (q.lhs,q.rhs)==(target[1],target[0]): q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
            if (q.lhs,q.rhs)==target[:2]:
                nn,rr=ts.compile(q); target_rec['replay']=m.replay_dag(source,nn,rr,maximum_term_size=320,maximum_nodes=70000); target_rec['proof_nodes']=len(nn); target_rec['proof_cost']=q.cost
    print('SPECTRUM_PROMOTION '+json.dumps({'id':row['id'],'census':census,'replayed':replayed,'projected':projected,'idempotence':chosen_info,'interfaces':vals,'target':target_rec},sort_keys=True),flush=True)
if __name__=='__main__':main()

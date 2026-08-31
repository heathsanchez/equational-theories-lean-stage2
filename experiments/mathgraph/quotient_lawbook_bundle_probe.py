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
    def orient(q,r): return q if not r else m.Recipe(q.rhs,q.lhs,'symmetry',(q,))

    e,s=setup(target,1200.0)
    pre_trace=[]
    for _ in range(3):
        rules=s.rules(); snap=list(rules); props=[]; proposed=0; stop=False
        for oi,o in enumerate(snap):
            if stop: break
            for ii,i in enumerate(snap):
                if stop: break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    c=s.interreduce(c,rules); props.append((s.target_score(c),c)); proposed+=1
                    if proposed>=512: stop=True; break
        props.sort(key=lambda x:x[0]); added=0
        for _,q in props:
            if s.add_clause(q): s.superpositions+=1; added+=1
            if added>=64: break
        pre_trace.append({'proposed':proposed,'added':added,'clauses':len(s.clauses)})

    objects=sorted(s.clauses,key=s.target_score)[:224]; probes=objects[:40]
    def alpha(q): return str(s.alpha_signature(q.lhs,q.rhs))
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
                            if c is not None: out.add(alpha(c))
        return frozenset(out)
    old={future(q) for q in objects}; seen=set(); spectrum={}; recipes={}; census=replayed=projected=0
    rules=s.rules(); stop=False
    for oi,o in enumerate(rules):
        if stop: break
        for ii,i in enumerate(rules):
            if stop: break
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None: continue
                c=s.interreduce(c,rules); names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names): continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen: continue
                seen.add(key); census+=1
                ns,r=s.compile(c)
                if m.replay_dag(source,ns,r,maximum_term_size=320,maximum_nodes=70000):
                    replayed+=1; fs=future(c)
                    if fs not in old:
                        raw=canon(c.lhs,c.rhs); pe,ps=setup(raw,30.0); pn,pr=ps.compile(c)
                        if m.replay_dag(source,pn,pr,maximum_term_size=320,maximum_nodes=70000):
                            projected+=1; ep=(pn[pr].lhs,pn[pr].rhs); act=canon(ep[0],ep[1])
                            if act[2]==('x',):
                                k=(m.render_term(act[0]),m.render_term(act[1]))
                                rec={'lhs':k[0],'rhs':k[1],'future_size':len(fs),'proof_nodes':len(pn),'raw_lhs':m.render_term(c.lhs),'raw_rhs':m.render_term(c.rhs)}
                                prev=spectrum.get(k)
                                if prev is None or (rec['proof_nodes'],-rec['future_size'])<(prev['proof_nodes'],-prev['future_size']):
                                    spectrum[k]=rec; recipes[k]=c
                if census>=256: stop=True; break

    def rank(k):
        l,r=m.parse_equation(k[0]+' = '+k[1]); rec=spectrum[k]
        return (m.term_size(l)+m.term_size(r),-rec['future_size'],rec['proof_nodes'],k[0],k[1])
    ordered=sorted(spectrum,key=rank)
    bundles=[]
    for n in (1,2,4,8):
        keys=ordered[:n]; te,ts=setup(target,180.0); added=[]
        for k in keys: added.append(bool(ts.add_clause(recipes[k])))
        tq=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve()
        out={'k':n,'laws':[spectrum[k] for k in keys],'added':added,'found':tq is not None,'replay':False,'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses)}
        if tq is not None:
            q=te.inline_recipe(tq)
            if (q.lhs,q.rhs)==(target[1],target[0]): q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
            if (q.lhs,q.rhs)==target[:2]:
                nn,rr=ts.compile(q); out['replay']=m.replay_dag(source,nn,rr,maximum_term_size=320,maximum_nodes=70000); out['proof_nodes']=len(nn); out['proof_cost']=q.cost
        bundles.append(out)
        if out['replay']: break
    print('QUOTIENT_LAWBOOK '+json.dumps({'id':row['id'],'pre_trace':pre_trace,'census':census,'replayed':replayed,'projected':projected,'interfaces':len(spectrum),'bundles':bundles},sort_keys=True),flush=True)
if __name__=='__main__': main()

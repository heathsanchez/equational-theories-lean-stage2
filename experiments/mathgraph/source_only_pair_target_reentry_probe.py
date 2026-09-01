#!/usr/bin/env python3
import argparse, importlib.util, json, time


def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); ap.add_argument('--solve-seconds',type=float,default=90.0); a=ap.parse_args()
    m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); neutral=m.parse_equation('x = x')
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':90,'maximum_replay_term_size':400,'maximum_depth':14,'maximum_rules':1024,'maximum_rounds':192,'new_clauses_per_round':96,'maximum_clauses':18000,'normalization_steps':384,'maximum_proof_nodes':90000})
    def setup(goal,sec):
        lim=dict(base); lim['seconds']=sec; e=m.TargetGroundedRefutation(source,goal,time.monotonic()+sec,lim); return e,e.search
    def arity(q): return len(m.term_variables(q.lhs)|m.term_variables(q.rhs))
    def orient(q,r): return q if not r else m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
    t0=time.monotonic(); de,ds=setup(neutral,30.0)
    def sig(q): return str(ds.alpha_signature(q.lhs,q.rhs))
    def skey(q): return (m.term_size(q.lhs)+m.term_size(q.rhs),arity(q),sig(q),m.render_term(q.lhs),m.render_term(q.rhs))
    pre=[]
    # SOURCE-ONLY developmental construction. The real target is not consulted here.
    for gen in range(1,4):
        rules=ds.rules(); snap=list(rules); props=[]; proposed=0; stop=False
        for oi,o in enumerate(snap):
            if stop: break
            for ii,i in enumerate(snap):
                if stop: break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=14,include_root=True):
                    c=ds.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    c=ds.interreduce(c,rules); props.append(c); proposed+=1
                    if proposed>=1024: stop=True; break
        buckets={1:[],2:[],3:[],4:[]}
        for q in props: buckets[min(4,max(1,arity(q)))].append(q)
        for xs in buckets.values(): xs.sort(key=skey)
        selected=[]; quota={1:20,2:24,3:24,4:12}
        for aa in (1,2,3,4): selected.extend(buckets[aa][:quota[aa]])
        if len(selected)<80:
            used={id(q) for q in selected}; selected.extend(sorted((q for q in props if id(q) not in used),key=skey)[:80-len(selected)])
        added=0; aaadd={}
        for q in selected:
            if ds.add_clause(q):
                ds.superpositions+=1; added+=1; aa=min(4,max(1,arity(q))); aaadd[aa]=aaadd.get(aa,0)+1
        pre.append({'generation':gen,'proposed':proposed,'added':added,'added_arity':aaadd,'clauses':len(ds.clauses)})

    rules=ds.rules(); partners=sorted(rules,key=skey)[:12]; raw=[]; seen=set()
    for q in rules:
        k=(sig(q),q.lhs,q.rhs)
        if q.lhs!=q.rhs and k not in seen: seen.add(k); raw.append(q)
    buckets={1:[],2:[],3:[],4:[]}
    for q in raw: buckets[min(4,max(1,arity(q)))].append(q)
    for xs in buckets.values(): xs.sort(key=skey)
    cand=[]
    for aa,n in ((1,8),(2,8),(3,8),(4,8)): cand.extend(buckets[aa][:n])
    cand=sorted(cand,key=skey)[:32]

    def children(q,ps,cap=20):
        out=[]; ss=set(); calls=0
        for pi,p in enumerate(ps):
            for a0,b0 in ((q,p),(p,q)):
                for ar in (False,True):
                    aa=orient(a0,ar)
                    for br in (False,True):
                        bb=orient(b0,br)
                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=8,include_root=True):
                            c=ds.critical_pair(aa,bb,0,pi,path)
                            if c is None: continue
                            calls+=1; c=ds.interreduce(c,rules)
                            if c.lhs==c.rhs: continue
                            k=sig(c)
                            if k in ss: continue
                            ss.add(k); out.append(c)
        out.sort(key=skey); return out[:cap],calls

    indiv=[]; individual_calls=0
    for q in cand:
        xs,n=children(q,partners); individual_calls+=n; indiv.append({sig(x) for x in xs})

    # Generate pair-only consequences without target information, and certify each against source.
    certified=[]; pair_calls=0; pair_count=0; seen_endpoint=set()
    for i in range(len(cand)):
        for j in range(i+1,len(cand)):
            out=[]; ss=set()
            for a0,b0 in ((cand[i],cand[j]),(cand[j],cand[i])):
                for ar in (False,True):
                    aa=orient(a0,ar)
                    for br in (False,True):
                        bb=orient(b0,br)
                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=9,include_root=True):
                            c=ds.critical_pair(aa,bb,i,j,path)
                            if c is None: continue
                            pair_calls+=1; c=ds.interreduce(c,rules)
                            if c.lhs==c.rhs: continue
                            k=sig(c)
                            if k in ss: continue
                            ss.add(k); out.append(c)
            baseline=indiv[i]|indiv[j]; novel=[q for q in out if sig(q) not in baseline]
            if not novel: continue
            pair_count+=1; novel.sort(key=skey)
            for q in novel[:8]:
                ns,r=ds.compile(q)
                if not m.replay_dag(source,ns,r,maximum_term_size=400,maximum_nodes=90000): continue
                ep=ns[r]; ek=(ds.alpha_signature(ep.lhs,ep.rhs),ep.lhs,ep.rhs)
                if ek in seen_endpoint: continue
                seen_endpoint.add(ek); certified.append((q,len(ns),i,j,len(novel),arity(ep)))

    # Only now reveal the real target: target may rank already-certified relational consequences,
    # but it did not influence their discovery, pair selection, or certification.
    te,ts=setup(target,a.solve_seconds)
    ranked=[]
    for q,pn,i,j,nov,aa in certified:
        ranked.append((ts.target_score(q),m.term_size(q.lhs)+m.term_size(q.rhs),pn,i,j,nov,aa,q))
    ranked.sort(key=lambda z:(z[0],z[1],z[2],z[3],z[4]))
    added=0
    for rec in ranked[:96]:
        if ts.add_clause(rec[-1]): added+=1
    q=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve(); replay=False; proof_nodes=None; certificate_bytes=None
    if q is not None:
        q=te.inline_recipe(q)
        if (q.lhs,q.rhs)==(target[1],target[0]): q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
        if (q.lhs,q.rhs)==target[:2]:
            nn,rr=ts.compile(q); replay=m.replay_dag(source,nn,rr,maximum_term_size=400,maximum_nodes=90000); proof_nodes=len(nn)
            if replay:
                code,_=m.make_dag_certificate(target,nn,rr); certificate_bytes=len(code.encode())
    sample=[{'score':z[0],'size':z[1],'proof_nodes':z[2],'pair':[z[3],z[4]],'pair_novelty':z[5],'arity':z[6],'lhs':m.render_term(z[-1].lhs),'rhs':m.render_term(z[-1].rhs)} for z in ranked[:12]]
    out={'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'candidates':len(cand),'partners':len(partners),'individual_calls':individual_calls,'pair_calls':pair_calls,'relational_pairs':pair_count,'certified_pair_only':len(certified),'added':added,'sample':sample,'found':q is not None,'replay':replay,'proof_nodes':proof_nodes,'certificate_bytes':certificate_bytes,'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses),'target_revealed_after_pair_certification':True}
    print('SOURCE_ONLY_PAIR_TARGET_REENTRY '+json.dumps(out,sort_keys=True),flush=True)
    if replay: raise SystemExit(0)

if __name__=='__main__': main()

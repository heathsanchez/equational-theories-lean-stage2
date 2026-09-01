#!/usr/bin/env python3
import argparse, importlib.util, json, time


def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); a=ap.parse_args()
    m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); neutral=m.parse_equation('x = x')
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':90,'maximum_replay_term_size':360,'maximum_depth':14,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':80,'maximum_clauses':18000,'normalization_steps':320,'maximum_proof_nodes':90000,'seconds':30.0})
    e=m.TargetGroundedRefutation(source,neutral,time.monotonic()+30.0,base); s=e.search
    def arity(q): return len(m.term_variables(q.lhs)|m.term_variables(q.rhs))
    def sig(q): return str(s.alpha_signature(q.lhs,q.rhs))
    def skey(q): return (m.term_size(q.lhs)+m.term_size(q.rhs),arity(q),sig(q),m.render_term(q.lhs),m.render_term(q.rhs))
    def orient(q,r): return q if not r else m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
    def shared_pair_arity(q1,q2):
        return len(m.term_variables(q1.lhs)|m.term_variables(q1.rhs)|m.term_variables(q2.lhs)|m.term_variables(q2.rhs))

    t0=time.monotonic(); pre=[]
    for gen in range(1,4):
        rules=s.rules(); snap=list(rules); props=[]; proposed=0; stop=False
        for oi,o in enumerate(snap):
            if stop: break
            for ii,i in enumerate(snap):
                if stop: break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=14,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    c=s.interreduce(c,rules); props.append(c); proposed+=1
                    if proposed>=1024: stop=True; break
        buckets={1:[],2:[],3:[],4:[]}
        for q in props: buckets[min(4,max(1,arity(q)))].append(q)
        for xs in buckets.values(): xs.sort(key=skey)
        quota={1:20,2:24,3:24,4:12}; selected=[]
        for aa in (1,2,3,4): selected.extend(buckets[aa][:quota[aa]])
        if len(selected)<80:
            used={id(q) for q in selected}; rest=sorted((q for q in props if id(q) not in used),key=skey); selected.extend(rest[:80-len(selected)])
        added=0; aaadd={}
        for q in selected:
            if s.add_clause(q):
                s.superpositions+=1; added+=1; aa=min(4,max(1,arity(q))); aaadd[aa]=aaadd.get(aa,0)+1
        pre.append({'generation':gen,'proposed':proposed,'added':added,'added_arity':aaadd,'clauses':len(s.clauses)})

    rules=s.rules(); partners=sorted(rules,key=skey)[:12]
    # Source-only candidate selection: preserve a fixed number per arity bucket.
    raw=[]; seen=set()
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
                            c=s.critical_pair(aa,bb,0,pi,path)
                            if c is None: continue
                            calls+=1; c=s.interreduce(c,rules)
                            if c.lhs==c.rhs: continue
                            k=sig(c)
                            if k in ss: continue
                            ss.add(k); out.append(c)
        out.sort(key=skey); return out[:cap],calls

    indiv=[]; individual_calls=0
    for q in cand:
        xs,n=children(q,partners); individual_calls+=n; indiv.append({sig(x) for x in xs})

    records=[]; pair_calls=0; endpoint_arity={}; replayed_novel=0
    for i in range(len(cand)):
        for j in range(i+1,len(cand)):
            out=[]; ss=set()
            for a0,b0 in ((cand[i],cand[j]),(cand[j],cand[i])):
                for ar in (False,True):
                    aa=orient(a0,ar)
                    for br in (False,True):
                        bb=orient(b0,br)
                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=9,include_root=True):
                            c=s.critical_pair(aa,bb,i,j,path)
                            if c is None: continue
                            pair_calls+=1; c=s.interreduce(c,rules)
                            if c.lhs==c.rhs: continue
                            k=sig(c)
                            if k in ss: continue
                            ss.add(k); out.append(c)
            baseline=indiv[i]|indiv[j]; novel=[q for q in out if sig(q) not in baseline]
            if not novel: continue
            novel.sort(key=skey); cert=[]
            for q in novel[:4]:
                ns,r=s.compile(q)
                ok=m.replay_dag(source,ns,r,maximum_term_size=360,maximum_nodes=90000)
                if ok:
                    replayed_novel+=1; ep=ns[r]; aa=arity(ep); endpoint_arity[aa]=endpoint_arity.get(aa,0)+1
                    cert.append({'lhs':m.render_term(ep.lhs),'rhs':m.render_term(ep.rhs),'arity':aa,'proof_nodes':len(ns)})
            records.append({'i':i,'j':j,'novelty':len(novel),'joint_arity':shared_pair_arity(cand[i],cand[j]),'a_arity':arity(cand[i]),'b_arity':arity(cand[j]),'a':m.render_term(cand[i].lhs)+' = '+m.render_term(cand[i].rhs),'b':m.render_term(cand[j].lhs)+' = '+m.render_term(cand[j].rhs),'certified_novel':cert})
    records.sort(key=lambda z:(-z['novelty'],-z['joint_arity'],z['i'],z['j']))
    out={'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'candidates':len(cand),'candidate_arities':{str(k):sum(1 for q in cand if min(4,max(1,arity(q)))==k) for k in (1,2,3,4)},'partners':len(partners),'individual_calls':individual_calls,'pair_calls':pair_calls,'relational_pairs':len(records),'max_pair_only_novelty':max([r['novelty'] for r in records],default=0),'max_joint_arity':max([r['joint_arity'] for r in records],default=0),'replayed_pair_only_children':replayed_novel,'pair_only_endpoint_arity':endpoint_arity,'top_pairs':records[:8]}
    print('SOURCE_ONLY_PAIR_INTERFACE_REFINEMENT '+json.dumps(out,sort_keys=True),flush=True)

if __name__=='__main__': main()

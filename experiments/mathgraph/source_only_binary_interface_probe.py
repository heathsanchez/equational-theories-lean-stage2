#!/usr/bin/env python3
import argparse, importlib.util, json, time


def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True); ap.add_argument('--certificate-dir',default='/tmp'); a=ap.parse_args()
    m=load(a.solver); row=json.load(open(a.row)); source=m.parse_equation(row['equation1']); neutral=m.parse_equation('x = x')
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':90,'maximum_replay_term_size':360,'maximum_depth':14,'maximum_rules':1024,'maximum_rounds':96,'new_clauses_per_round':80,'maximum_clauses':18000,'normalization_steps':320,'maximum_proof_nodes':90000,'seconds':25.0})
    e=m.TargetGroundedRefutation(source,neutral,time.monotonic()+25.0,base); s=e.search

    def canon(lhs,rhs):
        names={}
        def f(t):
            if t[0]=='var':
                if t[1] not in names: names[t[1]]=chr(ord('x')+len(names))
                return ('var',names[t[1]])
            return ('op',f(t[1]),f(t[2]))
        return f(lhs),f(rhs),tuple(dict.fromkeys(names.values()))

    def arity(q): return len(m.term_variables(q.lhs)|m.term_variables(q.rhs))
    def skey(q):
        return (m.term_size(q.lhs)+m.term_size(q.rhs),str(s.alpha_signature(q.lhs,q.rhs)),m.render_term(q.lhs),m.render_term(q.rhs))

    t0=time.monotonic(); pre=[]
    for gen in range(1,4):
        rules=s.rules(); snap=list(rules); props=[]; proposed=0; stop=False; proposed_arity={}
        for oi,o in enumerate(snap):
            if stop: break
            for ii,i in enumerate(snap):
                if stop: break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=14,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None: continue
                    c=s.interreduce(c,rules); props.append(c); proposed+=1
                    aa=min(4,arity(c)); proposed_arity[aa]=proposed_arity.get(aa,0)+1
                    if proposed>=1024: stop=True; break
        # Preserve distinctions the old scalar ordering erased: fixed arity buckets,
        # each internally ordered structurally. This is source-only and target-blind.
        buckets={1:[],2:[],3:[],4:[]}
        for q in props: buckets[min(4,max(1,arity(q)))].append(q)
        for xs in buckets.values(): xs.sort(key=skey)
        quota={1:20,2:24,3:24,4:12}; selected=[]
        for aa in (1,2,3,4): selected.extend(buckets[aa][:quota[aa]])
        if len(selected)<80:
            used={id(q) for q in selected}
            rest=sorted((q for q in props if id(q) not in used),key=skey)
            selected.extend(rest[:80-len(selected)])
        added=0; added_arity={}
        for q in selected:
            if s.add_clause(q):
                s.superpositions+=1; added+=1; aa=min(4,max(1,arity(q))); added_arity[aa]=added_arity.get(aa,0)+1
            if added>=80: break
        pre.append({'generation':gen,'proposed':proposed,'proposed_arity':proposed_arity,'added':added,'added_arity':added_arity,'clauses':len(s.clauses)})

    seen=set(); census=replayed=0; laws=[]; hits={}; s.deadline=time.monotonic()+18.0; rules=s.rules()
    wanted={
        ('(x ◇ y)','x'):'left_projection',
        ('x','(x ◇ y)'):'left_projection_symm',
        ('(x ◇ y)','y'):'right_projection',
        ('y','(x ◇ y)'):'right_projection_symm',
        ('(x ◇ y)','(y ◇ x)'):'commutativity',
    }
    endpoint_arity={}
    for oi,o in enumerate(rules):
        for ii,i in enumerate(rules):
            for path in m.nonvariable_positions(o.lhs,maximum_depth=14,include_root=True):
                if s.expired() or census>=768: break
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None: continue
                c=s.interreduce(c,rules); names=m.term_variables(c.lhs)|m.term_variables(c.rhs)
                if c.lhs==c.rhs or any(v.startswith('@') for v in names): continue
                key=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if key in seen: continue
                seen.add(key); census+=1
                ns,r=s.compile(c)
                if not m.replay_dag(source,ns,r,maximum_term_size=360,maximum_nodes=90000): continue
                replayed+=1
                ep=(ns[r].lhs,ns[r].rhs); act=canon(ep[0],ep[1]); aa=len(act[2]); endpoint_arity[aa]=endpoint_arity.get(aa,0)+1
                if aa!=2: continue
                rec={'lhs_t':act[0],'rhs_t':act[1],'lhs':m.render_term(act[0]),'rhs':m.render_term(act[1]),'proof_nodes':len(ns),'raw_lhs':m.render_term(c.lhs),'raw_rhs':m.render_term(c.rhs),'dag':ns,'root':r}
                laws.append(rec)
                tag=wanted.get((rec['lhs'],rec['rhs']))
                if tag and tag not in hits:
                    cert,nodes=m.make_dag_certificate(m.Equation(act[0],act[1]),ns,r)
                    p=f"{a.certificate_dir}/{tag}.lean"; open(p,'w').write(cert)
                    hits[tag]={'proof_nodes':len(ns),'certificate_nodes':nodes,'certificate':p}
            if s.expired() or census>=768: break
        if s.expired() or census>=768: break
    laws.sort(key=lambda r:(m.term_size(r['lhs_t'])+m.term_size(r['rhs_t']),r['proof_nodes'],r['lhs'],r['rhs']))
    out={'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'census':census,'replayed':replayed,'endpoint_arity':endpoint_arity,'binary_laws':len(laws),'hits':hits,'smallest':[{'lhs':r['lhs'],'rhs':r['rhs'],'proof_nodes':r['proof_nodes']} for r in laws[:24]]}
    print('SOURCE_ONLY_BINARY_INTERFACE '+json.dumps(out,sort_keys=True),flush=True)

if __name__=='__main__': main()

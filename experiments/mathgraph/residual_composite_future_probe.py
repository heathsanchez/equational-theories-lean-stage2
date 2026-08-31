#!/usr/bin/env python3
import argparse, importlib.util, json, time


def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path)
    m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--solver',required=True); ap.add_argument('--row',required=True)
    a=ap.parse_args(); m=load(a.solver); row=json.load(open(a.row))
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    base=dict(m.COMPACT_SUPERPOSITION_PROBE); base.update({'maximum_term_size':75,'maximum_replay_term_size':320,'maximum_depth':12,'maximum_rules':896,'maximum_rounds':96,'new_clauses_per_round':64,'maximum_clauses':14000,'normalization_steps':256,'maximum_proof_nodes':70000})
    def setup(goal,seconds):
        lim=dict(base); lim['seconds']=seconds; e=m.TargetGroundedRefutation(source,goal,time.monotonic()+seconds,lim); return e,e.search
    def orient(q,r): return q if not r else m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
    def exact(e,q):
        z=e.inline_recipe(q); return (z.lhs,z.rhs)==target[:2] or (z.lhs,z.rhs)==(target[1],target[0])
    def replay_target(e,s,q):
        q=e.inline_recipe(q)
        if (q.lhs,q.rhs)==(target[1],target[0]): q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
        if (q.lhs,q.rhs)!=target[:2]: return False,0
        nn,rr=s.compile(q); return m.replay_dag(source,nn,rr,maximum_term_size=320,maximum_nodes=70000),len(nn)

    e,s=setup(target,1200.0); pre=[]
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
        props.sort(key=lambda z:z[0]); added=0
        for _,q in props:
            if s.add_clause(q): s.superpositions+=1; added+=1
            if added>=64: break
        pre.append({'proposed':proposed,'added':added,'clauses':len(s.clauses)})

    rules=s.rules(); partners=sorted(rules,key=s.target_score)[:12]
    seen=set(); candidates=[]
    for oi,o in enumerate(rules):
        if len(candidates)>=96: break
        for ii,i in enumerate(rules):
            if len(candidates)>=96: break
            for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                c=s.critical_pair(o,i,oi,ii,path)
                if c is None: continue
                c=s.interreduce(c,rules)
                if c.lhs==c.rhs: continue
                k=(s.alpha_signature(c.lhs,c.rhs),c.lhs,c.rhs)
                if k in seen: continue
                seen.add(k); candidates.append(c)
                if len(candidates)>=96: break

    calls1=calls2=0; exact_child=None
    def children(q,depth,cap):
        nonlocal calls1,calls2,exact_child
        out=[]; ss=set()
        for pi,p in enumerate(partners):
            for a0,b0 in ((q,p),(p,q)):
                for ar in (False,True):
                    aa=orient(a0,ar)
                    for br in (False,True):
                        bb=orient(b0,br)
                        for path in m.nonvariable_positions(aa.lhs,maximum_depth=6,include_root=True):
                            c=s.critical_pair(aa,bb,0,pi,path)
                            if c is None: continue
                            if depth==1: calls1+=1
                            else: calls2+=1
                            c=s.interreduce(c,rules)
                            sig=str(s.alpha_signature(c.lhs,c.rhs))
                            if sig in ss: continue
                            ss.add(sig); out.append(c)
                            if exact(e,c): exact_child=c; return out
        out.sort(key=s.target_score)
        return out[:cap]

    records=[]; buckets={}
    for idx,q in enumerate(candidates):
        c1=children(q,1,8)
        if exact_child is not None: break
        sig1=tuple(sorted(str(s.alpha_signature(x.lhs,x.rhs)) for x in c1))
        sig2set=set()
        for x in c1:
            for y in children(x,2,8):
                sig2set.add(str(s.alpha_signature(y.lhs,y.rhs)))
                if exact_child is not None: break
            if exact_child is not None: break
        sig2=tuple(sorted(sig2set))
        rec={'index':idx,'candidate':q,'sig1':sig1,'sig2':sig2,'score':s.target_score(q)}
        records.append(rec); buckets.setdefault(sig1,[]).append(rec)
        if exact_child is not None: break

    alias_buckets=[]; distinguished=[]
    for sig1,group in buckets.items():
        if len(group)<2: continue
        variants={g['sig2'] for g in group}
        if len(variants)<2: continue
        alias_buckets.append({'size':len(group),'depth2_variants':len(variants)})
        reps={}
        for g in group:
            old=reps.get(g['sig2'])
            if old is None or g['score']<old['score']: reps[g['sig2']]=g
        distinguished.extend(reps.values())
    distinguished.sort(key=lambda g:(g['score'],g['index']))

    result={'id':row['id'],'pre_trace':pre,'candidates':len(candidates),'partners':len(partners),'calls_depth1':calls1,'calls_depth2':calls2,'one_step_alias_buckets':len(alias_buckets),'max_alias_bucket':max([x['size'] for x in alias_buckets],default=0),'depth2_distinguished':len(distinguished),'exact_child':exact_child is not None,'exact_child_replay':False,'target':{'found':False,'replay':False}}
    if exact_child is not None:
        ok,n=replay_target(e,s,exact_child); result['exact_child_replay']=ok; result['exact_child_nodes']=n
    if exact_child is None and distinguished:
        chosen=[g['candidate'] for g in distinguished[:16]]
        te,ts=setup(target,360.0); added=[bool(ts.add_clause(q)) for q in chosen]
        tq=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve()
        out={'found':tq is not None,'replay':False,'selected':len(chosen),'added':sum(added),'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses)}
        if tq is not None:
            ok,n=replay_target(te,ts,tq); out['replay']=ok; out['proof_nodes']=n
        result['target']=out
    print('RESIDUAL_COMPOSITE_FUTURE '+json.dumps(result,sort_keys=True),flush=True)


if __name__=='__main__': main()

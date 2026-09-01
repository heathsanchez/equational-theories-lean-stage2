#!/usr/bin/env python3
import argparse, importlib.util, json, time

def load(path):
    spec=importlib.util.spec_from_file_location('mgsolver',path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--solver',required=True);ap.add_argument('--row',required=True);ap.add_argument('--solve-seconds',type=float,default=90.0);a=ap.parse_args()
    m=load(a.solver);row=json.load(open(a.row));source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
    base=dict(m.COMPACT_SUPERPOSITION_PROBE);base.update({'maximum_term_size':90,'maximum_replay_term_size':380,'maximum_depth':14,'maximum_rules':1200,'maximum_rounds':192,'new_clauses_per_round':96,'maximum_clauses':20000,'normalization_steps':384,'maximum_proof_nodes':100000})
    def setup(sec):
        lim=dict(base);lim['seconds']=sec;e=m.TargetGroundedRefutation(source,target,time.monotonic()+sec,lim);return e,e.search
    t0=time.monotonic();e,s=setup(30.0);pre=[];generated=[]
    for gen in range(1,4):
        rules=s.rules();snap=list(rules);props=[];proposed=0;stop=False
        for oi,o in enumerate(snap):
            if stop:break
            for ii,i in enumerate(snap):
                if stop:break
                for path in m.nonvariable_positions(o.lhs,maximum_depth=12,include_root=True):
                    c=s.critical_pair(o,i,oi,ii,path)
                    if c is None:continue
                    c=s.interreduce(c,rules)
                    if c.lhs==c.rhs:continue
                    props.append((s.target_score(c),m.term_size(c.lhs)+m.term_size(c.rhs),c));proposed+=1
                    if proposed>=768:stop=True;break
        props.sort(key=lambda z:(z[0],z[1]));added=[]
        for _,_,q in props:
            if s.add_clause(q):s.superpositions+=1;added.append(q);generated.append(q)
            if len(added)>=96:break
        pre.append({'generation':gen,'proposed':proposed,'added':len(added),'clauses':len(s.clauses),'best_score':props[0][0] if props else None})
    # Replay certify generated clauses and deduplicate alpha-equivalent forms.
    certified=[];seen=set()
    for q in generated:
        k=s.alpha_signature(q.lhs,q.rhs)
        if k in seen:continue
        ns,r=s.compile(q)
        if not m.replay_dag(source,ns,r,maximum_term_size=380,maximum_nodes=100000):continue
        seen.add(k);certified.append((s.target_score(q),m.term_size(q.lhs)+m.term_size(q.rhs),len(ns),q))
    certified.sort(key=lambda z:(z[0],z[1],z[2]))
    te,ts=setup(a.solve_seconds);added=0
    for _,_,_,q in certified[:192]:
        if ts.add_clause(q):added+=1
    found=ts.collapse_proof() or ts.target_proof(ts.rules()) or ts.solve();replay=False;proof_nodes=None;cert_bytes=None
    if found is not None:
        q=te.inline_recipe(found)
        if (q.lhs,q.rhs)==(target[1],target[0]):q=m.Recipe(q.rhs,q.lhs,'symmetry',(q,))
        if (q.lhs,q.rhs)==target[:2]:
            nn,rr=ts.compile(q);replay=m.replay_dag(source,nn,rr,maximum_term_size=380,maximum_nodes=100000);proof_nodes=len(nn)
            if replay:
                code,_=m.make_dag_certificate(target,nn,rr);cert_bytes=len(code.encode())
    sample=[{'score':z[0],'size':z[1],'proof_nodes':z[2],'lhs':m.render_term(z[3].lhs),'rhs':m.render_term(z[3].rhs)} for z in certified[:12]]
    print('GENERATED_WORLD_PROMOTION '+json.dumps({'id':row['id'],'elapsed':round(time.monotonic()-t0,4),'pre_trace':pre,'generated':len(generated),'certified':len(certified),'added':added,'sample':sample,'found':found is not None,'replay':replay,'proof_nodes':proof_nodes,'certificate_bytes':cert_bytes,'rounds':ts.rounds,'superpositions':ts.superpositions,'clauses':len(ts.clauses)},sort_keys=True),flush=True)
if __name__=='__main__':main()

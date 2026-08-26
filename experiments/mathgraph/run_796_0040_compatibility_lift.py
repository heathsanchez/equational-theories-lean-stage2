#!/usr/bin/env python3
import importlib.util, json, sys, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
RID='evaluation_normal_0040'; MAX_NODES=120000; MAX_TERM_SIZE=45; BEAM=220; ROUNDS=7; SECONDS=40.0

def load_solver():
    p=ROOT/'submissions/mathgraph/solver.py'
    spec=importlib.util.spec_from_file_location('mg796compat',p)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

def load_row(path):
    for i,line in enumerate(Path(path).read_text().splitlines(),1):
        if not line.strip(): continue
        r=json.loads(line); rid=r.get('id') or r.get('problem_id') or r.get('name') or f'evaluation_normal_{i-1:04d}'
        if rid==RID: return r
    raise RuntimeError('0040 not found')

def eq_fields(r):
    def pick(*ks):
        for k in ks:
            if isinstance(r.get(k),str): return r[k]
    a=pick('equation1','equation_1','source','hypothesis','lhs_equation'); b=pick('equation2','equation_2','target','conclusion','rhs_equation')
    if not a or not b: raise RuntimeError('equation fields missing')
    return a,b

def positions(t,p=()):
    yield p,t
    if t[0]=='op':
        yield from positions(t[1],p+('L',)); yield from positions(t[2],p+('R',))

def proof_nodes(nodes,root):
    seen=set(); stack=[root]
    while stack:
        i=stack.pop()
        if i in seen: continue
        seen.add(i); stack.extend(getattr(nodes[i],'parents',()))
    return len(seen)

def main(path,outpath):
    m=load_solver(); row=load_row(path); eq1,eq2=eq_fields(row)
    source=m.parse_equation(eq1); target=m.parse_equation(eq2); tl,tr=target[:2]; sl,sr,sv=source
    deadline=time.monotonic()+SECONDS; nodes=[]; best={}; source_cache={}
    counters={'source_instances':0,'compatibility_lifts':0,'transitivity_steps':0,'generated_states':0}
    def add(n):
        if len(nodes)>=MAX_NODES or m.term_size(n.lhs)>MAX_TERM_SIZE or m.term_size(n.rhs)>MAX_TERM_SIZE: return None
        k=(n.lhs,n.rhs)
        if k in best: return best[k]
        i=len(nodes); nodes.append(n); best[k]=i; return i
    def M(a,b): return ('op',a,b)
    def R(t): return add(m.EqualityNode(t,t,'reflexivity',constructor='compatibility-lift'))
    def S(i):
        if i is None:return None
        p=nodes[i]; return add(m.EqualityNode(p.rhs,p.lhs,'symmetry',parents=(i,),constructor='compatibility-lift'))
    def T(i,j):
        if i is None or j is None:return None
        a,b=nodes[i],nodes[j]
        if a.rhs!=b.lhs:return None
        k=add(m.EqualityNode(a.lhs,b.rhs,'transitivity',parents=(i,j),constructor='compatibility-lift'))
        if k is not None:counters['transitivity_steps']+=1
        return k
    def H(vals):
        key=tuple(vals)
        if key in source_cache:return source_cache[key]
        mp=dict(zip(sv,vals)); lhs,rhs=m.substitute(sl,mp),m.substitute(sr,mp)
        i=add(m.EqualityNode(lhs,rhs,'source instance',substitution=tuple((v,mp[v]) for v in sv),constructor='compatibility-lift'))
        source_cache[key]=i
        if i is not None:counters['source_instances']+=1
        return i
    def lift(eq_id,outer,path):
        if eq_id is None:return None
        cur=outer; frames=[]
        for d in path:
            if cur[0]!='op':return None
            if d=='L':frames.append(('L',cur[2]));cur=cur[1]
            else:frames.append(('R',cur[1]));cur=cur[2]
        if cur!=nodes[eq_id].lhs:return None
        out=eq_id
        for d,sib in reversed(frames):
            p=nodes[out]
            if d=='L': n=m.EqualityNode(M(p.lhs,sib),M(p.rhs,sib),'congruence on left child',parents=(out,),context=('left',sib),constructor='compatibility-lift')
            else: n=m.EqualityNode(M(sib,p.lhs),M(sib,p.rhs),'congruence on right child',parents=(out,),context=('right',sib),constructor='compatibility-lift')
            out2=add(n)
            if out2 is None:return None
            out=out2;counters['compatibility_lifts']+=1
        return out
    target_terms=set(m.walk_subterms(tl))|set(m.walk_subterms(tr)); seed=target_terms|{('var',v) for v in set(source[2])|set(target[2])}
    pool=sorted(seed,key=lambda t:(m.term_size(t),m.structural_distance(t,tr),m.render_term(t)))[:14]
    root=R(tl); states={tl:root}; found=states.get(tr); snaps=[]
    def score(t):
        overlap=sum(st in target_terms for st in m.walk_subterms(t))
        return (m.structural_distance(t,tr),abs(m.term_size(t)-m.term_size(tr)),-overlap,m.term_size(t),m.render_term(t))
    for rnd in range(1,ROUNDS+1):
        if found is not None or time.monotonic()>=deadline or len(nodes)>=MAX_NODES:break
        nxt=dict(states)
        for term in sorted(states,key=score)[:BEAM]:
            if time.monotonic()>=deadline:break
            sid=states[term]
            for path,sub in positions(term):
                partial={}
                if m.match_term(sr,sub,partial) and all(v in partial for v in sv):
                    nid=T(sid,lift(S(H(tuple(partial[v] for v in sv))),term,path))
                    if nid is not None:nxt.setdefault(nodes[nid].rhs,nid);counters['generated_states']+=1
                for yv in pool[:8]:
                    for zv in pool[:8]:
                        if time.monotonic()>=deadline:break
                        mp={sv[0]:sub}
                        if len(sv)>1:mp[sv[1]]=yv
                        if len(sv)>2:mp[sv[2]]=zv
                        hid=H(tuple(mp[v] for v in sv))
                        if hid is None or nodes[hid].lhs!=sub:continue
                        nid=T(sid,lift(hid,term,path))
                        if nid is not None and nodes[nid].rhs not in nxt:nxt[nodes[nid].rhs]=nid;counters['generated_states']+=1
                    if time.monotonic()>=deadline:break
        states=dict(sorted(nxt.items(),key=lambda kv:score(kv[0]))[:BEAM*3]); found=states.get(tr); bt=min(states,key=score)
        snap={'round':rnd,'states':len(states),'nodes':len(nodes),'best_distance':m.structural_distance(bt,tr),'best_term':m.render_term(bt),'found':found is not None,**counters};snaps.append(snap);print('COMPAT0040',json.dumps(snap,sort_keys=True),flush=True)
    replay=False;err=None;pn=None
    if found is not None:
        try: replay=bool(m.replay_dag(source,nodes,found,maximum_term_size=MAX_TERM_SIZE,maximum_nodes=MAX_NODES));pn=proof_nodes(nodes,found)
        except Exception as e:err=type(e).__name__+': '+str(e)
    bt=min(states,key=score); out={'id':RID,'found':found is not None,'replayed':replay,'proof_nodes':pn,'replay_error':err,'nodes':len(nodes),'states':len(states),'best_distance':m.structural_distance(bt,tr),'best_term':m.render_term(bt),'snapshots':snaps,'counters':counters}
    Path(outpath).parent.mkdir(parents=True,exist_ok=True);Path(outpath).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print('COMPAT0040_SUMMARY',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__':
    import argparse;a=argparse.ArgumentParser();a.add_argument('--normal',required=True);a.add_argument('--output',required=True);x=a.parse_args();main(x.normal,x.output)

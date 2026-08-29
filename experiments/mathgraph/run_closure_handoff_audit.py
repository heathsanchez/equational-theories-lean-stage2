#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
IDS={'evaluation_extra_hard_0143','evaluation_extra_hard_0036','evaluation_normal_0036'}

def load_solver():
    spec=importlib.util.spec_from_file_location('mg_closure_solver',SOLVER)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

def inline(t,rev,seen=None):
    seen=set() if seen is None else seen
    if t[0]=='var' and t[1] in rev and t[1] not in seen:
        return inline(rev[t[1]],rev,seen|{t[1]})
    if t[0]=='op': return ('op',inline(t[1],rev,seen),inline(t[2],rev,seen))
    return t

def rigid_match(pattern, concrete, subst):
    if pattern[0]=='var':
        n=pattern[1]
        if n.startswith('@'): return pattern==concrete
        if n in subst: return subst[n]==concrete
        subst[n]=concrete; return True
    return concrete[0]=='op' and rigid_match(pattern[1],concrete[1],subst) and rigid_match(pattern[2],concrete[2],subst)

def covers(a,b,x,y):
    for p,q in ((a,b),(b,a)):
        s={}
        if rigid_match(p,x,s) and rigid_match(q,y,s): return True
    return False

def obj_summary(x):
    if x is None or isinstance(x,(str,int,float,bool)): return x
    if isinstance(x,(tuple,list)): return [obj_summary(v) for v in list(x)[:12]]
    if isinstance(x,dict): return {str(k):obj_summary(v) for k,v in list(x.items())[:30]}
    return repr(x)[:500]

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); args=ap.parse_args()
    m=load_solver(); rows=[r for r in json.load(open(args.input)) if r['id'] in IDS]; out=[]
    for row in rows:
        source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
        lim=dict(m.COMPACT_SUPERPOSITION_PROBE); lim.update({'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
        eng=m.TargetGroundedRefutation(source,target,time.monotonic()+10.0,lim); ans=eng.solve()
        rev=getattr(eng,'reverse_constants',{})
        clauses=[]
        for i,c in enumerate(eng.search.clauses):
            a,b=inline(c.lhs,rev),inline(c.rhs,rev)
            clauses.append((i,a,b,getattr(c,'proof_id',None),getattr(c,'kind',None)))
        # target-grounded representation if available
        grounded_target=getattr(eng,'target',target)
        gt_l=inline(grounded_target[0],rev) if isinstance(grounded_target,tuple) and len(grounded_target)>=2 else target[0]
        gt_r=inline(grounded_target[1],rev) if isinstance(grounded_target,tuple) and len(grounded_target)>=2 else target[1]
        direct=[]
        for i,a,b,pid,kind in clauses:
            if covers(a,b,target[0],target[1]) or covers(a,b,gt_l,gt_r):
                direct.append({'clause':i,'lhs':m.render_term(a),'rhs':m.render_term(b),'proof_id':pid,'kind':kind})
        # Try search normalization APIs if present, but never assume names.
        normalization={}
        for name in ('normalize','normalize_term','reduce','rewrite','normal_form'):
            fn=getattr(eng.search,name,None)
            if callable(fn):
                for label,t in [('target_lhs',getattr(eng,'ground_target_lhs',gt_l)),('target_rhs',getattr(eng,'ground_target_rhs',gt_r))]:
                    try: normalization[name+':'+label]=obj_summary(fn(t))
                    except Exception as e: normalization[name+':'+label]='ERROR '+type(e).__name__+': '+str(e)
        attrs={}
        for objname,obj in [('engine',eng),('search',eng.search)]:
            attrs[objname+'_methods']=[n for n in dir(obj) if not n.startswith('_') and callable(getattr(obj,n,None))]
            for n in ('goal','target','ground_target','target_lhs','target_rhs','root','proof_root','result','rules','clauses'):
                if hasattr(obj,n) and n not in ('clauses',): attrs[objname+':'+n]=obj_summary(getattr(obj,n))
        out.append({'id':row['id'],'solve_found':bool(ans),'solve_repr':obj_summary(ans),'clauses':len(clauses),'rounds':getattr(eng.search,'rounds',None),'superpositions':getattr(eng.search,'superpositions',None),'reductions':getattr(eng.search,'reductions',None),'direct_target_cover':direct[:20],'normalization':normalization,'introspection':attrs})
    Path(args.output).parent.mkdir(parents=True,exist_ok=True); Path(args.output).write_text(json.dumps({'rows':out},indent=2,sort_keys=True)); print(json.dumps({'rows':out},indent=2,sort_keys=True))
if __name__=='__main__': main()

#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time, urllib.request
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
SOLVER=ROOT/'submissions/mathgraph/solver.py'
HELPER_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/normal0040-alpha-self-overlap-20260826/experiments/mathgraph/run_normal0040_materialized_self_overlap.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'

def load(path,name):
    s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m

def alpha_sig(rigid,a,b):
    n={}; x=rigid.alpha_canonical_term(a,n); y=rigid.alpha_canonical_term(b,n); return min((x,y),(y,x))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); ap.add_argument('--seconds',type=float,default=120); a=ap.parse_args()
    m=load(SOLVER,'mg_f258sep'); rigid=m.RigidSuperpositionModule()
    hp=ROOT/'experiments/mathgraph/_runtime_old_0040_helper.py'; hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h=load(hp,'mg_old_f258sep'); row=h.load_row(a.input)
        source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
        limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':a.seconds,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':100000,'new_clauses_per_round':64,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})
        engine=m.TargetGroundedRefutation(source,target,time.monotonic()+a.seconds,limits); search=engine.search
        trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
        ids={'f15','f17','f18','f19','f20','f27','f81','f95','f123','f126','f130','f148','f150','f196','f217','f258','f259'}
        defs={}; wanted={}
        for block in h.fof_blocks(proof):
            q=h.parse_fof(block)
            if not q: continue
            fid,kind,formula,_=q
            try: eq=h.formula_equality(formula)
            except Exception: eq=None
            if eq is None: continue
            x,y=eq
            if kind=='definition':
                if x[0]=='var' and x[1].startswith('sF'): defs[x[1]]=y
                elif y[0]=='var' and y[1].startswith('sF'): defs[y[1]]=x
            elif fid in ids:
                wanted[fid]=(h.map_rigids(h.inline_defs(x,defs),target[2]),h.map_rigids(h.inline_defs(y,defs),target[2]))
        wsig={fid:alpha_sig(rigid,*eq) for fid,eq in wanted.items()}
        def inline_pair(r): return (h.inline_engine_names(r.lhs,engine.reverse_constants),h.inline_engine_names(r.rhs,engine.reverse_constants))
        def matchfid(r,fid): return alpha_sig(rigid,*inline_pair(r))==wsig[fid]
        def orient(c,rev): return c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,))
        def expand_term(t):
            if t[0]=='var' and t[1] in engine.reverse_constants: return expand_term(engine.reverse_constants[t[1]])
            if t[0]=='op': return ('op',expand_term(t[1]),expand_term(t[2]))
            return t
        def expand_recipe(r,cache=None):
            cache={} if cache is None else cache
            if id(r) in cache: return cache[id(r)]
            ps=tuple(expand_recipe(p,cache) for p in r.parents); data=r.data
            if r.kind=='source':
                sub,rev=data; data=(tuple((k,expand_term(v)) for k,v in sub),rev)
            elif r.kind=='instantiate': data=tuple((k,expand_term(v)) for k,v in data)
            elif r.kind=='congruence': data=(data[0],expand_term(data[1]))
            q=m.Recipe(expand_term(r.lhs),expand_term(r.rhs),r.kind,ps,data); cache[id(r)]=q; return q
        original_cp=search.critical_pair
        def cp(outer,inner,oi,ii,path): return original_cp(expand_recipe(outer),expand_recipe(inner),oi,ii,path)
        search.critical_pair=cp
        def variants(c):
            o=search.orient(c)
            if o is not None: return [o]
            out=[]
            if c.lhs[0]!='var': out.append(c)
            if c.rhs[0]!='var': out.append(m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
            return out
        def rkey(r): return (search.alpha_signature(r.lhs,r.rhs),r.lhs,r.rhs)
        pending=[]; queued=set(); processed=set(); active=[]
        def enqueue(r):
            k=rkey(r)
            if k in processed or k in queued: return
            queued.add(k); pending.append(r)
        for r in search.rules(): enqueue(r)
        unguided_f258=None; given_steps=0; enumerated=0
        start=time.monotonic()
        while pending and not search.expired() and unguided_f258 is None:
            pending.sort(key=search.target_score); given=pending.pop(0); gkey=rkey(given); queued.discard(gkey)
            if gkey in processed: continue
            processed.add(gkey); given_steps+=1
            rules=search.rules(); partners=active[-256:]; pairings=[]
            for partner in partners:
                pairings.append((given,partner))
                if rkey(partner)!=gkey: pairings.append((partner,given))
            pairings.append((given,given)); proposals=[]; expired=False
            for oi,(outer,inner) in enumerate(pairings):
                if search.expired(): expired=True; break
                for path in m.nonvariable_positions(outer.lhs,maximum_depth=12,include_root=True):
                    if search.expired(): expired=True; break
                    p=search.critical_pair(outer,inner,oi,oi+1,path)
                    if p is None: continue
                    p=search.interreduce(p,rules); enumerated+=1; proposals.append((search.target_score(p),p))
                if expired: break
            proposals.sort(key=lambda x:x[0]); added=0
            for _,p in proposals:
                before=len(search.clauses)
                if search.add_clause(p):
                    search.superpositions+=1; added+=1
                    for c in search.clauses[before:]:
                        if matchfid(c,'f258') and unguided_f258 is None: unguided_f258=c
                        for r in variants(c): enqueue(r)
                    if unguided_f258 is not None or added>=64: break
            active.append(given)
            if expired: break

        # Build the known replay-valid f217 partner without using it to guide the unguided search.
        def replay(c):
            nodes,root=search.compile(engine.inline_recipe(c)); return bool(m.replay_dag(source,nodes,root,maximum_term_size=300,maximum_nodes=60000)),len(nodes)
        def cover(fid):
            goal=wanted[fid]
            for c in search.clauses:
                x,y=inline_pair(c)
                for rev,(u,v) in enumerate(((x,y),(y,x))):
                    sub={}
                    if rigid.match_term(u,goal[0],sub) and rigid.match_term(v,goal[1],sub): return search.instantiate(orient(c,bool(rev)),sub)
            # if search clauses changed too much, use fresh initial engine covers
            fresh=m.TargetGroundedRefutation(source,target,time.monotonic()+10.0,limits)
            fresh.solve()
            for c in fresh.search.clauses:
                x,y=(h.inline_engine_names(c.lhs,fresh.reverse_constants),h.inline_engine_names(c.rhs,fresh.reverse_constants))
                for rev,(u,v) in enumerate(((x,y),(y,x))):
                    sub={}
                    if rigid.match_term(u,goal[0],sub) and rigid.match_term(v,goal[1],sub): return fresh.search.instantiate(orient(c,bool(rev)),sub)
            return None
        def derive(left,right,fid,expand=False):
            if left is None or right is None: return None,[]
            details=[]
            for A,B,label in ((left,right,'lr'),(right,left,'rl')):
                if expand: A,B=expand_recipe(A),expand_recipe(B)
                for ar in (False,True):
                    aa=orient(A,ar)
                    for br in (False,True):
                        bb=orient(B,br)
                        for path in rigid.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):
                            q=original_cp(aa,bb,0,1,path)
                            if q is None or not matchfid(q,fid): continue
                            ok,n=replay(q); details.append({'order':label,'left_rev':ar,'right_rev':br,'path':list(path),'replay':ok,'nodes':n})
                            if ok: return q,details
            return None,details
        mats={fid:cover(fid) for fid in ('f15','f19','f20','f27','f81')}
        p95,_=derive(mats['f81'],mats['f81'],'f95'); p123,_=derive(mats['f27'],p95,'f123'); p126,_=derive(mats['f15'],p95,'f126')
        p130,_=derive(p123,p126,'f130'); p148,_=derive(mats['f20'],p126,'f148'); p150,_=derive(p130,p130,'f150'); p196,_=derive(p148,p150,'f196'); guided_f217,_=derive(mats['f19'],p196,'f217',True)

        direct,direct_details=derive(unguided_f258,guided_f217,'f259',True)
        remat=None; remat_details=[]
        if unguided_f258 is not None:
            gx,gy=wanted['f258']; ux,uy=inline_pair(unguided_f258)
            for rev,(u,v) in enumerate(((ux,uy),(uy,ux))):
                sub={}
                if rigid.match_term(u,gx,sub) and rigid.match_term(v,gy,sub):
                    remat=search.instantiate(orient(unguided_f258,bool(rev)),sub); break
        remat_hit,remat_details=derive(remat,guided_f217,'f259',True)
        out={'id':RID,'seconds_to_f258':time.monotonic()-start,'given_steps':given_steps,'enumerated':enumerated,'unguided_f258_found':unguided_f258 is not None,'unguided_f258_raw':[m.render_term(unguided_f258.lhs),m.render_term(unguided_f258.rhs)] if unguided_f258 else None,'unguided_f258_inlined':[m.render_term(x) for x in inline_pair(unguided_f258)] if unguided_f258 else None,'guided_f217_ready':guided_f217 is not None,'direct_f259':direct is not None,'direct_details':direct_details,'rematerialized_f258':remat is not None,'rematerialized_f259':remat_hit is not None,'rematerialized_details':remat_details}
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('F258_TO_F259_SEPARATOR',json.dumps(out,sort_keys=True),flush=True)
    finally: hp.unlink(missing_ok=True)
if __name__=='__main__': main()

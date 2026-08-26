#!/usr/bin/env python3
import argparse, importlib.util, json, time, urllib.request
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
HELPER_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/normal0040-alpha-self-overlap-20260826/experiments/mathgraph/run_normal0040_materialized_self_overlap.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path); mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod

def alpha_sig(rigid,a,b):
    n={}; x=rigid.alpha_canonical_term(a,n); y=rigid.alpha_canonical_term(b,n); return min((x,y),(y,x))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
    m=load(SOLVER,'mg796repr'); rigid=m.RigidSuperpositionModule()
    hp=ROOT/'experiments/mathgraph/_runtime_old_0040_helper.py'; hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h=load(hp,'mgoldrepr'); row=h.load_row(a.input)
        source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
        limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
        engine=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,limits); engine.solve()
        trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
        defs={}; wanted={}; ids=('f15','f19','f20','f27','f81','f95','f123','f126','f130','f148','f150','f196','f217')
        for block in h.fof_blocks(proof):
            q=h.parse_fof(block)
            if not q: continue
            fid,kind,formula,tail=q
            try: eq=h.formula_equality(formula)
            except Exception: eq=None
            if eq is None: continue
            x,y=eq
            if kind=='definition':
                if x[0]=='var' and x[1].startswith('sF'): defs[x[1]]=y
                elif y[0]=='var' and y[1].startswith('sF'): defs[y[1]]=x
            elif fid in ids:
                wanted[fid]=(h.map_rigids(h.inline_defs(x,defs),target[2]),h.map_rigids(h.inline_defs(y,defs),target[2]))
        def inline(c): return (h.inline_engine_names(c.lhs,engine.reverse_constants),h.inline_engine_names(c.rhs,engine.reverse_constants))
        def orient(c,rev): return c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,))
        def replay(c):
            nodes,root=engine.search.compile(engine.inline_recipe(c)); return bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000)),len(nodes)
        def cover(fid):
            goal=wanted[fid]
            for idx,c in enumerate(engine.search.clauses):
                x,y=inline(c)
                for rev,(u,v) in enumerate(((x,y),(y,x))):
                    sub={}
                    if rigid.match_term(u,goal[0],sub) and rigid.match_term(v,goal[1],sub):
                        inst=engine.search.instantiate(orient(c,bool(rev)),sub)
                        return inst,{'clause_index':idx,'reverse':bool(rev),'substitution':{k:m.render_term(v) for k,v in sub.items()},'base':[m.render_term(u),m.render_term(v)],'instance':[m.render_term(inline(inst)[0]),m.render_term(inline(inst)[1])],'alpha_exact':alpha_sig(rigid,*inline(inst))==alpha_sig(rigid,*goal)}
            return None,None
        def derive(left,right,fid):
            for A,B,label in ((left,right,'lr'),(right,left,'rl')):
                for ar in (False,True):
                    aa=orient(A,ar)
                    for br in (False,True):
                        bb=orient(B,br)
                        for path in rigid.nonvariable_positions(aa.lhs,maximum_depth=12,include_root=True):
                            q=engine.search.critical_pair(aa,bb,0,1,path)
                            if q is None: continue
                            if alpha_sig(rigid,*inline(q))==alpha_sig(rigid,*wanted[fid]):
                                ok,n=replay(q)
                                if ok: engine.search.add_clause(q); return q,{'order':label,'left_rev':ar,'right_rev':br,'path':list(path),'nodes':n}
            return None,None
        mats={}; meta={}
        for fid in ('f15','f19','f20','f27','f81'): mats[fid],meta[fid]=cover(fid)
        p95,_=derive(mats['f81'],mats['f81'],'f95')
        p123,_=derive(mats['f27'],p95,'f123'); p126,_=derive(mats['f15'],p95,'f126')
        p130,_=derive(p123,p126,'f130'); p148,_=derive(mats['f20'],p126,'f148'); p150,_=derive(p130,p130,'f150'); p196,p196meta=derive(p148,p150,'f196')
        native19=mats['f19']; native196=p196
        exact19=m.Recipe(*wanted['f19'],'separator',()); exact196=m.Recipe(*wanted['f196'],'separator',())
        def known_overlap(left,right):
            a1=orient(left,True); b1=orient(right,True)
            q=engine.search.critical_pair(a1,b1,0,1,('L',))
            if q is None: return {'child':None,'alpha_hit':False}
            x,y=inline(q)
            return {'child':[m.render_term(x),m.render_term(y)],'alpha_hit':alpha_sig(rigid,x,y)==alpha_sig(rigid,*wanted['f217'])}
        def describe(c,fid):
            x,y=inline(c); gx,gy=wanted[fid]
            sub={}; forward=rigid.match_term(x,gx,sub) and rigid.match_term(y,gy,sub)
            return {'native':[m.render_term(x),m.render_term(y)],'raw_native':[m.render_term(c.lhs),m.render_term(c.rhs)],'vampire':[m.render_term(gx),m.render_term(gy)],'alpha_exact':alpha_sig(rigid,x,y)==alpha_sig(rigid,gx,gy),'native_covers_vampire':forward,'cover_substitution':{k:m.render_term(v) for k,v in sub.items()}}
        def critical_trace(left,right):
            a1=orient(left,True); b1=orient(right,True)
            fl=engine.search.freshen(a1,'o0_'); fr=engine.search.freshen(b1,'i1_')
            selected=m.get_subterm(fl.lhs,('L',)); unifier=m.unify_terms(selected,fr.lhs)
            out={'oriented_left':[m.render_term(a1.lhs),m.render_term(a1.rhs)],'oriented_right':[m.render_term(b1.lhs),m.render_term(b1.rhs)],'fresh_left':[m.render_term(fl.lhs),m.render_term(fl.rhs)],'fresh_right':[m.render_term(fr.lhs),m.render_term(fr.rhs)],'selected':m.render_term(selected),'right_lhs':m.render_term(fr.lhs),'unifier':None if unifier is None else {k:m.render_term(v) for k,v in unifier.items()}}
            if unifier is not None:
                il=engine.search.instantiate(fl,unifier); ir=engine.search.instantiate(fr,unifier); changed=m.replace_subterm(il.lhs,('L',),ir.rhs)
                out.update({'instantiated_left':[m.render_term(il.lhs),m.render_term(il.rhs)],'instantiated_right':[m.render_term(ir.lhs),m.render_term(ir.rhs)],'changed':m.render_term(changed),'changed_equals_left_rhs':changed==il.rhs})
            return out
        out={'id':RID,'f19_cover_meta':meta['f19'],'f196_derivation':p196meta,'f19':describe(native19,'f19'),'f196':describe(native196,'f196'),'known_overlap_native':known_overlap(native19,native196),'known_overlap_exact':known_overlap(exact19,exact196),'critical_trace_native':critical_trace(native19,native196),'critical_trace_exact':critical_trace(exact19,exact196)}
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('F217_PARENT_REPRESENTATION',json.dumps(out,sort_keys=True),flush=True)
    finally: hp.unlink(missing_ok=True)
if __name__=='__main__': main()

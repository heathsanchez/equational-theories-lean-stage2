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
    m=load(SOLVER,'mg796expandcorr'); rigid=m.RigidSuperpositionModule()
    hp=ROOT/'experiments/mathgraph/_runtime_old_0040_helper.py'; hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h=load(hp,'mgoldexpandcorr'); row=h.load_row(a.input)
        source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
        limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':20.0,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})
        engine=m.TargetGroundedRefutation(source,target,time.monotonic()+20.0,limits); engine.solve()
        trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
        ids=('f15','f17','f18','f19','f20','f27','f81','f95','f123','f126','f130','f148','f150','f196','f217','f229','f231','f244','f258','f259','f278')
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

        def inline(c): return (h.inline_engine_names(c.lhs,engine.reverse_constants),h.inline_engine_names(c.rhs,engine.reverse_constants))
        def orient(c,rev): return c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,))
        def replay(c):
            nodes,root=engine.search.compile(engine.inline_recipe(c)); return bool(m.replay_dag(source,nodes,root,maximum_term_size=300,maximum_nodes=60000)),len(nodes)
        def cover(fid):
            goal=wanted[fid]
            for c in engine.search.clauses:
                x,y=inline(c)
                for rev,(u,v) in enumerate(((x,y),(y,x))):
                    sub={}
                    if rigid.match_term(u,goal[0],sub) and rigid.match_term(v,goal[1],sub):
                        return engine.search.instantiate(orient(c,bool(rev)),sub)
            return None
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
                            q=engine.search.critical_pair(aa,bb,0,1,path)
                            if q is None: continue
                            if alpha_sig(rigid,*inline(q))!=alpha_sig(rigid,*wanted[fid]): continue
                            ok,n=replay(q); details.append({'order':label,'left_rev':ar,'right_rev':br,'path':list(path),'replay':ok,'nodes':n,'expanded':expand})
                            if ok:
                                engine.search.add_clause(q); return q,details
            return None,details

        mats={fid:cover(fid) for fid in ('f15','f17','f18','f19','f20','f27','f81')}
        out={'id':RID,'steps':{}}
        p95,d=derive(mats['f81'],mats['f81'],'f95',False); out['steps']['f95']=d
        p123,d=derive(mats['f27'],p95,'f123',False); out['steps']['f123']=d
        p126,d=derive(mats['f15'],p95,'f126',False); out['steps']['f126']=d
        p130,d=derive(p123,p126,'f130',False); out['steps']['f130']=d
        p148,d=derive(mats['f20'],p126,'f148',False); out['steps']['f148']=d
        p150,d=derive(p130,p130,'f150',False); out['steps']['f150']=d
        p196,d=derive(p148,p150,'f196',False); out['steps']['f196']=d
        p217,d=derive(mats['f19'],p196,'f217',True); out['steps']['f217']=d
        p229,d=derive(mats['f18'],p217,'f229',True); out['steps']['f229']=d
        p231,d=derive(p229,p126,'f231',True); out['steps']['f231']=d
        p244,d=derive(p148,p231,'f244',True); out['steps']['f244']=d
        p258,d=derive(mats['f17'],p244,'f258',True); out['steps']['f258']=d
        p259,d=derive(p258,p217,'f259',True); out['steps']['f259']=d
        p278,d=derive(mats['f15'],p259,'f278',True); out['steps']['f278']=d
        out['reached']=[fid for fid in ('f95','f123','f126','f130','f148','f150','f196','f217','f229','f231','f244','f258','f259','f278') if out['steps'].get(fid)]
        out['furthest']=out['reached'][-1] if out['reached'] else None

        out['f278_target_hit']=False; out['f278_judge_status']=None; out['f278_certificate_bytes']=None; out['f278_proof_nodes']=None
        if p278 is not None:
            rr=engine.inline_recipe(p278)
            nodes,root=engine.search.compile(rr)
            replayed=bool(m.replay_dag(source,nodes,root,maximum_term_size=300,maximum_nodes=60000))
            out['f278_replay']=replayed
            out['f278_target_hit']=(nodes[root].lhs,nodes[root].rhs)==target[:2]
            out['f278_root']=[m.render_term(nodes[root].lhs),m.render_term(nodes[root].rhs)]
            if replayed and out['f278_target_hit']:
                code,proof_nodes=m.make_dag_certificate(target,nodes,root)
                if hasattr(m,'_mg_elide_have_types'): code=m._mg_elide_have_types(code)
                out['f278_proof_nodes']=proof_nodes
                out['f278_certificate_bytes']=len(code.encode('utf-8'))
                if out['f278_certificate_bytes']<=100000:
                    out['f278_judge_status']=m.judge('true',code).get('status')

        engine.deadline=time.monotonic()+30.0; engine.search.deadline=engine.deadline
        recipe=engine.search.solve(); out['continued_recipe']=bool(recipe)
        if recipe:
            rr=engine.inline_recipe(recipe); nodes,root=engine.search.compile(rr)
            out['continued_nodes']=len(nodes); out['continued_replay']=bool(m.replay_dag(source,nodes,root,maximum_term_size=300,maximum_nodes=60000)); out['target_hit']=(nodes[root].lhs,nodes[root].rhs)==target[:2]
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
        print('GENERIC_EXPANSION_CORRIDOR',json.dumps(out,sort_keys=True),flush=True)
    finally: hp.unlink(missing_ok=True)
if __name__=='__main__': main()

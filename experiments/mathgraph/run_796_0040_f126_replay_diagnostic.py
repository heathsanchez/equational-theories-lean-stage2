#!/usr/bin/env python3
import argparse, importlib.util, json, time, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOLVER = ROOT / 'submissions/mathgraph/solver.py'
HELPER_URL = 'https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/normal0040-alpha-self-overlap-20260826/experiments/mathgraph/run_normal0040_materialized_self_overlap.py'
TRACE_URL = 'https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path); mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod

def alpha_sig(rigid,a,b):
    n={}; x=rigid.alpha_canonical_term(a,n); y=rigid.alpha_canonical_term(b,n); return min((x,y),(y,x))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
    m=load(SOLVER,'mg796f126')
    hp=ROOT/'experiments/mathgraph/_runtime_old_0040_helper.py'; hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h=load(hp,'oldh'); row=h.load_row(a.input); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
        limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
        engine=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,limits); engine.solve(); rigid=m.RigidSuperpositionModule()
        proof=next(r['proof'] for r in json.load(urllib.request.urlopen(TRACE_URL))['rows'] if r['id']==RID)
        defs={}; wanted={}
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
            elif fid in ('f15','f81','f95','f126'):
                wanted[fid]=(h.map_rigids(h.inline_defs(x,defs),target[2]),h.map_rigids(h.inline_defs(y,defs),target[2]))
        def inline_clause(c): return h.inline_engine_names(c.lhs,engine.reverse_constants),h.inline_engine_names(c.rhs,engine.reverse_constants)
        def orient(c,rev): return c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,))
        def mat_cover(fid):
            g=wanted[fid]
            for c in engine.search.clauses:
                x,y=inline_clause(c)
                for rev,(u,v) in enumerate(((x,y),(y,x))):
                    sub={}
                    if rigid.match_term(u,g[0],sub) and rigid.match_term(v,g[1],sub): return engine.search.instantiate(orient(c,bool(rev)),sub)
            return None
        f81=mat_cover('f81'); f15=mat_cover('f15'); p95=None
        if f81:
            for lr in (False,True):
                for rr in (False,True):
                    if p95: break
                    L=orient(f81,lr); R=orient(f81,rr)
                    for path in rigid.nonvariable_positions(L.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
                        q=engine.search.critical_pair(L,R,0,1,path)
                        if q and alpha_sig(rigid,*inline_clause(q))==alpha_sig(rigid,*wanted['f95']): p95=q; break
        out={'id':RID,'f15_cover':bool(f15),'f95':bool(p95),'candidates':[]}
        if f15 and p95:
            for left0,right0,label in ((f15,p95,'f15-p95'),(p95,f15,'p95-f15')):
                for lr in (False,True):
                    L=orient(left0,lr); paths=tuple(rigid.nonvariable_positions(L.lhs,maximum_depth=limits['maximum_depth'],include_root=True))
                    for rr in (False,True):
                        R=orient(right0,rr)
                        for path in paths:
                            q=engine.search.critical_pair(L,R,0,1,path)
                            if q is None or alpha_sig(rigid,*inline_clause(q))!=alpha_sig(rigid,*wanted['f126']): continue
                            nodes,root=engine.search.compile(q)
                            first_bad=None; prefix=[]
                            for i,node in enumerate(nodes):
                                # Validate the actual derivation prefix, not the full DAG with a different root.
                                ok=bool(m.replay_dag(source,nodes[:i+1],i,maximum_term_size=260,maximum_nodes=50000))
                                prefix.append(ok)
                                if not ok and first_bad is None:
                                    first_bad={'index':i,'kind':getattr(node,'kind',None),'parents':list(getattr(node,'parents',())),'lhs':m.render_term(node.lhs),'rhs':m.render_term(node.rhs),'orientation':getattr(node,'orientation',None),'substitution':[(k,m.render_term(v)) for k,v in getattr(node,'substitution',())],'context':getattr(node,'context',None),'context_record':repr(getattr(node,'context_record',None)),'overlap_record':repr(getattr(node,'overlap_record',None))}
                            out['candidates'].append({'order':label,'left_rev':lr,'right_rev':rr,'path':list(path),'nodes':len(nodes),'root':root,'root_replay':bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000)),'first_bad':first_bad,'prefix_true':sum(prefix)})
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('F126_REPLAY_DIAGNOSTIC',json.dumps(out,sort_keys=True),flush=True)
    finally: hp.unlink(missing_ok=True)
if __name__=='__main__': main()

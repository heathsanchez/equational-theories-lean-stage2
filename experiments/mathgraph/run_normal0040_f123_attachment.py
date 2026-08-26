#!/usr/bin/env python3
import argparse, importlib.util, json, re, sys, time, urllib.request
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'

def load_mod(path,name):
    spec=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(spec); sys.modules[name]=m; spec.loader.exec_module(m); return m

def alpha_sig(rigid,a,b):
    names={}; x=rigid.alpha_canonical_term(a,names); y=rigid.alpha_canonical_term(b,names); return min((x,y),(y,x))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); a=ap.parse_args()
    m=load_mod(SOLVER,'mg_f123_solver'); h=load_mod(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'mg_f123_helpers')
    row=h.load_row(a.input,RID); source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':15.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})
    engine=m.TargetGroundedRefutation(source,target,time.monotonic()+15.0,limits); baseline=engine.solve(); rigid=m.RigidSuperpositionModule()
    trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
    wanted=h.extract_wanted(proof,target[2],m,('f27','f81','f95','f123'))
    f27,f81,f95,f123=(wanted[k] for k in ('f27','f81','f95','f123'))

    def find_cover(eq):
        for c in engine.search.clauses:
            x=h.inline_engine_names(c.lhs,engine.reverse_constants); y=h.inline_engine_names(c.rhs,engine.reverse_constants)
            for rev,(u,v) in enumerate(((x,y),(y,x))):
                subst={}
                if rigid.match_term(u,eq[0],subst) and rigid.match_term(v,eq[1],subst):
                    return c,subst,bool(rev)
        return None

    out={'id':RID,'baseline_found':bool(baseline),'f81_cover_found':False,'f95_generated':False,'f27_cover_found':False,'f123_generated':False,'f123_seed_added':False,'seeded_found':False,'seeded_replay_ok':False,'proof_nodes':None,'proposal_count':0}

    c81=find_cover(f81)
    if c81:
        out['f81_cover_found']=True
        c,subst,rev=c81; base=c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,)); mat81=engine.search.instantiate(base,subst)
        goal95=alpha_sig(rigid,*f95); seed95=None
        for path in rigid.nonvariable_positions(mat81.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
            p=engine.search.critical_pair(mat81,mat81,0,0,path)
            if p is None: continue
            x=h.inline_engine_names(p.lhs,engine.reverse_constants); y=h.inline_engine_names(p.rhs,engine.reverse_constants)
            if alpha_sig(rigid,x,y)==goal95: seed95=p; break
        if seed95 is not None:
            out['f95_generated']=True; engine.search.add_clause(seed95)
            c27=find_cover(f27)
            if c27:
                out['f27_cover_found']=True
                c,subst,rev=c27; base27=c if not rev else m.Recipe(c.rhs,c.lhs,'symmetry',(c,)); mat27=engine.search.instantiate(base27,subst)
                goal123=alpha_sig(rigid,*f123); found123=None
                variants=[]
                for a0 in (mat27,m.Recipe(mat27.rhs,mat27.lhs,'symmetry',(mat27,))):
                    for b0 in (seed95,m.Recipe(seed95.rhs,seed95.lhs,'symmetry',(seed95,))):
                        for outer,inner in ((a0,b0),(b0,a0)):
                            for path in rigid.nonvariable_positions(outer.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
                                p=engine.search.critical_pair(outer,inner,0,1,path)
                                if p is None: continue
                                out['proposal_count']+=1
                                x=h.inline_engine_names(p.lhs,engine.reverse_constants); y=h.inline_engine_names(p.rhs,engine.reverse_constants)
                                if alpha_sig(rigid,x,y)==goal123:
                                    found123=p; break
                            if found123: break
                        if found123: break
                    if found123: break
                if found123 is not None:
                    out['f123_generated']=True; out['f123_seed_added']=bool(engine.search.add_clause(found123))
                    found=engine.solve(); out['seeded_found']=bool(found)
                    if found is not None:
                        nodes,root=found; out['proof_nodes']=len(m.proof_node_ids(nodes,root))
                        out['seeded_replay_ok']=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000) and (nodes[root].lhs,nodes[root].rhs)==target[:2])
    Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('NORMAL0040_F123_ATTACHMENT',json.dumps(out,sort_keys=True),flush=True)

if __name__=='__main__': main()

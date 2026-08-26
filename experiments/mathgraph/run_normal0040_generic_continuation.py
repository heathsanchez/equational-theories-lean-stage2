#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SOLVER=ROOT/'submissions/mathgraph/solver.py'
RID='evaluation_normal_0040'

def load(path,name):
    s=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(s); sys.modules[name]=m; s.loader.exec_module(m); return m

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True)
    a=ap.parse_args()
    m=load(SOLVER,'mg_generic_cont')
    h=load(Path(__file__).with_name('run_normal0040_alpha_helpers.py'),'h_generic_cont')
    row=h.load_row(a.input,RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
    lim=dict(m.COMPACT_SUPERPOSITION_PROBE)
    lim.update({'seconds':45.0,'maximum_term_size':65,'maximum_replay_term_size':260,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':64,'new_clauses_per_round':512,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':50000})

    baseline_deadline=time.monotonic()+6.0
    baseline_limits=dict(lim); baseline_limits['seconds']=6.0
    be=m.TargetGroundedRefutation(source,target,baseline_deadline,baseline_limits)
    base=be.solve()

    warm_deadline=time.monotonic()+6.0
    warm_limits=dict(lim); warm_limits['seconds']=6.0
    e=m.TargetGroundedRefutation(source,target,warm_deadline,warm_limits)
    warm=e.solve()
    r=m.RigidSuperpositionModule()
    out={'id':RID,'baseline_found':bool(base),'warm_found':bool(warm),'oracle_free':True,'policy':'retain-new-pair-immediately-simplify','fresh_scheduler_budget':True}
    if warm:
        nodes,root=warm; out.update(found=True,round=-1,proof_nodes=len(m.proof_node_ids(nodes,root)),replay_ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000)))
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('NORMAL0040_GENERIC_CONTINUATION',json.dumps(out,sort_keys=True),flush=True); return

    propagation_deadline=time.monotonic()+35.0
    e.deadline=propagation_deadline
    if hasattr(e.search,'deadline'): e.search.deadline=propagation_deadline
    if hasattr(e.search,'seconds'): e.search.seconds=35.0

    target_terms=[]
    for side in target[:2]: target_terms.extend(m.walk_subterms(side))

    def inline(t): return h.inline_engine_names(t,e.reverse_constants)
    def score(c):
        x,y=inline(c.lhs),inline(c.rhs)
        d=min([m.structural_distance(x,t) for t in target_terms]+[m.structural_distance(y,t) for t in target_terms])
        return (d, max(m.term_size(x),m.term_size(y)), m.term_size(x)+m.term_size(y), m.render_term(x), m.render_term(y))
    def orientations(c):
        return (c,m.Recipe(c.rhs,c.lhs,'symmetry',(c,)))
    def cps(a0,b0,cap=32):
        made=[]
        for aa in orientations(a0):
            for bb in orientations(b0):
                for outer,inner in ((aa,bb),(bb,aa)):
                    for path in r.nonvariable_positions(outer.lhs,maximum_depth=lim['maximum_depth'],include_root=True):
                        p=e.search.critical_pair(outer,inner,0,1,path)
                        if p is not None: made.append(p)
                        if len(made)>=cap: return made
        return made

    retained=list(e.search.clauses)
    out['initial_clauses']=len(retained)
    candidates=[]
    for c in list(retained):
        if time.monotonic()>=propagation_deadline: break
        candidates.extend(cps(c,c,cap=12))
    candidates=sorted(candidates,key=score)[:256]
    frontier=[]; added0=0
    for p in candidates:
        if e.search.add_clause(p): frontier.append(p); retained.append(p); added0+=1
    out['self_overlap_candidates']=len(candidates)
    out['self_overlap_added']=added0
    out['round_stats']=[]

    for rnd in range(1,9):
        if time.monotonic()>=propagation_deadline or not frontier: break
        bank=sorted(retained,key=score)[:320]
        raw=[]; pair_attempts=0
        for f in sorted(frontier,key=score)[:96]:
            for b in bank:
                if time.monotonic()>=propagation_deadline: break
                raw.extend(cps(f,b,cap=8)); pair_attempts+=1
                if pair_attempts>=12000 or len(raw)>=5000: break
            if pair_attempts>=12000 or len(raw)>=5000 or time.monotonic()>=propagation_deadline: break
        raw=sorted(raw,key=score)[:512]
        new=[]
        for p in raw:
            if e.search.add_clause(p): new.append(p); retained.append(p)
        out['round_stats'].append({'round':rnd,'frontier_in':len(frontier),'pair_attempts':pair_attempts,'candidates':len(raw),'added':len(new),'clauses':len(e.search.clauses)})
        frontier=new

    # Separate bounded finish window: propagation gets to run first.
    finish_deadline=time.monotonic()+10.0
    e.deadline=finish_deadline
    if hasattr(e.search,'deadline'): e.search.deadline=finish_deadline
    if hasattr(e.search,'seconds'): e.search.seconds=10.0
    found=e.solve()
    if found:
        nodes,root=found
        out.update(found=True,round='finish',proof_nodes=len(m.proof_node_ids(nodes,root)),replay_ok=bool(m.replay_dag(source,nodes,root,maximum_term_size=260,maximum_nodes=50000)))
    else:
        out.update(found=False,replay_ok=False)
    Path(a.output).parent.mkdir(parents=True,exist_ok=True)
    Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print('NORMAL0040_GENERIC_CONTINUATION',json.dumps(out,sort_keys=True),flush=True)
if __name__=='__main__': main()

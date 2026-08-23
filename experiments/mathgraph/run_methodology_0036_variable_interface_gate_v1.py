#!/usr/bin/env python3
import importlib.util, json, subprocess, sys, tempfile, time
from itertools import product
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
PROTO=ROOT/'experiments/mathgraph/protocols/methodology-0036-variable-interface-gate-v1.json'
OUT=ROOT/'experiments/mathgraph/results/methodology-0036-variable-interface-gate-v1.json'
RID='evaluation_normal_0036'
HIST='origin/mathgraph/superposition-selector-tournament-20260820'

def load_hist():
    text=subprocess.check_output(['git','show',f'{HIST}:submissions/mathgraph/solver.py'],text=True)
    p=Path(tempfile.gettempdir())/'mg0036_var_if_hist.py'; p.write_text(text)
    spec=importlib.util.spec_from_file_location('mg0036_var_if_hist',p)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

def connected(search,target):
    c=search.components(); a,b=target[:2]
    return a in c and b in c and c[a]==c[b]

def state(m,source,search,target):
    root=search.shortest_path(); replay=bool(root is not None and m.replay_dag(source,search.nodes,root))
    return connected(search,target),root,replay

def make_search(m,source,target,cfg):
    cap=[]; Base=m.ContextualSearch
    class I(Base):
        def add_node(self,node,graph_edge=True):
            nid=super().add_node(node,graph_edge=graph_edge)
            if nid is not None and getattr(node,'constructor',None)=='target-narrowing': cap.append(nid)
            return nid
    s=I(source,target,time.monotonic()+10,dict(cfg['limits']))
    s.solve_target_narrowing(cfg['maximum_depth'],cfg['branching'],cfg['maximum_terms'],cfg['maximum_context_depth'])
    return s,sorted(set(cap))

def add_reentry(m,s,source,target,old):
    tr=target[1]; parents=sorted({i for i in old if s.nodes[i].lhs==tr or s.nodes[i].rhs==tr})
    sv=list(source[2]); tv=[('var',v) for v in target[2]]; before=len(s.nodes); edges=s.graph_edges; n=0
    for xv,yv in product(tv,repeat=2):
        vals=[None]*len(sv); vals[sv.index('x')]=xv; vals[sv.index('y')]=yv; vals[sv.index('z')]=tr
        origins=tuple((v,val,tuple(parents) if val==tr else ()) for v,val in zip(sv,vals))
        if s.add_source_substitution(vals,generation=1,origins=origins) is not None: n+=1
    new=[i for i in range(before,len(s.nodes)) if s.nodes[i].kind=='source reentry']
    return n,s.graph_edges-edges,new

def variable_paths(term,maxdepth,path=()):
    if len(path)>maxdepth: return
    if term[0]=='var':
        if path: yield path
        return
    if len(path)==maxdepth: return
    yield from variable_paths(term[1],maxdepth,path+('L',))
    yield from variable_paths(term[2],maxdepth,path+('R',))

def collect_var(m,s,outer_nodes,inner_nodes,maxdepth,maxcand):
    idx={}
    for iid in inner_nodes:
        n=s.nodes[iid]; idx.setdefault(n.lhs,[]).append((iid,0)); idx.setdefault(n.rhs,[]).append((iid,1))
    comps=s.components(); out={}
    for oid in outer_nodes:
        if len(out)>=maxcand: break
        outer=s.nodes[oid]
        for oside,oterm in enumerate((outer.lhs,outer.rhs)):
            for path in variable_paths(oterm,maxdepth):
                before=m.get_subterm(oterm,path)
                for iid,iside in idx.get(before,()):
                    if oid==iid and oside==iside: continue
                    inner=s.nodes[iid]; after=inner.rhs if iside==0 else inner.lhs
                    changed=m.replace_subterm(oterm,path,after)
                    if changed==oterm or m.term_size(changed)>s.max_term_size: continue
                    other=outer.rhs if oside==0 else outer.lhs
                    consequence=(other,changed)
                    score=s.overlap_score(oterm,changed,consequence,comps)
                    key=(oid,iid,oside,iside,tuple(path),changed)
                    out[key]=(score,oid,iid,oside,iside,tuple(path),before,after,changed)
                    if len(out)>=maxcand: break
                if len(out)>=maxcand: break
            if len(out)>=maxcand: break
    return sorted(out.values(),key=lambda x:x[0])

def apply(m,source,target,s,cands,cap):
    applied=0; first_join=None; first_replay=None
    for cand in cands:
        if applied>=cap: break
        before=s.components_joined; nid=s.apply_overlap(cand,1)
        if nid is None: continue
        applied+=1; conn,root,replay=state(m,source,s,target)
        if first_join is None and (s.components_joined>before or conn): first_join={'applied_index':applied,'node_id':nid}
        if replay:
            first_replay={'applied_index':applied,'node_id':nid,'root':root}; break
    conn,root,replay=state(m,source,s,target)
    return {'applied':applied,'first_join':first_join,'first_replay':first_replay,'final_connected':conn,'final_root':root,'final_replay':replay}

def main():
    p=json.loads(PROTO.read_text()); assert p['frozen_before_execution'] is True
    m=load_hist(); row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); cfg=m.CONTEXTUAL_PORTFOLIO[0]
    d=p['constraints']['maximum_position_depth']; mc=p['constraints']['maximum_candidates_per_arm']; ac=p['constraints']['matched_application_cap']

    A,oldA=make_search(m,source,target,cfg)
    Ac=collect_var(m,A,oldA,oldA,d,mc); Ar=apply(m,source,target,A,Ac,ac)

    B,oldB=make_search(m,source,target,cfg); admitted,edges,newB=add_reentry(m,B,source,target,oldB)
    pre=state(m,source,B,target)
    Bf=collect_var(m,B,newB,oldB,d,mc//2); Br=collect_var(m,B,oldB,newB,d,mc//2)
    Bc=Bf+Br; Brs=apply(m,source,target,B,Bc,ac)

    ok=(A.max_term_size==19 and B.max_term_size==19 and len(oldA)==45 and len(oldB)==45 and admitted==9 and edges==9 and not pre[0] and not pre[2])
    if not ok: decision='MEASUREMENT_FAILURE'
    elif Ar['final_connected'] or Ar['final_replay'] or Ar['first_join'] is not None: decision='R2_GENERIC_VARIABLE_OVERLAP_SUFFICIENT'
    elif Brs['final_connected'] or Brs['final_replay'] or Brs['first_join'] is not None: decision='R1_VARIABLE_INTERFACE_CAUSAL'
    else: decision='R3_VARIABLE_INTERFACE_INSUFFICIENT'
    out={'schema':p['schema'],'id':RID,'decision':decision,'measurement_ok':ok,
         'arm_A':{'candidate_count':len(Ac),**Ar},
         'arm_B':{'forward_candidates':len(Bf),'reverse_candidates':len(Br),'candidate_count':len(Bc),**Brs},
         'parent':{'admitted_reentries':admitted,'reentry_edges':edges,'pre_connected':pre[0],'pre_replay':pre[2]},
         'sealed_transfer_ids_loaded':[]}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()

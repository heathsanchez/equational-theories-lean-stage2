#!/usr/bin/env python3
import importlib.util, json, subprocess, sys, tempfile, time
from itertools import combinations, product
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
PROTO=ROOT/'experiments/mathgraph/protocols/methodology-0036-common-specialization-interface-v1.json'
OUT=ROOT/'experiments/mathgraph/results/methodology-0036-common-specialization-interface-v1.json'
RID='evaluation_normal_0036'
HIST='origin/mathgraph/superposition-selector-tournament-20260820'

def load_hist():
    text=subprocess.check_output(['git','show',f'{HIST}:submissions/mathgraph/solver.py'],text=True)
    p=Path(tempfile.gettempdir())/'mg0036_common_spec_hist.py'; p.write_text(text)
    spec=importlib.util.spec_from_file_location('mg0036_common_spec_hist',p)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

def walk(t):
    yield t
    if t[0]=='op':
        yield from walk(t[1]); yield from walk(t[2])

def occurs(v,t,subst):
    t=apply_subst(t,subst)
    if t[0]=='var': return t[1]==v
    return occurs(v,t[1],subst) or occurs(v,t[2],subst)

def apply_subst(t,subst):
    if t[0]=='var' and t[1] in subst:
        return apply_subst(subst[t[1]],subst)
    if t[0]=='op': return ('op',apply_subst(t[1],subst),apply_subst(t[2],subst))
    return t

def unify_equations(eqs):
    pending=list(eqs); subst={}
    while pending:
        a,b=pending.pop(); a=apply_subst(a,subst); b=apply_subst(b,subst)
        if a==b: continue
        if a[0]=='var':
            v=a[1]
            if occurs(v,b,subst): return None
            subst={k:apply_subst(val,{v:b}) for k,val in subst.items()}; subst[v]=b; continue
        if b[0]=='var':
            pending.append((b,a)); continue
        if a[0]!='op' or b[0]!='op': return None
        pending.append((a[1],b[1])); pending.append((a[2],b[2]))
    return subst

def node_subst(node):
    try: return {str(v):t for v,t in node.substitution}
    except Exception: return {}

def pair_status(a,b):
    sa,sb=node_subst(a),node_subst(b); shared=sorted(set(sa)&set(sb))
    if not shared: return 'literal'
    conflicts=[(sa[v],sb[v]) for v in shared if sa[v]!=sb[v]]
    if not conflicts: return 'literal'
    return 'rescued' if unify_equations(conflicts) is not None else 'blocked'

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

def audit_pairs(s,pairs,cap):
    lit=rescue=blocked=0; checked=0
    for a,b in pairs:
        if checked>=cap: break
        checked+=1; st=pair_status(s.nodes[a],s.nodes[b])
        if st=='literal': lit+=1
        elif st=='rescued': rescue+=1
        else: blocked+=1
    denom=max(1,checked-lit)
    return {'checked':checked,'literal_compatible':lit,'specialization_rescued':rescue,'blocked_after_specialization':blocked,'rescue_rate_among_nonliteral':rescue/denom}

def main():
    p=json.loads(PROTO.read_text()); assert p['frozen_before_execution'] is True
    m=load_hist(); row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); cfg=m.CONTEXTUAL_PORTFOLIO[0]
    s,old=make_search(m,source,target,cfg); admitted,edges,new=add_reentry(m,s,source,target,old)
    cap=p['constraints']['maximum_pairs_per_arm']
    A=audit_pairs(s,combinations(old,2),cap)
    B=audit_pairs(s,((r,o) for r in new for o in old),cap)
    ok=(s.max_term_size==19 and len(old)==45 and admitted==9 and edges==9 and len(new)==9)
    if not ok: decision='MEASUREMENT_FAILURE'
    elif B['specialization_rescued']==0: decision='NO_SPECIALIZATION_RESCUE'
    elif B['rescue_rate_among_nonliteral']>A['rescue_rate_among_nonliteral']: decision='SYNCHRONIZED_SPECIALIZATION_SIGNAL'
    else: decision='GENERIC_SPECIALIZATION_SIGNAL'
    out={'schema':p['schema'],'id':RID,'decision':decision,'measurement_ok':ok,'arm_A_old_old':A,'arm_B_reentry_old':B,'parent':{'old_frontier_nodes':len(old),'admitted_reentries':admitted,'reentry_edges':edges,'new_reentry_nodes':len(new),'operative_cap':s.max_term_size},'sealed_transfer_ids_loaded':[]}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()

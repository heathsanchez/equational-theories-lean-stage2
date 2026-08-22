#!/usr/bin/env python3
import importlib.util, json, statistics, subprocess, sys, tempfile, time
from collections import Counter
from itertools import product
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
PROTO=ROOT/'experiments/mathgraph/protocols/methodology-0036-component-cut-factorization-v1.json'
OUT=ROOT/'experiments/mathgraph/results/methodology-0036-component-cut-factorization-v1.json'
RID='evaluation_normal_0036'; HIST='origin/mathgraph/superposition-selector-tournament-20260820'

def load_hist():
    text=subprocess.check_output(['git','show',f'{HIST}:submissions/mathgraph/solver.py'],text=True)
    p=Path(tempfile.gettempdir())/'mg0036_cut_hist.py'; p.write_text(text)
    spec=importlib.util.spec_from_file_location('mg0036_cut_hist',p)
    m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

def make_search(m,source,target,cfg):
    cap=[]; Base=m.ContextualSearch
    class I(Base):
        def add_node(self,node,graph_edge=True):
            nid=super().add_node(node,graph_edge=graph_edge)
            if nid is not None and getattr(node,'constructor',None)=='target-narrowing': cap.append(nid)
            return nid
    s=I(source,target,time.monotonic()+12,dict(cfg['limits']))
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

def alpha(t,env=None):
    env={} if env is None else env
    if t[0]=='var':
        env.setdefault(t[1],f'v{len(env)}'); return ('var',env[t[1]])
    return ('op',alpha(t[1],env),alpha(t[2],env))
def akey(t): return repr(alpha(t,{}))

def basis(m,target): return {akey(x) for side in target[:2] for x in m.walk_subterms(side) if x[0]=='op'}
def cov(m,t,b): return {akey(x) for x in m.walk_subterms(t) if x[0]=='op' and akey(x) in b}
def med(xs): return statistics.median(xs) if xs else None

def component_state(m,s,target,report_cap):
    comps=s.components(); tl,tr=target[:2]
    if tl not in comps or tr not in comps: return None
    lc,rc=comps[tl],comps[tr]
    L=sorted([t for t,c in comps.items() if c==lc],key=s.term_key)
    R=sorted([t for t,c in comps.items() if c==rc],key=s.term_key)
    if lc==rc:
        return {'connected':True,'lhs_size':len(L),'rhs_size':len(R),'cross_distance':0,'boundary_pairs':[],'signature_counts':{},'dominant_signature_fraction':1.0}
    best=None; pairs=[]
    for a in L:
        for b in R:
            d=m.structural_distance(a,b)
            if best is None or d<best: best=d; pairs=[(a,b)]
            elif d==best: pairs.append((a,b))
    def sig(a,b):
        if m.is_subterm(a,b): sub='L_IN_R'
        elif m.is_subterm(b,a): sub='R_IN_L'
        else: sub='NONE'
        return (a[0],b[0],abs(m.term_size(a)-m.term_size(b)),abs(len(m.term_variables(a))-len(m.term_variables(b))),sub)
    counts=Counter(sig(a,b) for a,b in pairs)
    dominant=max(counts.values(),default=0)/max(1,len(pairs))
    shown=[]
    for a,b in pairs[:report_cap]:
        shown.append({'lhs_component_term':m.render_term(a),'rhs_component_term':m.render_term(b),'distance':best,'signature':list(sig(a,b)),'lhs_size':m.term_size(a),'rhs_size':m.term_size(b)})
    return {'connected':False,'lhs_size':len(L),'rhs_size':len(R),'cross_distance':best,'boundary_pair_count':len(pairs),'boundary_pairs':shown,'signature_counts':{repr(k):v for k,v in counts.items()},'dominant_signature_fraction':dominant,'lhs_members':L,'rhs_members':R,'component_map':comps}

def association(m,s,target,old_nodes,state,max_records):
    if state is None or state.get('connected'): return {'positive_gain_count':0,'zero_gain_count':0,'positive_gain_median_opposite_distance':None,'zero_gain_median_opposite_distance':None}
    b=basis(m,target); source_base=cov(m,s.source[0],b)|cov(m,s.source[1],b)
    comps=state['component_map']; tl,tr=target[:2]; lc,rc=comps[tl],comps[tr]
    L=state['lhs_members']; R=state['rhs_members']; pos=[]; zero=[]; records=[]; seen=set()
    for nid in old_nodes:
        n=s.nodes[nid]
        for t in (n.lhs,n.rhs):
            if t in seen: continue
            seen.add(t); c=comps.get(t)
            if c not in (lc,rc): continue
            opposite=R if c==lc else L
            d=min((m.structural_distance(t,o) for o in opposite),default=None)
            if d is None: continue
            gain=len(cov(m,t,b)-source_base)
            (pos if gain>0 else zero).append(d)
            if len(records)<max_records: records.append({'term':m.render_term(t),'component':'L' if c==lc else 'R','target_gain':gain,'opposite_distance':d})
    return {'positive_gain_count':len(pos),'zero_gain_count':len(zero),'positive_gain_median_opposite_distance':med(pos),'zero_gain_median_opposite_distance':med(zero),'records':records}

def clean(st):
    if st is None:return None
    return {k:v for k,v in st.items() if k not in ('lhs_members','rhs_members','component_map')}

def main():
    p=json.loads(PROTO.read_text()); assert p['frozen_before_execution'] and RID not in p['sealed_transfer_ids']
    m=load_hist(); row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); cfg=m.CONTEXTUAL_PORTFOLIO[0]
    cap=p['constraints']['maximum_boundary_pairs_reported']; mr=p['constraints']['maximum_endpoint_records']
    S0,old0=make_search(m,source,target,cfg); st0=component_state(m,S0,target,cap); as0=association(m,S0,target,old0,st0,mr)
    S1,old1=make_search(m,source,target,cfg); admitted,edges,new=add_reentry(m,S1,source,target,old1); st1=component_state(m,S1,target,cap); as1=association(m,S1,target,old1+new,st1,mr)
    ok=(S0.max_term_size==19 and S1.max_term_size==19 and len(old0)==45 and len(old1)==45 and admitted==9 and edges==9 and st0 is not None and st1 is not None)
    surrogate=False
    if ok and not st1.get('connected'):
        pg=as1['positive_gain_median_opposite_distance']; zg=as1['zero_gain_median_opposite_distance']
        surrogate=(pg is not None and zg is not None and pg>=zg)
    compact=(ok and not st1.get('connected') and st1.get('dominant_signature_fraction',0)>=p['constraints']['compact_signature_fraction'])
    if not ok: decision='MEASUREMENT_FAILURE'
    elif st1.get('connected') or st1['cross_distance']<st0['cross_distance']: decision='CUT_ALREADY_CONTRACTED_BY_REENTRY'
    elif surrogate: decision='TARGET_COVERAGE_SURROGATE'
    elif compact: decision='COMPACT_CUT_OBLIGATION'
    else: decision='MULTIMODAL_CUT'
    out={'schema':p['schema'],'id':RID,'decision':decision,'measurement_ok':ok,'equations':{'source':row['equation1'],'target':row['equation2']},'S0':clean(st0),'S1':clean(st1),'association_S0':as0,'association_S1':as1,'reentry':{'admitted':admitted,'edges':edges},'secondary_flags':{'target_coverage_surrogate':surrogate,'compact_cut_signature':compact},'sealed_transfer_ids_loaded':[]}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()

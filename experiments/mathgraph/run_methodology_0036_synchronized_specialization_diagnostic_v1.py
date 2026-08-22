#!/usr/bin/env python3
import importlib.util, json, subprocess, sys, tempfile, time
from itertools import product
from pathlib import Path
from datasets import load_dataset

ROOT=Path(__file__).resolve().parents[2]
PROTO=ROOT/'experiments/mathgraph/protocols/methodology-0036-synchronized-specialization-diagnostic-v1.json'
OUT=ROOT/'experiments/mathgraph/results/methodology-0036-synchronized-specialization-diagnostic-v1.json'
RID='evaluation_normal_0036'; HIST='origin/mathgraph/superposition-selector-tournament-20260820'

def load_hist():
    text=subprocess.check_output(['git','show',f'{HIST}:submissions/mathgraph/solver.py'],text=True)
    p=Path(tempfile.gettempdir())/'mg0036_sync_hist.py'; p.write_text(text)
    spec=importlib.util.spec_from_file_location('mg0036_sync_hist',p); m=importlib.util.module_from_spec(spec); sys.modules[spec.name]=m; spec.loader.exec_module(m); return m

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

def rename(t,pfx):
    if t[0]=='var': return ('var',pfx+t[1])
    return ('op',rename(t[1],pfx),rename(t[2],pfx))
def deref(t,s):
    seen=set()
    while t[0]=='var' and t[1] in s and t[1] not in seen:
        seen.add(t[1]); t=s[t[1]]
    return t
def occurs(v,t,s):
    t=deref(t,s)
    if t[0]=='var': return t[1]==v
    return occurs(v,t[1],s) or occurs(v,t[2],s)
def unify(a,b):
    s={}; stack=[(a,b)]
    while stack:
        x,y=stack.pop(); x=deref(x,s); y=deref(y,s)
        if x==y: continue
        if x[0]=='var':
            if occurs(x[1],y,s): return None
            s[x[1]]=y; continue
        if y[0]=='var':
            if occurs(y[1],x,s): return None
            s[y[1]]=x; continue
        if x[0]!='op' or y[0]!='op': return None
        stack.extend([(x[1],y[1]),(x[2],y[2])])
    return s
def apply_sub(t,s):
    t=deref(t,s)
    if t[0]=='var': return t
    return ('op',apply_sub(t[1],s),apply_sub(t[2],s))

def positions(t,path=()):
    if path: yield path
    if t[0]=='op':
        yield from positions(t[1],path+('L',)); yield from positions(t[2],path+('R',))

def target_basis(m,target):
    return {akey(x) for side in target[:2] for x in m.walk_subterms(side) if x[0]=='op'}
def coverage(m,terms,basis):
    return {akey(x) for t in terms for x in m.walk_subterms(t) if x[0]=='op' and akey(x) in basis}

def scan(m,s,outer_ids,inner_ids,target,maxchecks):
    basis=target_basis(m,target); baseline=coverage(m,s.source[:2],basis)
    checked=literal=unifiable=rescue=target_rescue=0; examples=[]
    for oid in outer_ids:
      on=s.nodes[oid]
      for oside,ot0 in enumerate((on.lhs,on.rhs)):
       for path in positions(ot0):
        raw_before=m.get_subterm(ot0,path)
        for iid in inner_ids:
         if checked>=maxchecks: break
         inn=s.nodes[iid]
         for iside,it0 in enumerate((inn.lhs,inn.rhs)):
          if checked>=maxchecks: break
          checked+=1
          raw_inner=it0
          if raw_before==raw_inner: literal+=1; continue
          ot=rename(ot0,'A_'); it=rename(raw_inner,'B_'); before=m.get_subterm(ot,path)
          u=unify(before,it)
          if u is None: continue
          unifiable+=1
          sout=apply_sub(ot,u); sinner=apply_sub(it,u)
          changed=m.replace_subterm(sout,path,apply_sub(rename(inn.rhs if iside==0 else inn.lhs,'B_'),u))
          other=apply_sub(rename(on.rhs if oside==0 else on.lhs,'A_'),u)
          if max(m.term_size(changed),m.term_size(other))>19: continue
          rescue+=1
          gain=coverage(m,(other,changed,sinner),basis)-baseline
          if gain:
            target_rescue+=1
            if len(examples)<12: examples.append({'outer':oid,'inner':iid,'path':path,'gain':len(gain),'other':m.render_term(other),'changed':m.render_term(changed)})
        if checked>=maxchecks: break
       if checked>=maxchecks: break
      if checked>=maxchecks: break
    return {'checked':checked,'literal_matches_skipped':literal,'unifiable_nonliteral':unifiable,'admitted_rescues':rescue,'target_relevant_rescues':target_rescue,'examples':examples}

def main():
    p=json.loads(PROTO.read_text()); assert p['frozen_before_execution'] and RID not in p['sealed_transfer_ids']
    m=load_hist(); row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_normal',split='train') if r['id']==RID)
    source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2']); cfg=m.CONTEXTUAL_PORTFOLIO[0]
    A,oldA=make_search(m,source,target,cfg); armA=scan(m,A,oldA,oldA,target,p['constraints']['maximum_pair_checks_per_arm'])
    B,oldB=make_search(m,source,target,cfg); admitted,edges,newB=add_reentry(m,B,source,target,oldB); armB=scan(m,B,newB,oldB,target,p['constraints']['maximum_pair_checks_per_arm'])
    ok=(A.max_term_size==19 and B.max_term_size==19 and len(oldA)==45 and len(oldB)==45 and admitted==9 and edges==9)
    if not ok: decision='MEASUREMENT_FAILURE'
    elif armB['target_relevant_rescues']>0 and armB['target_relevant_rescues']>armA['target_relevant_rescues']: decision='R1_SYNCHRONIZED_SPECIALIZATION_SIGNAL'
    elif armA['target_relevant_rescues']>=armB['target_relevant_rescues'] and armA['target_relevant_rescues']>0: decision='R2_GENERIC_UNIFICATION_SIGNAL'
    else: decision='R3_NO_SPECIALIZATION_SIGNAL'
    out={'schema':p['schema'],'id':RID,'decision':decision,'measurement_ok':ok,'arm_A_old_old':armA,'arm_B_reentry_old':armB,'parent':{'old_nodes':len(oldB),'reentry_edges':edges},'sealed_transfer_ids_loaded':[]}
    OUT.parent.mkdir(parents=True,exist_ok=True); OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__': main()

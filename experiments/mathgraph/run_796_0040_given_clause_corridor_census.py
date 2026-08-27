#!/usr/bin/env python3
import argparse, importlib.util, json, sys, time, urllib.request
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
SOLVER=ROOT/'submissions/mathgraph/solver.py'
HELPER_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/normal0040-alpha-self-overlap-20260826/experiments/mathgraph/run_normal0040_materialized_self_overlap.py'
TRACE_URL='https://raw.githubusercontent.com/heathsanchez/equational-theories-lean-stage2/mathgraph/vampire-six-repro-20260820/experiments/mathgraph/results/vampire-six-20260820/mathgraph-six-vampire.json'
RID='evaluation_normal_0040'
CORRIDOR=('f95','f123','f126','f130','f148','f150','f196','f217','f229','f231','f244','f258','f259','f278')

def load(path,name):
    s=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m

def alpha_sig(rigid,a,b):
    n={}; x=rigid.alpha_canonical_term(a,n); y=rigid.alpha_canonical_term(b,n); return min((x,y),(y,x))

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--output',required=True); ap.add_argument('--seconds',type=float,default=120); ap.add_argument('--keep',type=int,default=64); ap.add_argument('--partners',type=int,default=256); a=ap.parse_args()
    m=load(SOLVER,'mg_gc_census'); rigid=m.RigidSuperpositionModule()
    hp=ROOT/'experiments/mathgraph/_runtime_old_0040_helper.py'; hp.write_bytes(urllib.request.urlopen(HELPER_URL).read())
    try:
        h=load(hp,'mg_old_gc_census'); row=h.load_row(a.input)
        source=m.parse_equation(row['equation1']); target=m.parse_equation(row['equation2'])
        limits=dict(m.COMPACT_SUPERPOSITION_PROBE); limits.update({'seconds':a.seconds,'maximum_term_size':65,'maximum_replay_term_size':300,'maximum_depth':12,'maximum_rules':768,'maximum_rounds':100000,'new_clauses_per_round':a.keep,'maximum_clauses':12000,'normalization_steps':256,'maximum_proof_nodes':60000})
        engine=m.TargetGroundedRefutation(source,target,time.monotonic()+a.seconds,limits); search=engine.search
        trace=json.load(urllib.request.urlopen(TRACE_URL)); proof=next(r['proof'] for r in trace['rows'] if r['id']==RID)
        defs={}; wanted={}
        ids=set(CORRIDOR)
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
        wanted_sig={fid:alpha_sig(rigid,*eq) for fid,eq in wanted.items()}
        events={fid:{'generated':0,'retained':0,'queued':0,'activated':0,'used_as_parent':0,'first_generated_step':None,'first_retained_step':None,'first_queued_step':None,'first_activated_step':None} for fid in CORRIDOR}

        def inline_pair(r):
            return (h.inline_engine_names(r.lhs,engine.reverse_constants),h.inline_engine_names(r.rhs,engine.reverse_constants))
        def matches(r):
            sig=alpha_sig(rigid,*inline_pair(r)); return [fid for fid,s in wanted_sig.items() if s==sig]
        def mark(stage,r,step):
            for fid in matches(r):
                e=events[fid]; e[stage]+=1
                fk='first_'+stage+'_step'
                if fk in e and e[fk] is None: e[fk]=step

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
        expansion_calls=0; expansion_changed=0; enumerated=0; given_steps=0
        def cp(outer,inner,oi,ii,path):
            nonlocal expansion_calls, expansion_changed
            expansion_calls+=1; eo=expand_recipe(outer); ei=expand_recipe(inner)
            if (eo.lhs,eo.rhs,ei.lhs,ei.rhs)!=(outer.lhs,outer.rhs,inner.lhs,inner.rhs): expansion_changed+=1
            return original_cp(eo,ei,oi,ii,path)
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
        def enqueue(r,step):
            k=rkey(r)
            if k in processed or k in queued: return
            queued.add(k); pending.append(r); mark('queued',r,step)
        for r in search.rules(): enqueue(r,0)
        recipe=None; start=time.monotonic()
        while pending and not search.expired() and len(search.clauses)<limits['maximum_clauses']:
            pending.sort(key=search.target_score); given=pending.pop(0); gkey=rkey(given); queued.discard(gkey)
            if gkey in processed: continue
            processed.add(gkey); given_steps+=1; mark('activated',given,given_steps)
            rules=search.rules(); goal=search.target_proof(rules)
            if goal is not None: recipe=goal; break
            partners=active[-a.partners:]; pairings=[]
            for partner in partners:
                pairings.append((given,partner));
                if rkey(partner)!=gkey: pairings.append((partner,given))
            pairings.append((given,given)); proposals=[]; expired=False
            for oi,(outer,inner) in enumerate(pairings):
                for r in (outer,inner):
                    for fid in matches(r): events[fid]['used_as_parent']+=1
                if search.expired(): expired=True; break
                for path in m.nonvariable_positions(outer.lhs,maximum_depth=limits['maximum_depth'],include_root=True):
                    if search.expired(): expired=True; break
                    p=search.critical_pair(outer,inner,oi,oi+1,path)
                    if p is None: continue
                    p=search.interreduce(p,rules); enumerated+=1; mark('generated',p,given_steps); proposals.append((search.target_score(p),p))
                if expired: break
            proposals.sort(key=lambda x:x[0]); added=0
            for _,p in proposals:
                before=len(search.clauses)
                if search.add_clause(p):
                    search.superpositions+=1; added+=1; mark('retained',p,given_steps)
                    for c in search.clauses[before:]:
                        for r in variants(c): enqueue(r,given_steps)
                    if added>=a.keep: break
            active.append(given); search.rounds=given_steps
            goal=search.target_proof(search.rules())
            if goal is not None: recipe=goal; break
            if expired: break
        out={'id':RID,'found_recipe':bool(recipe),'seconds':time.monotonic()-start,'given_steps':given_steps,'clauses':len(search.clauses),'pending_rules':len(pending),'active_rules':len(active),'enumerated':enumerated,'superpositions':search.superpositions,'reductions':search.reductions,'expansion_calls':expansion_calls,'expansion_changed':expansion_changed,'events':events,'reached_generated':[f for f in CORRIDOR if events[f]['generated']],'reached_retained':[f for f in CORRIDOR if events[f]['retained']],'reached_activated':[f for f in CORRIDOR if events[f]['activated']]}
        Path(a.output).parent.mkdir(parents=True,exist_ok=True); Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print('GIVEN_CLAUSE_CORRIDOR_CENSUS',json.dumps(out,sort_keys=True),flush=True)
    finally: hp.unlink(missing_ok=True)
if __name__=='__main__': main()

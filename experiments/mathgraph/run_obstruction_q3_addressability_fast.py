#!/usr/bin/env python3
import importlib.util, json, sys
from pathlib import Path
from datasets import load_dataset
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'experiments/mathgraph/run_obstruction_vector_q0_composition.py'

def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m

def main():
 ov=load(BASE,'ov_q3_base')
 m=ov.load(ov.SOLVER,'ov_q3_m');sym=ov.load(ov.SYM,'ov_q3_sym');selfm=ov.load(ov.SELF,'ov_q3_self');op=ov.load(ov.OPC,'ov_q3_op');op.selfmod=selfm
 miss=ov.load(ov.MISS,'ov_q3_miss');reify=ov.load(ov.REIFY,'ov_q3_reify');reify.selfm=selfm;ms=ov.load(ov.MS,'ov_q3_ms');ms.selfmod=selfm
 j=ov.load(ov.JOIN,'ov_q3_j');j.selfm=selfm;bridge=ov.load(ov.BRIDGE,'ov_q3_bridge');bridge.selfm=selfm;att=ov.load(ov.ATT,'ov_q3_att');att.selfm=selfm
 row=next(dict(r) for r in load_dataset('SAIRfoundation/equational-theories-selected-problems','evaluation_order5',split='train') if r['id']==ov.RID)
 source=m.parse_equation(row['equation1']);target=m.parse_equation(row['equation2'])
 base,common,req,rkeys,atoms,attachments,s1w,s2w,S2items=ov.build_atomic(m,sym,source,target,selfm,op,miss,reify,ms,j,bridge,att)
 s2,closed2=ov.state(m,sym,source,target,S2items,28);g2=ov.geometry(m,target,s2.nodes);f2=ov.boundary_features(m,target,g2,s2.nodes,rkeys)
 exact=0;examples=[];eps=j.endpoint_vars(source)
 if eps:
  ep=eps[0];bare_left=source[0][0]=='var' and source[0][1]==ep;pattern=source[1] if bare_left else source[0]
  for side_name,A,B in [('L_to_R',g2['L'],g2['R']),('R_to_L',g2['R'],g2['L'])]:
   for a in sorted(A,key=m.term_size)[:80]:
    for b in sorted(B,key=m.term_size)[:80]:
     env={ep:a}
     if m.match_term(pattern,b,env) and all(v in env for v in source[2]):
      exact+=1
      if len(examples)<8: examples.append({'direction':side_name,'anchor':m.render_term(a),'matched':m.render_term(b),'subst':{k:m.render_term(v) for k,v in env.items()}})
 out={'schema':'mathgraph.obstruction-q3-addressability-fast.v1','id':ov.RID,'baseline':{**{k:g2[k] for k in ('lhs_present','rhs_present','joined','cross_distance')},**f2},'Q3':{'exact_live_component_source_bridges':exact,'decision':'ADDRESSABILITY_OBSTRUCTION_IN_BOUND' if exact==0 else 'EXACT_BRIDGE_ADDRESSABLE','examples':examples},'bounds':{'left_component_examined':min(80,len(g2['L'])),'right_component_examined':min(80,len(g2['R']))},'protocol':{'bounded_only':True,'no_global_addressability_claim':True}}
 outp=ROOT/'experiments/mathgraph/results/obstruction-q3-addressability-fast.json';outp.parent.mkdir(parents=True,exist_ok=True);outp.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2,sort_keys=True),flush=True)
if __name__=='__main__': main()

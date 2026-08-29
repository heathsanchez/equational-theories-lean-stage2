import importlib.util,json,sys
from pathlib import Path
HELPER=Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec=importlib.util.spec_from_file_location('sep18_helper_sizeaudit',HELPER)
h=importlib.util.module_from_spec(spec); sys.modules[spec.name]=h; spec.loader.exec_module(h)

def main():
  eqs=h.load_equations(); m=h.load_solver(); source=m.parse_equation(eqs[2666]); target=m.parse_equation(eqs[2860])
  x,y,z=(('var','x'),('var','y'),('var','z')); M=lambda a,b:('op',a,b)
  v0=M(x,y); v1=M(x,v0); v2=M(v1,z); v3=M(v2,z); v6=M(v3,v0)
  args_list=[(v3,v0,v0),(v2,z,z),(v1,z,z),(M(v3,v3),z,z),(M(v6,v6),v0,v0),(x,v0,y)]
  sl,sr,vs=source; rows=[]
  for i,args in enumerate(args_list,1):
    mp=dict(zip(vs,args)); lhs=m.substitute(sl,mp); rhs=m.substitute(sr,mp)
    rows.append({'teacher_atom':i,'arg_sizes':[m.term_size(a) for a in args],'lhs_size':m.term_size(lhs),'rhs_size':m.term_size(rhs),'passes_35':m.term_size(lhs)<=35 and m.term_size(rhs)<=35,'passes_65':m.term_size(lhs)<=65 and m.term_size(rhs)<=65})
  out={'schema':'mathgraph.2666-teacher-atom-size-audit.v1','rows':rows}
  p=Path('experiments/mathgraph/results/2666-teacher-atom-size-audit.json'); p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()

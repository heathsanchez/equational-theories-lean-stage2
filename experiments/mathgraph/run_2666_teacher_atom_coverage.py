import importlib.util, json, sys
from itertools import product
from pathlib import Path
HELPER=Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec=importlib.util.spec_from_file_location('sep18_helper_atomcov',HELPER)
h=importlib.util.module_from_spec(spec); sys.modules[spec.name]=h; spec.loader.exec_module(h)

def main():
    eqs=h.load_equations(); m=h.load_solver(); source=m.parse_equation(eqs[2666]); target=m.parse_equation(eqs[2860])
    x,y,z=(('var','x'),('var','y'),('var','z')); M=lambda a,b:('op',a,b)
    v0=M(x,y); v1=M(x,v0); v2=M(v1,z); v3=M(v2,z); v6=M(v3,v0)
    teacher_args=[
      ('h4',(v3,v0,v0)),('h7',(v2,z,z)),('h_v1zz',(v1,z,z)),
      ('h_v3v3',(M(v3,v3),z,z)),('h_v6v6',(M(v6,v6),v0,v0)),('h_xv0y',(x,v0,y)),
    ]
    tl,tr=target[:2]; terms=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))|{x,y,z}
    term_list=sorted(terms,key=lambda t:(m.term_size(t),m.render_term(t))); seed_fill=term_list[:14]
    seeded=set(); sv=source[2]
    for pattern in source[:2]:
      for concrete in term_list:
        partial={}
        if not m.match_term(pattern,concrete,partial): continue
        missing=[v for v in sv if v not in partial]
        for fill in product(seed_fill,repeat=len(missing)):
          mp=dict(partial); mp.update(zip(missing,fill)); args=tuple(mp[v] for v in sv)
          lhs=m.substitute(source[0],mp); rhs=m.substitute(source[1],mp); seeded.add((lhs,rhs))
    rows=[]
    for name,args in teacher_args:
      mp=dict(zip(sv,args)); pair=(m.substitute(source[0],mp),m.substitute(source[1],mp))
      rows.append({'name':name,'seeded':pair in seeded,'args':[m.render_term(a) for a in args],
                   'arg_in_target_terms':[a in terms for a in args],
                   'arg_in_seed_fill':[a in seed_fill for a in args],
                   'arg_sizes':[m.term_size(a) for a in args]})
    out={'schema':'mathgraph.2666-teacher-atom-coverage.v1','term_count':len(term_list),'seed_fill_count':len(seed_fill),
         'seeded_equalities':len(seeded),'rows':rows}
    p=Path('experiments/mathgraph/results/2666-teacher-atom-coverage.json'); p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()

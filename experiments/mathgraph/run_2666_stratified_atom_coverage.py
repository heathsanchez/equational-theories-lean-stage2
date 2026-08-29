import importlib.util,json,sys,time
from pathlib import Path
HELPER=Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec=importlib.util.spec_from_file_location('sep18_helper_strat_atoms',HELPER)
h=importlib.util.module_from_spec(spec); sys.modules[spec.name]=h; spec.loader.exec_module(h)

def main():
  eqs=h.load_equations(); m=h.load_solver(); source=m.parse_equation(eqs[2666]); target=m.parse_equation(eqs[2860])
  key=lambda t:(m.term_size(t),m.render_term(t)); tl,tr=target[:2]
  base=set(m.walk_subterms(tl))|set(m.walk_subterms(tr))|{('var',v) for v in target[2]}; base=sorted(base,key=key)
  gen1=[]; seen=set(base)
  for a in base:
    for b in base:
      t=('op',a,b)
      if m.term_size(t)<=21 and t not in seen: seen.add(t); gen1.append(t)
  squares=[]; attachments=[]
  for a in gen1:
    sq=('op',a,a)
    if m.term_size(sq)<=31 and sq not in seen: seen.add(sq); squares.append(sq)
    for b in base:
      for t in (('op',a,b),('op',b,a)):
        if m.term_size(t)<=31 and t not in seen: seen.add(t); attachments.append(t)
  dist=lambda t:(min(m.structural_distance(t,tl),m.structural_distance(t,tr)),m.term_size(t),m.render_term(t))
  pool=[]
  def take(items,n):
    for t in sorted(items,key=dist)[:n]:
      if t not in pool: pool.append(t)
  take(base,len(base)); take(gen1,60); take(squares,70); take(attachments,80); pool=pool[:220]
  limits={'max_term_size':35,'max_pool_terms':220,'max_core_terms':48,'max_source_attempts':700000,'max_source_edges':16000,'max_graph_edges':20000,'max_derivation_nodes':24000,'max_congruence_rounds':0}
  s=m.EqualitySearch(source,target,time.monotonic()+30,limits=limits); s.initial_pool=tuple(pool); s.instantiate_sources(pool)
  x,y,z=(('var','x'),('var','y'),('var','z')); M=lambda a,b:('op',a,b)
  v0=M(x,y); v1=M(x,v0); v2=M(v1,z); v3=M(v2,z); v6=M(v3,v0)
  teacher_args=[(v3,v0,v0),(v2,z,z),(v1,z,z),(M(v3,v3),z,z),(M(v6,v6),v0,v0),(x,v0,y)]
  sl,sr,vs=source
  wanted=[]
  for args in teacher_args:
    mp=dict(zip(vs,args)); wanted.append((m.substitute(sl,mp),m.substitute(sr,mp)))
  present=set()
  for n in s.nodes:
    if n.kind in ('source instance','source reentry'): present.add((n.lhs,n.rhs)); present.add((n.rhs,n.lhs))
  rows=[]
  for i,(args,eq) in enumerate(zip(teacher_args,wanted),1):
    rows.append({'teacher_atom':i,'present':eq in present,'arg_sizes':[m.term_size(a) for a in args],'args':[m.render_term(a) for a in args]})
  out={'schema':'mathgraph.2666-stratified-atom-coverage.v1','pool':len(pool),'source_nodes':sum(n.kind=='source instance' for n in s.nodes),'graph_edges':s.graph_edges,'exhaustion':s.exhaustion,'teacher_atoms_present':sum(r['present'] for r in rows),'teacher_atoms_total':len(rows),'rows':rows}
  p=Path('experiments/mathgraph/results/2666-stratified-atom-coverage.json'); p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,sort_keys=True))
if __name__=='__main__': main()

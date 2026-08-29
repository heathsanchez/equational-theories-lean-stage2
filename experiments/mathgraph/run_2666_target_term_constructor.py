import importlib.util,json,sys,time
from itertools import product
from pathlib import Path
HELPER=Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec=importlib.util.spec_from_file_location('sep18_helper_tterm',HELPER)
h=importlib.util.module_from_spec(spec); sys.modules[spec.name]=h; spec.loader.exec_module(h)

def main():
  eqs=h.load_equations(); m=h.load_solver(); source=m.parse_equation(eqs[2666]); target=m.parse_equation(eqs[2860])
  base=set(m.walk_subterms(target[0]))|set(m.walk_subterms(target[1]))|{('var',v) for v in target[2]}
  key=lambda t:(m.term_size(t),m.render_term(t)); base=sorted(base,key=key)
  gen1=set(base)
  for a in base:
    for b in base:
      t=('op',a,b)
      if m.term_size(t)<=21: gen1.add(t)
  # Preserve target attachment, then square promising first-generation terms.
  gen2=set(gen1)
  for a in sorted(gen1,key=key):
    sq=('op',a,a)
    if m.term_size(sq)<=31: gen2.add(sq)
    for b in base:
      for t in (('op',a,b),('op',b,a)):
        if m.term_size(t)<=31: gen2.add(t)
  pool=sorted(gen2,key=lambda t:(min(m.structural_distance(t,target[0]),m.structural_distance(t,target[1])),m.term_size(t),m.render_term(t)))[:180]

  limits={'max_term_size':35,'max_pool_terms':180,'max_core_terms':32,'max_source_attempts':500000,'max_source_edges':12000,'max_graph_edges':50000,'max_derivation_nodes':60000,'max_congruence_rounds':4}
  search=m.EqualitySearch(source,target,time.monotonic()+45.0,limits=limits)
  search.initial_pool=tuple(pool)
  search.instantiate_sources(pool)
  root=search.shortest_path()
  first=0
  for r in range(4):
    if root is not None: break
    before=len(search.nodes); search.add_congruence_round(pool[:32],first); first=before; root=search.shortest_path()
    if search.expired(): break
  result={'schema':'mathgraph.2666-target-term-constructor.v1','base_terms':len(base),'gen1_terms':len(gen1),'gen2_terms':len(gen2),'pool_terms':len(pool),'found':root is not None,'nodes':len(search.nodes),'graph_edges':search.graph_edges,'exhaustion':search.exhaustion}
  if root is not None:
    try: result['replayed']=bool(m.replay_dag(source,search.nodes,root,maximum_term_size=35,maximum_nodes=60000))
    except Exception as e: result['replayed']=False; result['replay_error']=type(e).__name__+': '+str(e)
    result['proof']=h.proof_summary(search.nodes,root)
  else: result['replayed']=False
  # Explicitly verify the two previously missing teacher arguments are now in the pool.
  x,y,z=(('var','x'),('var','y'),('var','z')); M=lambda a,b:('op',a,b); v0=M(x,y); v1=M(x,v0); v2=M(v1,z); v3=M(v2,z); v6=M(v3,v0)
  result['contains_v3_square']=M(v3,v3) in pool; result['contains_v6_square']=M(v6,v6) in pool
  p=Path('experiments/mathgraph/results/2666-target-term-constructor.json'); p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
  print(json.dumps(result,sort_keys=True))
if __name__=='__main__':main()

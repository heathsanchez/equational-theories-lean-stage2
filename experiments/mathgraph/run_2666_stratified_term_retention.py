import importlib.util,json,sys,time
from pathlib import Path
HELPER=Path('experiments/mathgraph/run_18_edge_constructor_separator.py')
spec=importlib.util.spec_from_file_location('sep18_helper_strat',HELPER)
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
  # Stratified retention: never let target-distance erase an entire constructor family.
  pool=[]
  def take(items,n):
    for t in sorted(items,key=dist)[:n]:
      if t not in pool: pool.append(t)
  take(base,len(base)); take(gen1,60); take(squares,70); take(attachments,80)
  pool=pool[:220]
  limits={'max_term_size':35,'max_pool_terms':220,'max_core_terms':48,'max_source_attempts':700000,'max_source_edges':16000,'max_graph_edges':70000,'max_derivation_nodes':80000,'max_congruence_rounds':5}
  search=m.EqualitySearch(source,target,time.monotonic()+55.0,limits=limits); search.initial_pool=tuple(pool); search.instantiate_sources(pool); root=search.shortest_path(); first=0
  for _ in range(5):
    if root is not None: break
    before=len(search.nodes); search.add_congruence_round(pool[:48],first); first=before; root=search.shortest_path()
    if search.expired(): break
  x,y,z=(('var','x'),('var','y'),('var','z')); M=lambda a,b:('op',a,b); v0=M(x,y); v1=M(x,v0); v2=M(v1,z); v3=M(v2,z); v6=M(v3,v0)
  out={'schema':'mathgraph.2666-stratified-term-retention.v1','base':len(base),'gen1':len(gen1),'squares':len(squares),'attachments':len(attachments),'pool':len(pool),
       'contains_v3_square':M(v3,v3) in pool,'contains_v6_square':M(v6,v6) in pool,'found':root is not None,'nodes':len(search.nodes),'graph_edges':search.graph_edges,'exhaustion':search.exhaustion}
  if root is not None:
    try: out['replayed']=bool(m.replay_dag(source,search.nodes,root,maximum_term_size=35,maximum_nodes=80000))
    except Exception as e: out['replayed']=False; out['replay_error']=type(e).__name__+': '+str(e)
    out['proof']=h.proof_summary(search.nodes,root)
  else: out['replayed']=False
  p=Path('experiments/mathgraph/results/2666-stratified-term-retention.json'); p.parent.mkdir(parents=True,exist_ok=True); p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n'); print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()

from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sys
R=Path(__file__).resolve().parents[4];B=R/'book/coverage/checks/applied-future26/scalar-scenario-v2';assert not B.exists();(B/'original-tmp/objects').mkdir(parents=True);(B/'sources').mkdir()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();ref=lambda p:{'file':str(p.relative_to(R)),'sha256':H(p)}
peers=[Path('/tmp/lyapunov-scalar-linear-risk26-independent-foundations-seven-component-review-v1.json'),Path('/tmp/lyapunov1397-generic-log26-independent-foundations-full-scope-review-v1.json')];expected=['440108fbd5a4919aaee2d867a50216881f8c4c114b8414d276b0ce0d1067a53c','b1f6bfb3e204fc29642f05b858838cf9ed6cee80a97a0b21a10e8e990bcf9a0c'];assert[H(p)for p in peers]==expected
sources=[(Path('/tmp/CompleteLyapunovScalarLinearScenarioRiskCumulative26.lean'),'8d4d0a9ab54a13a9941c3cedd01fabeee704b4179393918a3d17b496f74c6b21',12),(Path('/tmp/CompleteLyapunovScenarioGenericLog26.lean'),'b51899742592e88148174512e4bfea3e54064fc61e2d18e3dadb0dfb3b2b97eb',1)]
proposal=Path('/tmp/foundations-hertneck-and-scenario-source53-qualification-proposal26-v1.json');approval=Path('/tmp/hertneck-scenario-source53-independent-applied-semantic-and-full-parser-review26-v1.json');assert H(approval)=='349044d041663e5aaf6f59307297b4f01406d01c3a578d8544f2955f3c20a40e'
found=set(peers+[p for p,h,c in sources]+[proposal,approval]);seen=set()
def scan(v):
 if isinstance(v,str)and v.startswith('/tmp/')and '\n'not in v and len(v)<500:
  p=Path(v)
  if p.is_file():found.add(p)
 elif isinstance(v,dict):
  for k,x in v.items():scan(k);scan(x)
 elif isinstance(v,list):
  for x in v:scan(x)
while found-seen:
 p=next(iter(found-seen));seen.add(p)
 if p.suffix=='.json':
  try:scan(json.loads(p.read_text()))
  except json.JSONDecodeError:pass
aliases={}
for p in sorted(found):
 q=B/'original-tmp/objects'/(H(p)+p.suffix)
 if q.exists():assert H(q)==H(p)
 else:q.write_bytes(p.read_bytes())
 assert H(q)==H(p);aliases[str(p)]=ref(q)
sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
rows=[]
for(src,h,count),peer in zip(sources,peers):
 assert H(src)==h
 p=R/'verification/lean/SafeLearning'/src.name;assert not p.exists();p.write_bytes(src.read_bytes());snap=B/'sources'/(src.stem+'-source-v1.lean');snap.write_bytes(src.read_bytes());names=[r['name']for r in declarations(src.read_text())if r['kind']in['theorem','lemma']];assert len(names)==count
 d=json.loads(peer.read_text());rows.append({'source':ref(p),'source_snapshot':ref(snap),'original_source':{'file':str(src),'sha256':h},'original_source_byte_copy':aliases[str(src)],'public_theorems':names,'original_semantic_peer':aliases[str(peer)],'original_semantic_review_time':d.get('reviewed_at_utc')})
sel=json.loads((R/'reports/full-coverage/checkpoint-25-selection.json').read_text());protected={n:r['sha256']for n,r in sel['proof_files'].items()};assert len(protected)==1156
for n,h in protected.items():assert H(R/n)==h
for p in(R/'SafeLearning').iterdir():
 if p.suffix in{'.html','.css','.js'}:protected[str(p.relative_to(R))]=H(p)
for n in['core','foundations','applied','modules','applied-promotions']:p=R/'book/coverage'/(n+'.json');protected[str(p.relative_to(R))]=H(p)
for n in['book/coverage/inventory.json','book/coverage/inventory-after-correction52.json','reports/full-coverage/root-source52-final-owner-integration25-v1.json']:protected[n]=H(R/n)
observation=R/'book/coverage/checks/applied-future26/scalar-scenario/initial-original-archive-basename-collision-tool-observation-v1.json'
prep={'status':'prepared_exact_cumulative_scalar12_and_generic_log1_for_unselected_future26_actual_pairs','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'proof_sources':rows,'public_theorem_count':13,'canonical_original_byte_aliases':aliases,'protected_current_inputs_sha256':protected,'selected25_proof_source_count':1156,'current_asset_count':31,'installed25_owner_count':5,'proposed_source53_qualification':aliases[str(proposal)],'proposal_independent_approval':aliases[str(approval)],'preserved_original_preparation_tool_failure':ref(observation),'selection_caution':'Select only final cumulative12, not its duplicate separatebase5 namespace, plus separate genericlog1. Both peers retain pending wholecurrent52 and linked arbitrarytie gap; virtual/actual qualifiedSource53 fresh correspondence is still required.','scope':'Original proof bodies/actual failures/successes/peer times exact. Canonical files prepared only, compiler execution pending coordinated shared slot. No Source53 assignment or working/source/owner/PUB mutation.'}
p=B/'two-source13-canonical-source-and-original-history-preparation-v1.json';p.write_text(json.dumps(prep,indent=2)+'\n');print(json.dumps({'preparation':ref(p),'sources':2,'public_theorems':13,'original_tmp_copies':len(aliases)}))

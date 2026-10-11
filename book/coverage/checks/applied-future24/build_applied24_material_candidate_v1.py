"""Build a unique isolated candidate from fresh full-literal peers; never write live owners."""
from pathlib import Path
from datetime import datetime,timezone
import copy,json,hashlib,collections,sys,shutil
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'book/coverage/checks/applied-future24/source51'
INV='book/coverage/inventory-after-correction51.json';INV_SHA='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
OLD='book/coverage/applied.json';OLD_SHA='cf35fa4605bd21c1d6b638ab2fecfdd871beea8e7a3b850456b8053832ae9131'
PROM='book/coverage/applied-promotions.json';PROM_SHA='64d40e98a0cb98cbb0e4355c38709a6a89b7d2822e982e34fc340dbc402fcdce'
READY='book/coverage/checks/applied-future24/four-material24-canonical-paired-build-readiness-v1.json'
REVIEWS=[('/tmp/applied-total-variance-material24-three-literals-independent-foundations-review-v1.json','346051faf4e79616dfa0a0c44e33b9ab7403c8dd2c0e02b1ea1fea10f9bded1c'),('/tmp/applied-mixture-material24-two-literals-independent-foundations-review-v1.json','7a56dbb31cc537a91f3fd26913c4b5521e9899590e5f7d2e789de9295d7db4ff'),('/tmp/applied-mixture-covariance-material24-ensemble-independent-foundations-component-review-v2.json','a5574a575c2ca7ff0d422ff2369a6e070b66806afafd3c4b290aca0d242181b6')]
def path(p):return Path(p) if Path(p).is_absolute() else ROOT/p
def H(p):return hashlib.sha256(path(p).read_bytes()).hexdigest()
def read(p):return json.loads(path(p).read_text())
def rel(p):return Path(p).relative_to(ROOT).as_posix()
def ref(p):return {'file':rel(path(p)) if path(p).is_relative_to(ROOT) else str(p),'sha256':H(p)}
def exact_copy(s,t):
 s=path(s);t=path(t);t.parent.mkdir(parents=True,exist_ok=True)
 if t.exists():assert H(s)==H(t),str(t)
 else:
  with t.open('xb') as f:f.write(s.read_bytes())
 assert H(s)==H(t)
def write(name,r):
 p=BASE/name;assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
assert H(OLD)==OLD_SHA and H(PROM)==PROM_SHA and H(INV)==H('book/coverage/inventory.json')==INV_SHA
manifest=read('reports/full-coverage/checkpoint-23-manifest.json');assert len(manifest['proof_files'])==1131
protected={n:z['sha256'] for n,z in manifest['proof_files'].items()}
protected.update({n:d for n,d in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in ['book/coverage/inventory.json',OLD,PROM,'book/coverage/core.json','book/coverage/foundations.json','book/coverage/modules.json']})
def guard():
 for n,d in protected.items():assert H(n)==d,n
guard();old=read(OLD);oldprom=read(PROM);ledger=copy.deepcopy(old);prom=copy.deepcopy(oldprom);inv=read(INV);us={u['key']:u for u in inv['material_source_units']}
assert len(old['exercises'])==128 and len(old['material_claims'])==1954 and len(old['proof_files'])==298
history=[]
for n in [OLD,PROM]:
 q=BASE/'baseline23-unpruned-working'/Path(n).name;exact_copy(n,q);history.append({'original':n,'sha256':H(n),'byte_exact_copy':rel(q)})
ready=read(READY);assert ready['status']=='passed_genuine_four_canonical_standalone_and_named_pairs_unselected_future24' and ready['public_theorem_count']==29 and len(ready['proof_sources'])==4
aliases={}
def archive(p):
 p=path(p)
 if not p.is_file() or p.suffix not in ['.json','.log','.py','.lean','.txt']:return
 h=H(p);q=BASE/'objects'/(h+p.suffix);exact_copy(p,q);aliases[str(p)]={'file':rel(q),'sha256':h}
def scan(r):
 if isinstance(r,str):
  if '\n' not in r and len(r)<1000 and (r.startswith('/tmp/') or r.startswith('book/coverage/') or r.startswith('verification/lean/') or r.startswith('reports/full-coverage/')):archive(r)
 elif isinstance(r,dict):
  for k,v in r.items():scan(k);scan(v)
 elif isinstance(r,list):
  for v in r:scan(v)
scan(ready);archive(READY)
preparation=read(ready['canonical_preparation']['file']);scan(preparation);archive(ready['canonical_preparation']['file'])
for original,alias in preparation['original_TMP_byte_copies'].items():assert H(original)==H(alias['file'])==alias['sha256'];aliases[original]=copy.deepcopy(alias)
reviews=[];rows=[];claims={k:c for c in ledger['material_claims'] for k in c['source_unit_keys']}
for f,d in REVIEWS:
 assert H(f)==d;r=read(f);assert r['errors']==[] and 'passed' in r['status'];scan(r);archive(f)
 rr={'file':aliases[str(path(f))]['file'],'sha256':d,'original_TMP_path':f,'reviewer':r['reviewer'],'original_review_time':r['reviewed_at_utc']}
 reviews.append({'reference':rr,'exact_original_body':r})
 for u in r['material_units']:
  key=u['source_unit_key'];z=us[key];assert u['entire_inventory_record']==z
  assert H(z['source'])==z['source_sha256'] and hashlib.sha256(z['source_text'].encode()).hexdigest()==z['text_sha256']
  c=claims[key];assert c['source_unit_keys']==[key] and c['status']=='pending';before=copy.deepcopy(c)
  source_review={**rr,'source_unit_key':key,'unit_text_sha256':z['text_sha256'],'inventory':INV,'inventory_sha256':INV_SHA,'classification_scope':u['per_unit_reason']}
  common=dict(lean_declarations=copy.deepcopy(u['lean_declarations']),hypotheses=copy.deepcopy(u['hypotheses']),correspondence=u['per_unit_reason'],source_review=source_review,original_complete_literal_review_record=copy.deepcopy(u),preserved_entire_original_pending_claim=before)
  if u['whole_unit_approved']:
   assert u['material_status']=='proved' and u['missing_clauses']==[]
   c.update(kind='independently_reviewed_whole_mathematical_source_unit',status='proved',remaining_gaps=[],**common)
  else:
   assert key=='primer-probability.html::node-401' and u['material_status']=='pending' and u['missing_clauses']
   approved=[]
   for component in u['components']:
    assert component['missing_clauses']==[] and component['remaining_gaps']==[]
    approved.append({'id':key+'::'+component['component_id'],'statement_in_prose':component['exact_component_literal'],'kind':'independently_reviewed_mathematical_component','status':'proved','lean_declarations':copy.deepcopy(component['lean_declarations']),'hypotheses':copy.deepcopy(component['hypotheses']),'correspondence':component['per_component_reason'],'remaining_gaps':[],'source_review':copy.deepcopy(source_review)})
   c.update(kind='independently_reviewed_mathematical_unit_partial_components',status='pending',remaining_gaps=copy.deepcopy(u['missing_clauses']),approved_components=approved,**common)
  prom['material'][key]={'source_text_sha256':z['text_sha256'],'claim':{k:copy.deepcopy(v) for k,v in c.items() if k not in ['source','source_unit_keys','source_sha256','text_sha256']},'source_review':copy.deepcopy(source_review)}
  rows.append({'source_unit_key':key,'entire_current51_inventory_record':z,'original_complete_reviewed_row':u,'original_source_review':rr,'original_pending_claim':before,'normalized_exact_ledger_claim':copy.deepcopy(c)})
assert len(rows)==6 and sum(z['original_complete_reviewed_row']['whole_unit_approved'] for z in rows)==5
assert len({z['source_unit_key'] for z in rows})==6
sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
new={};actual=[];export_names=[];base_names=set()
for n,z in manifest['proof_files'].items():base_names.update(d['name'] for d in declarations(path(n).read_text()))
for z in ready['proof_sources']:
 src=z['source']['file'];h=z['source']['sha256'];assert H(src)==h and src not in old['proof_files'] and src not in manifest['proof_files'];ledger['proof_files'][src]=h
 names=[d['name'] for d in declarations(path(src).read_text()) if d['kind'] in ['theorem','lemma']];assert names==z['public_theorem_names'];export_names+=names
 evidence={src:h,z['source_snapshot']['file']:h};ps=[]
 for pair in z['actual_canonical_pair']:
  p=pair['record']['file'];a=read(p);assert H(p)==pair['record']['sha256']
  assert a['exit_code']==0 and a['source']==src and a['source_sha256_before']==a['source_sha256_after']==h and H(a['log'])==a['log_sha256']
  evidence[p]=H(p);evidence[a['log']]=H(a['log']);archive(p);scan(a);ps.append(p);actual.append({'file':p,'sha256':H(p),'entire_original_record':a})
 for review in reviews:
  if any(set(u['lean_declarations'])&set(names) for u in review['exact_original_body']['material_units']):evidence[review['reference']['file']]=review['reference']['sha256']
 new[src]={'sha256':h,'evidence_sha256':evidence,'standalone_evidence':ps[0],'standalone_evidence_sha256':H(ps[0]),'named_evidence':ps[1],'named_evidence_sha256':H(ps[1]),'theorem_count':len(names),'mapped_named_declarations':names,'ownership':'Applied24 new paired proof source for five complete material passages and one precise ensemble component; no new whole exercise or blanket node401 closure.'}
assert len(new)==4 and len(export_names)==29 and len(actual)==8
for row in rows:assert set(row['normalized_exact_ledger_claim']['lean_declarations'])<=base_names|set(export_names)
changed={z['source_unit_key'] for z in rows}
for a,b in zip(old['material_claims'],ledger['material_claims']):
 if not set(a['source_unit_keys'])&changed:assert a==b
assert old['exercises']==ledger['exercises'] and oldprom['exercises']==prom['exercises']
for k,v in oldprom['material'].items():
 if k not in changed:assert prom['material'][k]==v
assert {n:h for n,h in ledger['proof_files'].items() if n not in new}==old['proof_files']
now=datetime.now(timezone.utc).isoformat();integration={'inventory':INV,'inventory_sha256':INV_SHA,'baseline23_unpruned_working_history':history,'exact_source_reviews':[r['reference'] for r in reviews],'fresh_material_keys':sorted(changed),'new_proof_files':new,'scope':'Isolated current51 future24 candidate. Five complete variance/mixture passages, one ensemble covariance component with whole401 Gaussian numbers pending. All128 whole exercises, all old material bodies and three unreferenced metadata entries remain exact; live23 owners unchanged.'}
ledger['current24_material_candidate_integration']=integration;prom['current24_material_candidate_integration']=integration;ledger['generated_at_utc']=now
write('original-review-and-exact-row-bindings-v1.json',{'status':'passed_exact_current51_original_review_and_actual_pair_bindings','created_at_utc':now,'current_inventory':ref(INV),'exact_owned_exercise_records':[e for e in inv['exercises'] if e['source'] in old['scope_pages']],'exact_owned_material_records':[u for u in inv['material_source_units'] if u['source'] in old['scope_pages']],'baseline23_history':history,'reviews':reviews,'material_rows':rows,'new_proof_files':new,'actual_paired_records':actual,'canonical_original_path_aliases':aliases,'counts':{'material_rows':6,'whole_proved_material_units':5,'precise_component_groups':1,'whole401_status':'pending','new_sources':4,'new_public_exports':29,'actual_zero_records':8},'coverage_complete':False})
write('canonical-path-aliases-v1.json',{'status':'byte_exact_original_review_execution_checker_warning_failure_history_aliases','aliases':aliases})
write('applied24-candidate-v1.json',ledger);write('applied-promotions24-candidate-v1.json',prom)
for z in history:assert H(z['original'])==H(z['byte_exact_copy'])==z['sha256']
guard()
write('applied-audit24-candidate-source51-additions-v1.json',{'schema_version':1,'status':'isolated_source51_applied24_candidate_ready_for_independent_mechanics_no_live_mapping_claim','created_at_utc':now,'inventory':INV,'inventory_sha256':INV_SHA,'base_selection':'reports/full-coverage/checkpoint-23-manifest.json','base_selection_sha256':H('reports/full-coverage/checkpoint-23-manifest.json'),'mapped_ledger':rel(BASE/'applied24-candidate-v1.json'),'mapped_ledger_sha256':H(BASE/'applied24-candidate-v1.json'),'mapped_promotions':rel(BASE/'applied-promotions24-candidate-v1.json'),'mapped_promotions_sha256':H(BASE/'applied-promotions24-candidate-v1.json'),'candidate_builder':rel(Path(__file__)),'candidate_builder_sha256':H(__file__),'original_review_bindings':rel(BASE/'original-review-and-exact-row-bindings-v1.json'),'original_review_bindings_sha256':H(BASE/'original-review-and-exact-row-bindings-v1.json'),'canonical_path_aliases':rel(BASE/'canonical-path-aliases-v1.json'),'canonical_path_aliases_sha256':H(BASE/'canonical-path-aliases-v1.json'),'source_sha256':old['source_sha256'],'proof_files':new,'new_actual_paired_records':actual,'original_independent_review_references':[r['reference'] for r in reviews],'baseline23_owner_assets':history,'new_material_keys':sorted(changed),'counts':{'old_whole_exercises_unchanged':128,'old_exercise_claims_unchanged':468,'owned_physical_units':2059,'new_material_units':6,'new_whole_proved_material_units':5,'new_precise_component_groups':1,'whole401_remains_pending':True,'new_whole_exercises':0,'new_proof_sources':4,'new_public_exports':29,'actual_zero_paired_records':8,'prior_ledger_proof_rows_preserved':298},'coverage_complete':False,'limits':['Original full semantic review bodies/times, all failed compiler/checker trials and actual warning logs remain unchanged under explicit canonical byte aliases.','Countable variance requires true mixture L2 as explicitly inherited from source finite-second-moment assumptions. No componentwise-only implication is invented.','Node401 is partial solely for the approved equal-weight ensemble covariance clause. Its scalar Gaussian mixture probabilities and numerical comparisons remain pending.','Candidate copy is isolated; no actual global24 validation, aggregate audit, live owner amendment or publication claimed.']})
print(json.dumps({'status':'passed','offer':rel(BASE/'applied-audit24-candidate-source51-additions-v1.json'),'offer_sha256':H(BASE/'applied-audit24-candidate-source51-additions-v1.json'),'new_sources':4,'public_theorems':29,'whole_units':5,'precise_components':1}))

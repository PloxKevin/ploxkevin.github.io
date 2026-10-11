"""Build a unique isolated candidate from fresh full-literal peers; never write live owners."""
from pathlib import Path
from datetime import datetime,timezone
import copy,json,hashlib,collections,sys,shutil
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'book/coverage/checks/applied-future25/source52'
INV='book/coverage/inventory-after-correction52.json';INV_SHA='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
OLD='book/coverage/applied.json';OLD_SHA='b869af52ff5db1e39b3971cdeb32e1afae4aa87f69c59af31f599e897066464d'
PROM='book/coverage/applied-promotions.json';PROM_SHA='5d28d3d8bbcbfa0a7b96dce7b27c63ff4f55dd7f785568c8d44f6acf319815e3'
READY='book/coverage/checks/applied-future25/seven-source43-canonical-paired-build-readiness-v1.json'
REVIEWS=[('/tmp/applied-gaussian-mixture401-independent-foundations-full-source-review-v1.json','7a06bc6b2c9d3f78411468c1da48e3c9aa58a51a729d07f3ac21013150ddb727'),('/tmp/applied-conditioning-alarm25-independent-foundations-full-source-review-v1.json','9b7c9ef7ff7e4acfc2d8649a19119884025693a392307a0b3640bf26e9b26751'),('/tmp/applied-truncated-conditioning25-independent-foundations-full-source-review-v1.json','a737f8f6d7abbb31e4e697f68839ad5a75fee44256bf7ceb7c7cc954ffcc6e13')]
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
manifest=read('reports/full-coverage/checkpoint-24-selection.json');assert len(manifest['proof_files'])==1144
protected={n:z['sha256'] for n,z in manifest['proof_files'].items()}
protected.update({n:H(n) for n in ['book/coverage/inventory.json',OLD,PROM,'book/coverage/core.json','book/coverage/foundations.json','book/coverage/modules.json']+list(read(INV)['source_sha256'])})
def guard():
 for n,d in protected.items():assert H(n)==d,n
guard();old=read(OLD);oldprom=read(PROM);ledger=copy.deepcopy(old);prom=copy.deepcopy(oldprom);inv=read(INV);us={u['key']:u for u in inv['material_source_units']}
assert len(old['exercises'])==128 and len(old['material_claims'])==1954 and len(old['proof_files'])==302
history=[]
for n in [OLD,PROM]:
 q=BASE/'baseline24-unpruned-working'/Path(n).name;exact_copy(n,q);history.append({'original':n,'sha256':H(n),'byte_exact_copy':rel(q)})
ready=read(READY);assert ready['status']=='passed_genuine_seven_canonical_standalone_and_named_pairs_unselected_future25' and ready['public_theorem_count']==43 and len(ready['proof_sources'])==7
aliases={}
failed_v1_paths=['book/coverage/checks/applied-future25/build_applied25_material_candidate_v1.py','book/coverage/checks/applied-future25/run_applied25_isolated_material_candidate_actual_v1.py','book/coverage/checks/applied-future25/applied25-isolated-material-candidate-actual-v1.json','book/coverage/checks/applied-future25/applied25-isolated-material-candidate-actual-v1.log']
failed_v1_history=[ref(p) for p in failed_v1_paths]
assert read(failed_v1_paths[2])['actual_exit_code']==1
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
for p in failed_v1_paths:archive(p)
scan(ready);archive(READY)
preparation=read(ready['canonical_preparation']['file']);scan(preparation);archive(ready['canonical_preparation']['file'])
for alias in preparation['original_absolute_path_byte_aliases']:
 original=alias['original_absolute_path'];canonical=alias['canonical_file'];assert H(original)==H(canonical)==alias['sha256'];aliases[original]={'file':canonical,'sha256':alias['sha256']}
scan(read('book/coverage/checks/applied-future25/baseline-frozen24-manifest-original-byte-alias-v1.json'));archive('book/coverage/checks/applied-future25/baseline-frozen24-manifest-original-byte-alias-v1.json')
reviews=[];rows=[];claims={k:c for c in ledger['material_claims'] for k in c['source_unit_keys']}
for f,d in REVIEWS:
 assert H(f)==d;r=read(f);assert r['errors']==[] and 'passed' in r['status'];scan(r);archive(f)
 rr={'file':aliases[str(path(f))]['file'],'sha256':d,'original_TMP_path':f,'reviewer':r['reviewer'],'original_review_time':r['reviewed_at_utc']}
 reviews.append({'reference':rr,'exact_original_body':r})
 for u in r['material_units']:
  key=u['entire_inventory_record']['key'];z=us[key];assert u['entire_inventory_record']==z
  assert H(z['source'])==z['source_sha256'] and hashlib.sha256(z['source_text'].encode()).hexdigest()==z['text_sha256']
  c=claims[key];assert c['source_unit_keys']==[key] and c['status']=='pending';before=copy.deepcopy(c)
  source_review={**rr,'source_unit_key':key,'unit_text_sha256':z['text_sha256'],'inventory':INV,'inventory_sha256':INV_SHA,'classification_scope':u.get('per_unit_reason',u.get('per_component_reason','Scoped event formulas; generic joint-density clause remains pending.'))}
  whole=u['whole_source_unit_approved'] if 'whole_source_unit_approved' in u else u['whole_unit_approved']
  if whole:
   declarations=u['lean_declarations'];hypotheses=u['hypotheses'];reason=u.get('per_unit_reason',u.get('per_component_reason'))
  else:
   assert key=='primer-probability.html::node-371' and len(u['components'])==4
   declarations=list(dict.fromkeys(d for comp in u['components'] for d in comp['lean_declarations']))
   hypotheses=list(dict.fromkeys(h for comp in u['components'] for h in comp['hypotheses']))
   reason='Four actual event conditioning/finite-partition formulas are independently approved; generic joint-density conditional and marginal clauses remain pending.'
  source_review['classification_scope']=reason
  common=dict(lean_declarations=copy.deepcopy(declarations),hypotheses=copy.deepcopy(hypotheses),correspondence=reason,source_review=source_review,original_complete_literal_review_record=copy.deepcopy(u),preserved_entire_original_pending_claim=before)
  if whole:
   assert u['missing_clauses']==[]
   c.update(kind='independently_reviewed_whole_mathematical_source_unit',status='proved',remaining_gaps=[],**common)
  else:
   assert key=='primer-probability.html::node-371' and u['remaining_gaps']
   approved=[]
   for component in u['components']:
    assert component['missing_clauses']==[]
    approved.append({'id':key+'::'+component['component_id'],'statement_in_prose':{'conditional_event_ratio':r'$\mathbb P(A\mid B)=\mathbb P(A\cap B)/\mathbb P(B)$','conditional_event_product':r'$\mathbb P(A\cap B)=\mathbb P(A\mid B)\mathbb P(B)$','finite_partition_total_probability':r'$\mathbb P(A)=\sum_j\mathbb P(A\mid B_j)\mathbb P(B_j)$','finite_partition_Bayes':r'$\mathbb P(B_i\mid A)=\mathbb P(A\mid B_i)\mathbb P(B_i)/\sum_j\mathbb P(A\mid B_j)\mathbb P(B_j)$'}[component['component_id']],'kind':'independently_reviewed_mathematical_component','status':'proved','lean_declarations':copy.deepcopy(component['lean_declarations']),'hypotheses':copy.deepcopy(component['hypotheses']),'correspondence':component['per_component_reason'],'remaining_gaps':[],'source_review':copy.deepcopy(source_review)})
   c.update(kind='independently_reviewed_mathematical_unit_partial_components',status='pending',remaining_gaps=copy.deepcopy(u['remaining_gaps']),approved_components=approved,**common)
  prom['material'][key]={'source_text_sha256':z['text_sha256'],'claim':{k:copy.deepcopy(v) for k,v in c.items() if k not in ['source','source_unit_keys','source_sha256','text_sha256']},'source_review':copy.deepcopy(source_review)}
  rows.append({'source_unit_key':key,'entire_current52_inventory_record':z,'original_complete_reviewed_row':u,'original_source_review':rr,'original_pending_claim':before,'normalized_exact_ledger_claim':copy.deepcopy(c)})
assert len(rows)==11 and sum(z['normalized_exact_ledger_claim']['status']=='proved' for z in rows)==10
assert len({z['source_unit_key'] for z in rows})==11
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
  if any(set(u.get('lean_declarations', [d for c in u.get('components', []) for d in c['lean_declarations']]))&set(names) for u in review['exact_original_body']['material_units']):evidence[review['reference']['file']]=review['reference']['sha256']
 new[src]={'sha256':h,'evidence_sha256':evidence,'standalone_evidence':ps[0],'standalone_evidence_sha256':H(ps[0]),'named_evidence':ps[1],'named_evidence_sha256':H(ps[1]),'theorem_count':len(names),'mapped_named_declarations':names,'ownership':'Applied25 explicit new paired proof source for approved Gaussian401, event conditioning and truncated conditional laws; no new whole exercise or generic density371 promotion.'}
assert len(new)==7 and len(export_names)==43 and len(actual)==14
for row in rows:assert set(row['normalized_exact_ledger_claim']['lean_declarations'])<=base_names|set(export_names)
changed={z['source_unit_key'] for z in rows}
for a,b in zip(old['material_claims'],ledger['material_claims']):
 if not set(a['source_unit_keys'])&changed:assert a==b
assert old['exercises']==ledger['exercises'] and oldprom['exercises']==prom['exercises']
for k,v in oldprom['material'].items():
 if k not in changed:assert prom['material'][k]==v
assert {n:h for n,h in ledger['proof_files'].items() if n not in new}==old['proof_files']
now=datetime.now(timezone.utc).isoformat();integration={'inventory':INV,'inventory_sha256':INV_SHA,'baseline24_unpruned_working_history':history,'preserved_initial_builder_schema_failure':failed_v1_history,'exact_source_reviews':[r['reference'] for r in reviews],'fresh_material_keys':sorted(changed),'new_proof_files':new,'scope':'Isolated current52 future25 candidate: ten whole Gaussian/event/truncation passages plus four event components of371 whose generic density clauses remain pending. All128 whole exercises, old bodies and unreferenced proof metadata stay exact; live24 owners unchanged.'}
ledger['current25_material_candidate_integration']=integration;prom['current25_material_candidate_integration']=integration;ledger['generated_at_utc']=now
write('original-review-and-exact-row-bindings-v1.json',{'status':'passed_exact_current52_original_review_and_actual_pair_bindings','created_at_utc':now,'current_inventory':ref(INV),'exact_owned_exercise_records':[e for e in inv['exercises'] if e['source'] in old['scope_pages']],'exact_owned_material_records':[u for u in inv['material_source_units'] if u['source'] in old['scope_pages']],'baseline24_history':history,'preserved_initial_builder_schema_failure':failed_v1_history,'reviews':reviews,'material_rows':rows,'new_proof_files':new,'actual_paired_records':actual,'canonical_original_path_aliases':aliases,'counts':{'material_rows':11,'whole_proved_material_units':10,'precise_component_groups':4,'whole371_status':'pending','whole401_status':'proved','new_sources':7,'new_public_exports':43,'actual_zero_records':14},'coverage_complete':False})
write('canonical-path-aliases-v1.json',{'status':'byte_exact_original_review_execution_checker_warning_failure_history_aliases','aliases':aliases})
write('applied25-candidate-v1.json',ledger);write('applied-promotions25-candidate-v1.json',prom)
for z in history:assert H(z['original'])==H(z['byte_exact_copy'])==z['sha256']
guard()
write('applied-audit25-candidate-source52-additions-v1.json',{'schema_version':1,'status':'isolated_source52_applied25_candidate_ready_for_independent_mechanics_no_live_mapping_claim','created_at_utc':now,'inventory':INV,'inventory_sha256':INV_SHA,'base_selection':'reports/full-coverage/checkpoint-24-selection.json','base_selection_sha256':H('reports/full-coverage/checkpoint-24-selection.json'),'mapped_ledger':rel(BASE/'applied25-candidate-v1.json'),'mapped_ledger_sha256':H(BASE/'applied25-candidate-v1.json'),'mapped_promotions':rel(BASE/'applied-promotions25-candidate-v1.json'),'mapped_promotions_sha256':H(BASE/'applied-promotions25-candidate-v1.json'),'candidate_builder':rel(Path(__file__)),'candidate_builder_sha256':H(__file__),'original_review_bindings':rel(BASE/'original-review-and-exact-row-bindings-v1.json'),'original_review_bindings_sha256':H(BASE/'original-review-and-exact-row-bindings-v1.json'),'canonical_path_aliases':rel(BASE/'canonical-path-aliases-v1.json'),'canonical_path_aliases_sha256':H(BASE/'canonical-path-aliases-v1.json'),'source_sha256':old['source_sha256'],'proof_files':new,'new_actual_paired_records':actual,'original_independent_review_references':[r['reference'] for r in reviews],'baseline24_owner_assets':history,'preserved_initial_builder_schema_failure':failed_v1_history,'new_material_keys':sorted(changed),'counts':{'old_whole_exercises_unchanged':128,'old_exercise_claims_unchanged':468,'owned_physical_units':2059,'new_material_units':11,'new_whole_proved_material_units':10,'new_precise_component_groups':4,'whole371_remains_pending':True,'whole401_approved':True,'new_whole_exercises':0,'new_proof_sources':7,'new_public_exports':43,'actual_zero_paired_records':14,'prior_ledger_proof_rows_preserved':302},'coverage_complete':False,'limits':['Original full semantic review bodies/times, all failed compiler/checker trials and actual warning logs remain unchanged under explicit canonical byte aliases.','Countable variance requires true mixture L2 as explicitly inherited from source finite-second-moment assumptions. No componentwise-only implication is invented.','Node401 is completely approved by its fresh full peer; node371 remains pending for generic joint-density clauses and has only four approved event components.','Candidate copy is isolated; no actual global25 validation, aggregate audit, live owner amendment or publication claimed.']})
print(json.dumps({'status':'passed','offer':rel(BASE/'applied-audit25-candidate-source52-additions-v1.json'),'offer_sha256':H(BASE/'applied-audit25-candidate-source52-additions-v1.json'),'new_sources':7,'public_theorems':43,'whole_units':10,'precise_components':4}))

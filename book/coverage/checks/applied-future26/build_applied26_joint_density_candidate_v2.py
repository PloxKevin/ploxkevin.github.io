"""Create isolated future26 literal/proof candidates; no live owners are written."""
from pathlib import Path
from datetime import datetime,timezone
import copy,json,hashlib,sys
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'book/coverage/checks/applied-future26/source52-v2'
H=lambda p:hashlib.sha256((Path(p)if Path(p).is_absolute()else ROOT/p).read_bytes()).hexdigest()
read=lambda p:json.loads((Path(p)if Path(p).is_absolute()else ROOT/p).read_text())
ref=lambda p:{'file':str(Path(p).relative_to(ROOT))if Path(p).is_absolute()and Path(p).is_relative_to(ROOT)else str(p),'sha256':H(p)}
INV='book/coverage/inventory-after-correction52.json';OLD='book/coverage/applied.json';PROM='book/coverage/applied-promotions.json'
assert H(INV)==H('book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
assert H(OLD)=='0a4ee34e6e3b55391a596c90ea92591eaa6bb3f6a103016c1c01635d225e0a9b';assert H(PROM)=='2b70fcbd1536285b8c51a62de7f99d2fae4368ff06d0aeed61b3d97dfccc193a'
assert not BASE.exists();BASE.mkdir(parents=True)
old=read(OLD);oldprom=read(PROM);ledger=copy.deepcopy(old);prom=copy.deepcopy(oldprom);inv=read(INV)
selection='reports/full-coverage/checkpoint-25-selection.json';sel=read(selection);assert len(sel['proof_files'])==1156
protected={n:r['sha256']for n,r in sel['proof_files'].items()}
for n in list(inv['source_sha256'])+[INV,'book/coverage/inventory.json',OLD,PROM,'book/coverage/core.json','book/coverage/foundations.json','book/coverage/modules.json']:protected[n]=H(n)
def guard():
 for n,h in protected.items():assert H(n)==h,n
guard();history=[]
for n in [OLD,PROM]:
 q=BASE/'baseline25-unpruned-working'/Path(n).name;q.parent.mkdir(parents=True,exist_ok=True);assert not q.exists();q.write_bytes((ROOT/n).read_bytes());assert H(q)==H(n);history.append({'original':ref(n),'exact_byte_copy':ref(q)})
ready_paths=['book/coverage/checks/applied-future26/joint-density371/two-source15-canonical-paired-build-readiness-v1.json','book/coverage/checks/applied-future26/cvar-fractional-selector/one-source8-canonical-paired-build-readiness-v1.json']
ready=[read(n)for n in ready_paths];assert len(ready[0]['proof_sources'])==2 and len(ready[1]['proof_sources'])==1
prep=[read(r['canonical_preparation']['file'])for r in ready]
review_ref=prep[0]['original_semantic_peer'];review=read(review_ref['file']);assert H(review_ref['file'])==review_ref['sha256']=='50033ac5648f23b0cf3298da2019122d8567444085819f759479036ce610ceb4';assert review['errors']==[]
u=review['material_units'][0];key='primer-probability.html::node-371';current=next(z for z in inv['material_source_units']if z['key']==key);assert u['entire_inventory_record']==current and u['whole_source_unit_approved']is True and u['missing_clauses']==[]
claim=next(c for c in ledger['material_claims']if key in c['source_unit_keys']);assert claim['source_unit_keys']==[key] and claim['status']=='pending';before=copy.deepcopy(claim)
source_review={**review_ref,'original_TMP_path':'/tmp/applied-joint-density371-independent-foundations-full-source-review25-v1.json','reviewer':review['reviewer'],'original_review_time':review['reviewed_at_utc'],'source_unit_key':key,'unit_text_sha256':current['text_sha256'],'inventory':INV,'inventory_sha256':H(INV),'classification_scope':u['per_component_reason']}
claim.update(kind='independently_reviewed_whole_mathematical_source_unit',status='proved',lean_declarations=copy.deepcopy(u['lean_declarations']),hypotheses=copy.deepcopy(u['hypotheses']),correspondence=u['per_component_reason'],remaining_gaps=[],source_review=source_review,original_complete_literal_review_record=copy.deepcopy(u),preserved_entire_original_partial_claim=before)
# Original four component records stay exact as historical component decisions.
assert claim['approved_components']==before['approved_components']
prom['material'][key]={'source_text_sha256':current['text_sha256'],'claim':{k:copy.deepcopy(v)for k,v in claim.items()if k not in ['source','source_unit_keys','source_sha256','text_sha256']},'source_review':copy.deepcopy(source_review)}
sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
new={};records=[];all_names=[];all_source_declarations=[];aliases={}
for preparation in prep:
 for original,row in preparation['canonical_original_byte_aliases'].items():assert H(original)==H(row['file'])==row['sha256'];aliases[original]=row
for r in ready:
 for row in r['proof_sources']:
  src=row['source']['file'];h=row['source']['sha256'];assert H(src)==h and src not in old['proof_files'] and src not in sel['proof_files']
  actual_declarations=declarations((ROOT/src).read_text());names=[r['name']for r in actual_declarations if r['kind']in ['theorem','lemma']];source_decl_names=[r['name']for r in actual_declarations];all_source_declarations+=source_decl_names;assert names==row['public_theorems'];all_names+=names;ledger['proof_files'][src]=h
  evidence={src:h,row['source_snapshot']['file']:h};ps=[]
  for pair in row['actual_canonical_pair']:
   rr=pair['record'];assert H(rr['file'])==rr['sha256'];a=read(rr['file']);assert type(a['exit_code'])is int and a['exit_code']==0 and a['source']==src and a['source_sha256_before']==a['source_sha256_after']==h and H(a['log'])==a['log_sha256'];assert H(row['source_snapshot']['file'])==h
   evidence[rr['file']]=rr['sha256'];evidence[a['log']]=a['log_sha256'];records.append({'record':rr,'entire_original_actual_record':a});ps.append(rr)
  original_peer=row['original_semantic_peer'];assert H(original_peer['file'])==original_peer['sha256'];evidence[original_peer['file']]=original_peer['sha256']
  new[src]={'sha256':h,'evidence_sha256':evidence,'standalone_evidence':ps[0]['file'],'standalone_evidence_sha256':ps[0]['sha256'],'named_evidence':ps[1]['file'],'named_evidence_sha256':ps[1]['sha256'],'theorem_count':len(names),'mapped_named_declarations':source_decl_names,'public_theorem_names':names,'ownership':'Applied26 explicit paired proof source; joint-density whole371 or cross-owner Landscape15 CVaR proof supplied explicitly, no filename-based ownership inference.'}
assert len(new)==3 and len(all_names)==23 and len(records)==6 and len(ledger['proof_files'])==312 and len(old['proof_files'])==309
base_names=set()
for n in sel['proof_files']:base_names.update(r['name']for r in declarations((ROOT/n).read_text()))
assert set(claim['lean_declarations'])<=base_names|set(all_source_declarations)
assert old['exercises']==ledger['exercises']and oldprom['exercises']==prom['exercises']
for a,b in zip(old['material_claims'],ledger['material_claims']):
 if key not in a['source_unit_keys']:assert a==b
for k,v in oldprom['material'].items():
 if k!=key:assert prom['material'][k]==v
assert {n:h for n,h in ledger['proof_files'].items()if n not in new}==old['proof_files']
row={'source_unit_key':key,'entire_inventory_record':current,'original_complete_reviewed_row':u,'original_source_review':source_review,'preserved_original_partial_claim':before,'normalized_exact_ledger_claim':copy.deepcopy(claim)}
integration={'inventory':INV,'inventory_sha256':H(INV),'baseline25_unpruned_working_history':history,'exact_original_semantic_peer':review_ref,'original_review_time':review['reviewed_at_utc'],'fresh_material_keys':[key],'new_proof_files':new,'cross_owner_proof_supply':{'verification/lean/SafeLearning/CompleteAppliedCVaRFractionalSelector26.lean':'Module owns fresh Landscape15 whole mapping from originalad377 review; no Applied whole156/1351 promotion.'},'scope':'Isolated future26 candidate. Whole371 only, plus explicit CVaR8 proof supply. All old128 exercise/468 claims and1943? material bodies preserved; exact count asserted below. No live owner or fixed25 amendment.'}
ledger['current26_material_candidate_integration']=integration;prom['current26_material_candidate_integration']=integration;ledger['generated_at_utc']=datetime.now(timezone.utc).isoformat()
assert len(old['material_claims'])==1954;integration['scope']=integration['scope'].replace('1943?','1953 other')
def write(n,v):
 q=BASE/n;assert not q.exists();q.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n');return ref(q)
failure_paths=['book/coverage/checks/applied-future26/build_applied26_joint_density_candidate_v1.py','book/coverage/checks/applied-future26/run_applied26_joint_density_candidate_actual_v1.py','book/coverage/checks/applied-future26/applied26-isolated-joint-density-candidate-actual-v1.json','book/coverage/checks/applied-future26/applied26-isolated-joint-density-candidate-actual-v1.log']
assert read(failure_paths[2])['actual_exit_code']==1
failed=[ref(p)for p in failure_paths]
integration['preserved_initial_builder_failure']=failed
binding={'preserved_initial_builder_failure':failed,'status':'passed_exact_source52_original_whole371_and_actual_three_source_pair_bindings','current_inventory':ref(INV),'original_semantic_peer':review_ref,'entire_original_semantic_body_and_time':review,'material_rows':[row],'new_proof_files':new,'actual_paired_records':records,'canonical_original_path_aliases':aliases,'baseline25_unpruned_working_history':history,'protected_current_inputs_sha256':protected,'exact_owned_exercise_records':[e for e in inv['exercises']if e['source']in old['scope_pages']],'exact_owned_material_records':[e for e in inv['material_source_units']if e['source']in old['scope_pages']],'cvar_component_semantic_peer':prep[1]['original_semantic_peer'],'original_landscape15_whole_peer':prep[1]['original_landscape15_whole_peer'],'coverage_complete':False}
br=write('original-review-and-exact-row-bindings-v1.json',binding);cr=write('applied26-candidate-v1.json',ledger);pr=write('applied-promotions26-candidate-v1.json',prom);ar=write('canonical-path-aliases-v1.json',{'aliases':aliases});guard()
offer={'schema_version':1,'status':'isolated_source52_applied26_candidate_ready_for_independent_mechanics_no_live_mapping_claim','inventory':INV,'inventory_sha256':H(INV),'base_selection':selection,'base_selection_sha256':H(selection),'mapped_ledger':cr['file'],'mapped_ledger_sha256':cr['sha256'],'mapped_promotions':pr['file'],'mapped_promotions_sha256':pr['sha256'],'candidate_builder':ref(Path(__file__)),'original_review_bindings':br,'canonical_path_aliases':ar,'source_sha256':old['source_sha256'],'proof_files':new,'new_actual_paired_records':records,'original_independent_review_references':[review_ref,prep[1]['original_semantic_peer']],'baseline25_owner_assets':history,'new_material_keys':[key],'counts':{'old_whole_exercises_unchanged':128,'old_exercise_claims_unchanged':468,'owned_physical_units':2059,'old_material_claim_rows':1954,'other_material_rows_unchanged':1953,'new_whole_proved_material_units':1,'new_whole_exercises':0,'new_proof_sources':3,'new_public_exports':23,'actual_zero_paired_records':6,'prior_ledger_proof_rows_preserved':309},'preserved_initial_builder_failure':failed,'coverage_complete':False,'limits':['All old whole decisions and semantic bodies/review times remain exact. Original371 four approved components remain exact with full original partial-row history.','CVaR8 is explicit cross-owner proof supply for Landscape15; endpoint/inverse-transform/integral whole156/1351 scope remains pending.','No actual global26/aggregate/live owner/PUB/HTML mutation or fixed25 amendment claimed.','CumulativeCVaR8 includes separate quantile1 namespace; select cumulative8 alone and preserve original1 archival review/source.']}
of=write('applied-audit26-candidate-source52-additions-v1.json',offer);print(json.dumps({'status':'passed','offer':of,'candidate':cr,'promotions':pr,'whole_units':1,'new_sources':3,'public_names':23,'actual_pair_records':6}))

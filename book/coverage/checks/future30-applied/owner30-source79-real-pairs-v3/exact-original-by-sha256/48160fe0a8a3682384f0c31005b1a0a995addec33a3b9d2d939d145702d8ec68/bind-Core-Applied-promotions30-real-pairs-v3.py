from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp/applied30b-owner30-paired-v3')
OUT=ROOT/'book/coverage/checks/future30-applied/owner30-source79-real-pairs-v3'
DRAFT='book/coverage/checks/future30-applied/owner30-source79-draft-v4/Core-Applied-promotions30-source79-three-owned92-with-shared-Core58-isolated-draft-offer-v4.json';DRAFT_SHA='aff18254733f11f4e436074e061d7a8df0654bea2b1fa2b97e1c95883eff555d'
READINESS='book/coverage/checks/future30-core/current79-canonical-pairs45-v1/actual-reviewed30-canonical-paired-readiness-v1.json';READY_SHA='4ce14955fe77d0cc9447ff9963e79631ce8dbff3110683d261eb3c89eaa2cf7e'
PRIMARY='reports/full-coverage/current79-canonical-pairs45-application30-execution-v1.json';PRIMARY_SHA='8e3e384891e52794a493d078350abe282c8d215ff7f883eae6a3861c4eda77ee'
RUNNER='book/coverage/checks/run_root30_reviewed_canonical_pairs_v2.py';RUNNER_SHA='ec15d8df2c473174489cc412868db434e483dafc862d649334edf2d3512c4e2c'
CTX=Path('/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json');CTX_SHA='d06f4ef21178b787db693df28ca5ae01386728915e0596cba5fd17f000db0737'
physical={};aliases={}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def encoded(d):return (json.dumps(d,indent=2,ensure_ascii=False)+'\n').encode()
def check(r):
 p=ROOT/r['file'];assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'],r['file']
 assert 'bytes' not in r or p.stat().st_size==r['bytes'];physical[r['file']]=r['sha256'];return json.loads(p.read_bytes()) if p.suffix=='.json' else p
def close(p):
 p=Path(p);p=p if p.is_absolute() else ROOT/p;b=p.read_bytes();h=hashlib.sha256(b).hexdigest()
 if p.is_relative_to(ROOT):q=p
 else:
  q=OUT/'exact-original-by-sha256'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==b
  else:
   with q.open('xb') as f:f.write(b)
 n=q.relative_to(ROOT).as_posix();physical[n]=h;r={'file':n,'sha256':h,'bytes':len(b)};aliases[str(p)]=r;return r
def guard():
 assert sha(CTX)==CTX_SHA;c=json.loads(CTX.read_bytes())
 for n,h in {**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']}.items():
  p=ROOT/n;assert p.resolve().is_relative_to(ROOT) and not p.is_symlink() and sha(p)==h,n
 return {'protected_selected29_sources':1197,'unchanged_current79_book_assets':31,'unchanged_historical_Source65_owner29_files':5,'protection_errors':[]}
before=guard();OUT.mkdir(exist_ok=False)
prior_failure={k:close(Path('/tmp/applied30b-owner30-paired-v1')/name) for k,name in [('helper','bind-Core-Applied-promotions30-real-pairs-v1.py'),('recorder','run-bind-Core-Applied-promotions30-real-pairs-v1.py'),('native','Core-Applied-promotions30-real-pair-binding-actual-v1.json'),('raw_log','Core-Applied-promotions30-real-pair-binding-actual-v1.log')]}
fn=check(prior_failure['native']);assert fn['status']=='failed' and fn['actual_exit_code']==1
prior_failure['original_actual_times']={k:fn[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}
prior_failure['reason']='Binder1 parsed the real multi-line primary stdout log as JSON after verifying its SHA. NEW2 returns physical non-JSON files from check while parsing only JSON records. Actual90/compiler/semantic data and all original bodies/times remain unchanged.'
second_failure={k:close(Path('/tmp/applied30b-owner30-paired-v2')/name) for k,name in [('helper','bind-Core-Applied-promotions30-real-pairs-v2.py'),('recorder','run-bind-Core-Applied-promotions30-real-pairs-v2.py'),('native','Core-Applied-promotions30-real-pair-binding-actual-v2.json'),('raw_log','Core-Applied-promotions30-real-pair-binding-actual-v2.log')]}
sn=check(second_failure['native']);assert sn['status']=='failed' and sn['actual_exit_code']==1
second_failure['original_actual_times']={k:sn[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}
second_failure['reason']='Binder2 recovered the exact original dictionaries, then compared ASCII-escaped serialization with the genuine original UTF8 serialization. All three original owners use indent2/ensure_asciiFalse/newline. NEW3 preserves that actual encoding, enabling exact original-byte inverse; math/proof/pair data are unchanged.'
draft_ref={'file':DRAFT,'sha256':DRAFT_SHA};offer=check(draft_ref);assert offer['installation_ready'] is False
ready_ref={'file':READINESS,'sha256':READY_SHA};ready=check(ready_ref);assert ready['status']=='passed_actual_reviewed30_canonical_standalone_and_named_pairs_unselected' and ready['errors']==[]
assert ready['source_count']==len(ready['sources'])==45 and ready['public_theorem_count']==966 and ready['actual_compiler_command_count']==len(ready['actual_paired_records'])==90
primary_ref={'file':PRIMARY,'sha256':PRIMARY_SHA};native=check(primary_ref)
assert native['status']=='passed' and type(native['actual_exit_code']) is int and native['actual_exit_code']==0
assert native['actual_command']==['python3',RUNNER,'--plan','book/coverage/checks/future30-core/current79-canonical-plan45-v2.json','--plan-sha256','4a2c2ab8e877d098f243562adc2112c116aa93062b40757c2d5e0cd57f90b09d','--apply']
assert native['actual_workdir']==str(ROOT) and native['helper_sha256_before']==native['helper_sha256_after']=={RUNNER:RUNNER_SHA}
assert native['selection29_before']==native['selection29_after']=={'file':'reports/full-coverage/checkpoint-29-selection.json','sha256':'ad4eb2940daa6f89dfb52390abc26c8bedb00dae7f97534957f5a4e87ac0d8a9'}
check({'file':native['log'],'sha256':native['log_sha256']});close(RUNNER);close(native['recorder']['file'])
rows={r['canonical_source']:r for r in ready['sources']};assert len(rows)==45
roles={o:[r for r in ready['sources'] if r['owner']==o] for o in ['core','foundations','applied','modules']}
assert {o:len(rs) for o,rs in roles.items()}=={'core':1,'foundations':27,'applied':2,'modules':15}
assert {o:sum(r['public_theorem_count'] for r in rs) for o,rs in roles.items()}=={'core':58,'foundations':370,'applied':34,'modules':504}
for r in ready['actual_paired_records']:
 source=r['source']['file'];assert rows[source]['original_tmp_source']['sha256']==r['source']['sha256']==sha(ROOT/source)
 assert type(r['actual_exit_code']) is int and r['actual_exit_code']==0
 n=check(r['actual_record']);assert n['status']=='passed' and type(n['exit_code']) is int and n['exit_code']==0
 expected=['lake','env','lean','SafeLearning/'+Path(source).name] if r['kind']=='standalone' else ['lake','build','SafeLearning.'+Path(source).stem]
 assert r['kind'] in ['standalone','named'] and n['command']==expected and n['actual_workdir']==str(ROOT/'verification/lean')
 assert n['source']==source and n['source_sha256_before']==n['source_sha256_after']==r['source']['sha256']
 assert r['raw_log']=={'file':n['log'],'sha256':n['log_sha256']}
 for k in ['raw_log','source_snapshot']:
  p=ROOT/r[k]['file'];assert p.is_file() and sha(p)==r[k]['sha256'];physical[r[k]['file']]=r[k]['sha256']
 assert r['source_snapshot']['sha256']==r['source']['sha256']
candidate={x:copy.deepcopy(check(r)) for x,r in offer['outputs'].items()}
old={x:check(r) for x,r in offer['original_owner29_physical_refs'].items()};newproofs={'core':{},'applied':{}}
for plan in offer['literal_and_promotion_binding']['expected_three_pending_canonical_pair_edges_count_once']:
 owner=plan['canonical_owner'];dest=plan['expected_canonical_target'];row=rows[dest]
 assert owner==row['owner'] and row['original_tmp_source']['sha256']==plan['exact_reviewed_original_source']['sha256']
 assert sha(ROOT/dest)==plan['exact_reviewed_original_source']['sha256']
 pair=[p for p in ready['actual_paired_records'] if p['source']['file']==dest]
 assert len(pair)==2 and {p['kind'] for p in pair}=={'standalone','named'}
 names=[d['name'] for d in row['public_declarations'] if d['kind'] in ['theorem','lemma']]
 assert len(names)==len(set(names))==row['public_theorem_count']
 evidence={p[k]['file']:p[k]['sha256'] for p in pair for k in ['actual_record','raw_log','source_snapshot']}
 metadata={'sha256':row['original_tmp_source']['sha256'],'theorem_count':len(names),'public_theorem_names':names,'mapped_named_declarations':names,
 'public_declarations':row['public_declarations'],'declarations':[d['name'] for d in row['public_declarations']],
 'actual_pair':pair,'evidence_sha256':evidence,'actual_root90_primary_native':primary_ref,'actual_root45_readiness':ready_ref,
 'original_math_peer':plan['full_independent_whole_peer'],'scope':'Actual source-matched standalone/named0 pairs; original semantic peer bodies/times remain exact; aggregate kernel/axiom audit and live integration are separate.'}
 assert dest not in candidate[owner]['proof_files'];candidate[owner]['proof_files'][dest]=metadata;newproofs[owner][dest]=metadata;physical.update(evidence)
assert len(newproofs['core'])==1 and len(newproofs['applied'])==2
assert sum(p['theorem_count'] for m in newproofs.values() for p in m.values())==92
for owner in ['core','applied']:
 d=candidate[owner]
 for r in d['material_claims']:
  if 'future30_real_canonical_pair_binding_status' in r:r['future30_real_canonical_pair_binding_status']='bound_actual_source_matched_Root0_standalone_named_pair' if r['lean_declarations'] else 'editorial_scope_requires_original_full_heading_review_only'
 if owner=='core':
  e=next(e for e in d['exercises'] if e['inventory_key']=='cmdp.html::exercise-21')
  for c in e['claims']:
   if 'future30_real_canonical_pair_binding_status' in c:c['future30_real_canonical_pair_binding_status']='bound_actual_source_matched_Root0_standalone_named_pair'
  d['counts']['proof_files']=len(d['proof_files'])
for key,value in candidate['applied-promotions']['material'].items():
 if 'future30_real_canonical_pair_binding_status' in value['claim']:
  value['claim']['future30_real_canonical_pair_binding_status']='bound_actual_source_matched_Root0_standalone_named_pair' if value['claim']['lean_declarations'] else 'editorial_scope_requires_original_full_heading_review_only'
binding={'status':'actual_Root45_90_zero_pairs_bound_to_exact_Core1_Applied2_promos_candidates_independent_mapping_pending',
 'bound_at_utc':datetime.now(timezone.utc).isoformat(),'original_exact_draft_offer':draft_ref,'prior_genuine_binding1_failure':prior_failure,'prior_genuine_binding2_failure':second_failure,'actual_root90_primary_native':primary_ref,'actual_root45_readiness':ready_ref,
 'new_proof_files_by_owner':newproofs,'all_original_root90_body_times_warnings_sources_snapshots_logs_preserved':True,
 'old_owner29_proof_files_and_all_prior_mathematical_bodies_times_retained':True,
 'original_draft_binding_is_historical_and_remains_exact':True,'independent_final_forward_inverse_mapping_review_pending':True,
 'Root_live_five_owner_global_preflight_integration_selection_kernel_axiom_audit_and_publication_remain_separate':True,'coverage_complete':False}
for x in candidate:candidate[x]['future30_actual_canonical_binding']=binding
def delta(a,b,path=()):
 changes=[]
 if type(a) is not type(b):return [{'op':'replace','path':list(path),'before':a,'after':b}]
 if isinstance(a,dict):
  for k in a:
   if k not in b:changes.append({'op':'remove','path':list(path+(k,)),'before':a[k]})
   else:changes+=delta(a[k],b[k],path+(k,))
  for k in b:
   if k not in a:changes.append({'op':'add','path':list(path+(k,)),'after':b[k]})
 elif isinstance(a,list):
  if len(a)!=len(b):changes.append({'op':'replace','path':list(path),'before':a,'after':b})
  else:
   for i,(x,y) in enumerate(zip(a,b)):changes+=delta(x,y,path+(i,))
 elif a!=b:changes.append({'op':'replace','path':list(path),'before':a,'after':b})
 return changes
def transform(value,patch,inverse=False):
 d=copy.deepcopy(value)
 for op in reversed(patch) if inverse else patch:
  p=d
  for key in op['path'][:-1]:p=p[key]
  key=op['path'][-1];kind=op['op']
  if inverse:
   if kind=='add':assert p[key]==op['after'];del p[key]
   elif kind=='remove':assert key not in p;p[key]=copy.deepcopy(op['before'])
   else:assert p[key]==op['after'];p[key]=copy.deepcopy(op['before'])
  else:
   if kind=='add':assert key not in p;p[key]=copy.deepcopy(op['after'])
   elif kind=='remove':assert p[key]==op['before'];del p[key]
   else:assert p[key]==op['before'];p[key]=copy.deepcopy(op['after'])
 return d
patches={};inverse=[]
for x in candidate:
 patches[x]=delta(old[x],candidate[x]);assert transform(old[x],patches[x])==candidate[x]
 recovered=transform(candidate[x],patches[x],True);assert recovered==old[x]
 oldbytes=(ROOT/offer['original_owner29_physical_refs'][x]['file']).read_bytes();assert encoded(recovered)==oldbytes
 inverse.append({'owner':x,'exact_original_owner':offer['original_owner29_physical_refs'][x],'forward_equals_candidate':True,'inverse_recovers_original_full_dictionary_and_exact_bytes':True,'patch_operation_count':len(patches[x])})
after=guard();assert before==after
def write(name,data):
 p=OUT/name
 with p.open('xb') as f:f.write(encoded(data))
 return close(p)
outputs={x:write(x+'30-source79-actual-pair-bound-candidate-v3.json',d) for x,d in candidate.items()}
patch_ref=write('Core-Applied-promotions30-exact-raw29-forward-inverse-patches-v3.json',{'status':'exact_actual_forward_inverse_of_three_owner_dictionaries_and_original_bytes_checked','patches':patches,'inverse_checks':inverse,'original_owner_refs':offer['original_owner29_physical_refs'],'candidate_refs':outputs,'no_math_decision_inferred_from_diff':True})
close(CTX);close(Path(__file__))
for r in offer['literal_and_promotion_binding']['new_whole_material_changes']:check(r['full_independent_peer'])
final={'status':'prepared_exact_Source79_Core1_Applied2_promotions_owner30_actual90_pairs_bound_candidate_offer_independent_final_review_pending',
 'candidate_refs':outputs,'inventory':offer['current_inventory'],'inventory_sha256':offer['current_inventory']['sha256'],
 'original_draft_offer':draft_ref,'prior_genuine_binding1_failure':prior_failure,'prior_genuine_binding2_failure':second_failure,'original_owner29_physical_refs':offer['original_owner29_physical_refs'],
 'new_proof_files_by_owner':newproofs,'actual_root45_readiness':ready_ref,'actual_root90_primary_native':primary_ref,
 'exact_raw29_forward_inverse_patch':patch_ref,'inverse_checks':inverse,
 'original14_whole_material_decisions_and_full_Exercise21_scope':offer['literal_and_promotion_binding']['new_whole_material_changes'],
 'exact_new_proof_sources':3,'exact_new_public_theorems':92,'canonical_owner_role_counts':{'core':{'sources':1,'theorems':58},'applied':{'sources':2,'theorems':34}},
 'original_Core_Exercise16_stays_partial_no_Filippov17_or_other_new_source_added':True,
 'all_unchanged_prior_math_claim_bodies_reviews_failures_native_times_and_source_splits_preserved_by_inverse':True,
 'actual_canonical_pair_record_count_for_three_sources':6,'all90_actual_records_sources_snapshots_raw_status_commands_cwd_checked':True,
 'independent_final_forward_inverse_mapping_review_pending':True,'installation_ready_without_final_mapping_peer':False,
 'live_five_owner_Source_canonical_or_publication_mutation':False,'compiler_or_canonical_producer_invoked_by_binder':False,
 'before_guard':before,'after_guard':after,'coverage_complete':False,'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':physical}
fr=write('Core1-Applied2-promotions30-source79-real90-pair-bound-forward-inverse-final-review-offer-v3.json',final)
print(json.dumps({'offer':fr,'candidate_refs':outputs,'new_proof_sources':3,'new_public_theorems':92,'actual_pairs':6,'all90_checked':True,'protection_errors':[],'independent_final_review_pending':True}))

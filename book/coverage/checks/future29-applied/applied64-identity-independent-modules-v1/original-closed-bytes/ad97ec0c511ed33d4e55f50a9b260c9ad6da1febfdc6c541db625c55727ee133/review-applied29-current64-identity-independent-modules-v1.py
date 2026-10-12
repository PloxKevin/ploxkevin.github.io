from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future29-applied/applied64-identity-independent-modules-v1';assert not D.exists();D.mkdir(parents=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def loc(n):
 p=Path(n);p=p if p.is_absolute()else R/p;assert p.is_file()and not p.is_symlink()and (p.resolve().is_relative_to(R)or p.resolve().is_relative_to('/tmp'));return p
def read(p):return json.loads(Path(p).read_bytes())
def checked(r):
 p=loc(r['file']);assert sha(p)==r['sha256'];return p
O=Path('/tmp/applied29-current64-identity-v1/applied29-current64-identity-offer-draft-v2.json');assert sha(O)=='dd6eefd0638aee7a188721a348fb530028ea458a6872ca4eeab4c99a915ac38b';o=read(O)
assert o['status']=='isolated_applied29_current64_identity_candidate_awaiting_independent_mechanics'and o['errors']==[]and o['coverage_complete']is False
C=checked(o['candidate']);P=checked(o['candidate_promotions']);c=read(C);p=read(P)
B=R/'book/coverage/applied.json';BP=R/'book/coverage/applied-promotions.json';assert sha(B)=='447a97e920f8155b64067a4db0d3a785f3fe1d14e8154f05943f70d085c9f31e';assert sha(BP)=='fd6cee003ac36731f99ac5d2db20354f798c83f991c4c02710588eaa6a94100d';b=read(B);bp=read(BP)
assert set(c)-set(b)==set(p)-set(bp)=={'current64_owner_identity'}and set(b)-set(c)==set(bp)-set(p)==set()
rev=copy.deepcopy(c);revp=copy.deepcopy(p);overlay=rev.pop('current64_owner_identity');overlayp=revp.pop('current64_owner_identity');assert overlay==overlayp and rev==b and revp==bp
assert (json.dumps(rev,indent=2,ensure_ascii=False)+'\n').encode()==B.read_bytes()and (json.dumps(revp,indent=2,ensure_ascii=False)+'\n').encode()==BP.read_bytes()
assert checked(overlay['original_installed28_ledger']).read_bytes()==B.read_bytes()and checked(overlay['original_installed28_promotions']).read_bytes()==BP.read_bytes()
S=checked(o['identity_sidecar']);side=read(S);assert checked(overlay['identity_sidecar'])==S;assert side['errors']==[]and side['semantic_review_redecided']is False and side['changed_owned_literals']==[]and side['new_proof_sources']==side['new_mathematical_decisions']==0
old=read(checked(side['historical_inventory']));N=R/'book/coverage/inventory-after-correction64.json';assert sha(N)==o['inventory_sha256']==overlay['inventory_sha256']=='11136add476e6b5be58f4bc6ea038602d51016a7e8370eeb67e17e9358893f98';assert loc(o['inventory'])==N;new=read(N);scope=set(b['scope_pages']);assert len(scope)==3 and b['source_sha256']==o['source_sha256']==side['owned_source_sha256_unchanged']=={n:new['source_sha256'][n]for n in scope}=={n:old['source_sha256'][n]for n in scope}
for section,count in [('exercises',128),('material_source_units',2059)]:
 a={x['key']:x for x in old[section]if x['source']in scope};z={x['key']:x for x in new[section]if x['source']in scope};assert a==z and len(z)==count
assert len(c['exercises'])==128 and sum(len(e['claims'])for e in c['exercises'])==468 and len(c['material_claims'])==1954 and len(c['proof_files'])==312
assert o['counts']==b['counts']and o['proof_files']=={}and o['new_actual_paired_records']==o['new_material_keys']==o['new_exercises']==[]
assert overlay['inventory']==o['inventory']and overlay['changed_owned_literals']==[]and overlay['new_proof_sources']==overlay['new_mathematical_decisions']==0
prior=read(checked(o['original_reviewed_current60_offer']));assert prior['status']=='independently_reviewed_isolated_applied28_current60_identity_offer'and prior['errors']==[]and checked(prior['candidate']).read_bytes()==B.read_bytes()and checked(prior['candidate_promotions']).read_bytes()==BP.read_bytes();assert o['original_complete_independent_peer']==prior['original_complete_independent_peer']
oldpeer=read(checked(o['original_complete_independent_peer']));assert oldpeer['errors']==[]and oldpeer['status'].startswith('passed_')
app=read(checked(overlay['actual_source61_to64_application']));assert app['selected28_proof_sources_unchanged']==1186 and app['five_installed28_owner_ledgers_unchanged']is True and [x['correction_id']for x in app['applications']]==[61,62,63,64]and all(x['source_after']['file']not in scope for x in app['applications'])
native=read(checked(o['actual_isolated_candidate_preparation']));assert type(native['actual_exit_code'])is int and native['actual_exit_code']==0 and native['protection_errors']==[]and native['live_owner_or_source_or_publication_written']is False;assert native['actual_command']==['python3',o['candidate_builder']['file']]and native['actual_workdir']==str(R)and native['helper_sha256_before']==native['helper_sha256_after']
assert sha(loc(native['log']))==native['log_sha256'];checked(o['candidate_builder']);checked(o['actual_preparation_runner'])
for name,h in native['helper_sha256_after'].items():assert sha(loc(name))==h
assert o['actual_finalizer']==o['actual_isolated_candidate_preparation']and native['actual_source64_installed28_context']['sha256']=='442590b45444a97af4b12a37b9ee3f6166b6118a85516e339c6d55bb0c33c6e0'
assert len(o['required_evidence_artifacts_sha256'])==252
for n,h in o['required_evidence_artifacts_sha256'].items():assert sha(loc(n))==h,n
assert len(o['original_closed_byte_aliases'])==230
for original,r in o['original_closed_byte_aliases'].items():checked(r)
assert {k:v for k,v in prior['required_evidence_artifacts_sha256'].items()}=={k:o['required_evidence_artifacts_sha256'][k]for k in prior['required_evidence_artifacts_sha256']}
assert prior['original_closed_byte_aliases']==o['original_closed_byte_aliases']
refs={};aliases={}
def bind(path):
 p=loc(str(path));h=sha(p);dst=D/'original-closed-bytes'/h/p.name;dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists():assert dst.read_bytes()==p.read_bytes()
 else:dst.write_bytes(p.read_bytes())
 ref={'file':str(dst.relative_to(R)),'sha256':h,'bytes':dst.stat().st_size};refs[ref['file']]=h;aliases[str(p)]=ref;return ref
out={'status':'passed_independent_exact_applied29_current64_identity_only_candidate_mechanics','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':bind(C),'candidate_promotions':bind(P),'offer':bind(O),'original_candidate_sha256':o['candidate']['sha256'],'original_promotions_sha256':o['candidate_promotions']['sha256'],'original_offer_sha256':sha(O),'exact_only_added_field_to_both_candidates':'current64_owner_identity','exact_inverse_recovers_entire_raw_installed28_ledger_and_promotions_bytes':True,'all128_exercise_records_468_claims_1954_material_rows_312_proof_metadata_records_and_all_hypotheses_declarations_review_body_times_unchanged':True,'all128_owned_exercise_and2059_owned_material_source_records_entire_equal_between60_and64':True,'all3_owned_page_hashes_unchanged':True,'all252_offer_closure_hashes_and230_inherited_original_aliases_physically_checked':True,'new_proof_sources':0,'new_mathematical_or_status_decisions':0,'original_complete_independent_current60_peer':o['original_complete_independent_peer'],'original_current60_full_semantic_decisions_and_native_body_times_retained_without_redecision':True,'actual_author_preparation':bind(checked(o['actual_isolated_candidate_preparation'])),'actual_author_log':bind(loc(native['log'])),'author_native_original_commands_codes_helper_maps_body_and_times_verified':True,'identity_sidecar':bind(S),'identity_integrity':bind(checked(o['identity_integrity'])),'builder':bind(checked(o['candidate_builder'])),'preparation_runner':bind(checked(o['actual_preparation_runner'])),'all1186_current64_31assets_and_five_owners_held_by_actual_reader_wrapper':True,'no_compiler_source_owner_canonical_selection_or_publication_mutation':True,'canonical_durable_candidate_ref_rebinding_remains_author_future_step':True,'coverage_complete':False,'required_evidence_artifacts_sha256':refs,'original_closed_byte_aliases':aliases}
q=D/'applied29-current64-identity-independent-modules29-peer-v1.json';q.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'peer':str(q.relative_to(R)),'sha256':sha(q),'bytes':q.stat().st_size,'checked_closure_refs':252,'checked_aliases':230}))

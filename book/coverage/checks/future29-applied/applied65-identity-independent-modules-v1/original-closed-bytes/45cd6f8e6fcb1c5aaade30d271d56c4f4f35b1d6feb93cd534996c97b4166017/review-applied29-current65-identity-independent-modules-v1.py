from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future29-applied/applied65-identity-independent-modules-v1';assert not D.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_bytes())
def P(n):p=Path(n);return p if p.is_absolute()else R/p
def check(v):p=P(v['file']);assert H(p)==v['sha256'];return p
def ref(p):return {'file':Path(p).relative_to(R).as_posix(),'sha256':H(p)}
O=Path('/tmp/applied29-current65-identity-v2/applied29-current65-identity-offer-draft-v2.json');assert H(O)=='b7a493754d8490485066be5b8ae2b8e5548b638da9c10f509928ed8a0d81299a';o=J(O);assert o['errors']==[]and o['proof_files']=={}and o['coverage_complete']is False
C=check(o['candidate']);CP=check(o['candidate_promotions']);c,p=J(C),J(CP);oldoffer=J(check(o['original_current64_offer']));C64=check(oldoffer['candidate']);P64=check(oldoffer['candidate_promotions']);c64,p64=J(C64),J(P64)
assert set(c)-set(c64)==set(p)-set(p64)=={'current65_owner_identity'}and set(c64)<=set(c)and set(p64)<=set(p)
rev,revp=copy.deepcopy(c),copy.deepcopy(p);overlay=rev.pop('current65_owner_identity');overlayp=revp.pop('current65_owner_identity');assert overlay==overlayp and rev==c64 and revp==p64
assert (json.dumps(rev,ensure_ascii=False,indent=2)+'\n').encode()==C64.read_bytes()and(json.dumps(revp,ensure_ascii=False,indent=2)+'\n').encode()==P64.read_bytes()
rev.pop('current64_owner_identity');revp.pop('current64_owner_identity');assert(json.dumps(rev,ensure_ascii=False,indent=2)+'\n').encode()==(R/'book/coverage/applied.json').read_bytes()and(json.dumps(revp,ensure_ascii=False,indent=2)+'\n').encode()==(R/'book/coverage/applied-promotions.json').read_bytes()
peer=check(o['original_entire_current64_independent_peer_body_and_time']);assert H(peer)=='9d6d456662042ca629c4589fc7865c0c1e5cf0f0befbbac44038de7157d09f2b'and J(peer)['errors']==[]and o['original_complete_independent_peer']==oldoffer['original_complete_independent_peer']
side=J(check(o['identity_sidecar']));assert side['errors']==[]and side['semantic_review_redecided']is False and side['changed_owned_literals']==[]and side['new_proof_sources']==side['new_mathematical_decisions']==0
oldinv,newinv=J(check(side['historical_inventory'])),J(check(side['current_inventory']));assert H(check(side['current_inventory']))==o['inventory_sha256']=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68';scope=set(c['scope_pages']);assert len(scope)==3 and c['source_sha256']==o['source_sha256']=={n:newinv['source_sha256'][n]for n in scope}=={n:oldinv['source_sha256'][n]for n in scope}
for section,count in [('exercises',128),('material_source_units',2059)]:
 a={x['key']:x for x in oldinv[section]if x['source']in scope};b={x['key']:x for x in newinv[section]if x['source']in scope};assert a==b and len(a)==count
assert len(c['exercises'])==128 and sum(len(e['claims'])for e in c['exercises'])==468 and len(c['material_claims'])==1954 and len(c['proof_files'])==312 and c['counts']==c64['counts']==o['counts']
assert o['new_actual_paired_records']==o['new_material_keys']==o['new_exercises']==[]
app=J(check(side['actual_source65_application']));assert app['selected28_proof_sources_unchanged']==1186 and app['five_owner28_ledgers_unchanged']is True
native=J(check(o['actual_finalizer']));assert native['actual_exit_code']==0 and native['protection_errors']==[]and native['actual_command']==['python3','/tmp/prepare-applied29-current65-identity-overlay-v2.py']and native['actual_workdir']==str(R)and native['helper_sha256_before']==native['helper_sha256_after']and H(P(native['log']))==native['log_sha256']
for n,h in native['helper_sha256_after'].items():assert H(P(n))==h
assert native['actual_source65_installed28_context']['sha256']=='10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78'
for n,h in o['required_evidence_artifacts_sha256'].items():assert H(P(n))==h,n
for n,a in o['original_closed_byte_aliases'].items():check(a)
assert len(o['required_evidence_artifacts_sha256'])==287 and len(o['original_closed_byte_aliases'])==243
failed=J(check(side['original_author1_prewrite_schema_failure']['actual']));assert failed['actual_exit_code']==1
ctx=J('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
for n,h in {**ctx['pins_sha256'],**ctx['held_current_source_sha256']}.items():assert H(P(n))==h,n
D.mkdir(parents=True);out={'status':'passed_independent_exact_applied29_current65_identity_only_candidate_mechanics','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':o['candidate'],'candidate_promotions':o['candidate_promotions'],'offer':{'file':str(O),'sha256':H(O)},'original_entire_current64_independent_peer_body_and_time':o['original_entire_current64_independent_peer_body_and_time'],'exact_only_added_field_to_both_candidates':'current65_owner_identity','exact_inverse_recovers_both_entire_raw_approved64_original_bytes_then_both_installed28_original_bytes':True,'all128_exercises_468claims_1954material_rows_312proof_metadata_body_statuses_hypotheses_declarations_review_times_unchanged':True,'all128_owned_exercises_and2059_owned_material_inventory_records_entire_equal64_to65':True,'all3_owned_page_source_fingerprints_exact':True,'all287_closure_hashes_and243_original_aliases_checked':True,'author1_true_prewrite_alias_bytes_schema_failure_and_author2_zero_native_body_log_commands_helpers_times_preserved':True,'new_proof_sources':0,'new_mathematical_or_status_decisions':0,'original64_semantic_review_redecided':False,'no_compiler_source_owner_canonical_selection_or_publication_mutation':True,'durable_candidate_rebinding_remains_author_future_step':True,'actual_finalizer':None,'coverage_complete':False}
q=D/'applied29-current65-identity-independent-modules29-peer-v1.json';q.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':ref(q),'candidate':o['candidate'],'promotions':o['candidate_promotions'],'status':out['status']}))

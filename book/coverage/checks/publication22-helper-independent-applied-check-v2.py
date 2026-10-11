from pathlib import Path
from datetime import datetime, timezone
import ast, copy, hashlib, json

ROOT=Path('/home/oxrexkevin/SafetyBased')
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p: json.loads(p.read_text())
check=Path(__file__)
out=ROOT/'book/coverage/checks/publication22-helper-independent-applied-review-v2.json'
old=ROOT/'book/coverage/checks/publication22-helper-independent-applied-review-v1.json'
main1=ROOT/'book/coverage/checks/root_prepare_and_stage_publication22_v1.py'
main2=ROOT/'book/coverage/checks/root_prepare_and_stage_publication22_v2.py'
conf1=ROOT/'book/coverage/checks/root_prepare_pages22_config_v1.py'
conf2=ROOT/'book/coverage/checks/root_prepare_pages22_config_v2.py'
assert not out.exists()
assert sha(main1)=='63d273dffcd8797a059fdd3170668d13cca63fc7d172571130ef03cbb5f01954'
assert sha(main2)=='9cd7262173790ce37bd45639f480d0963fd731333a7f6c85eaacb92a25bf1e7b'
assert sha(conf2)=='c79e18cd7a3f724f04003b3d7ce3793d13cbb141475f693f9a5c61a3527e9867'
assert sha(old)=='a8b29b0944857e584cdd7d199aed3d7161ac9ef05a3690b1a118d9b99296134d'
oldbody=read(old)
assert oldbody['helper_sha256']==sha(main1) and oldbody['errors']==[]
for p in (main1,main2,conf1,conf2): ast.parse(p.read_text())
normalized=main2.read_text()
for a,b in [
 ('root_prepare_and_stage_publication22_v2.py','root_prepare_and_stage_publication22_v1.py'),
 ('publication22-helper-independent-applied-review-v2.json','publication22-helper-independent-applied-review-v1.json'),
 ('pages22-config-preparation-v2.json','pages22-config-preparation-v1.json'),
 ('pages22-config-previous-original-v2.yml','pages22-config-previous-original-v1.yml'),
 ('pages22-config-execution-v2.json','pages22-config-execution-v1.json'),
 ('pages22-config-execution-v2.log','pages22-config-execution-v1.log'),
 ('root_prepare_pages22_config_v2.py','root_prepare_pages22_config_v1.py')]: normalized=normalized.replace(a,b)
addition="extras.update({'book/coverage/checks/root_prepare_pages22_config_v1.py', 'reports/full-coverage/pages22-config-execution-v1.json', 'reports/full-coverage/pages22-config-execution-v1.log'})\nassert read(REPORTS/'pages22-config-execution-v1.json')['actual_exit_code']==1\nassert read(REPORTS/'pages22-config-execution-v1.json')['actual_exit_code']==0\n"
assert normalized.count(addition)==1
assert normalized.replace(addition,'')==main1.read_text()
manifest_path=ROOT/'reports/full-coverage/checkpoint-22-manifest.json'
manifest=read(manifest_path)
assert manifest['status']=='formal_verification_passed_partial_coverage'
selection_path=ROOT/'reports/full-coverage/checkpoint-22-selection.json'
selection=read(selection_path)
assert sha(selection_path)==manifest['selection_sha256'] and selection['proof_file_count']==1113
audit_path=ROOT/'reports/full-coverage/lean-checkpoint-22/verification-original.json'
audit=read(audit_path)
assert audit['status']=='passed' and audit['proof_file_count']==1113 and audit['theorem_count']==9002
assert all(x['exit_code']==0 for x in audit['checks'])
baseline=read(ROOT/'reports/full-coverage/checkpoint-21-selection.json')
assert len(baseline['proof_files'])==1089
for name,row in baseline['proof_files'].items():
 assert sha(ROOT/name)==sha(ROOT/'reports/full-coverage/checkpoint-22'/name)==row['sha256']==manifest['proof_files'][name]['sha256']
removed=[
 'verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean',
 'verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean',
 'verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean']
owner_rows={}
for owner in ('core','foundations','applied','modules'):
 name='book/coverage/'+owner+'.json'; current=ROOT/name; snapshot=ROOT/'reports/full-coverage/checkpoint-22'/name; published=ROOT/'reports/book/publication-repo'/name
 assert sha(current)==manifest['working_inputs_sha256'][name]
 assert sha(snapshot)==sha(published)==manifest['frozen_inputs_sha256'][name]
 w=read(current); s=read(snapshot); excluded=manifest['excluded_unreferenced_ledger_metadata'][owner]
 assert excluded==(removed if owner=='applied' else [])
 assert set(w['proof_files'])-set(manifest['proof_files'])==set(excluded)
 normalized=copy.deepcopy(w); listed=normalized['proof_files']
 normalized['proof_files']=([n for n in listed if n not in excluded] if isinstance(listed,list) else {n:v for n,v in listed.items() if n not in excluded})
 if 'proof_sha256' in normalized:
  assert set(normalized['proof_sha256'])-set(manifest['proof_files'])<=set(excluded)
  normalized['proof_sha256']={n:v for n,v in normalized['proof_sha256'].items() if n not in excluded}
 assert normalized==s
 assert {k:v for k,v in w.items() if k not in ('proof_files','proof_sha256')}=={k:v for k,v in s.items() if k not in ('proof_files','proof_sha256')}
 owner_rows[owner]={'working_sha256':sha(current),'frozen_published_sha256':sha(snapshot),'excluded_unreferenced_metadata':excluded,'all_claim_review_and_other_fields_exact':True}
reports=ROOT/'reports/full-coverage'
failure_path=reports/'pages22-config-execution-v1.json'; failure=read(failure_path)
success_path=reports/'pages22-config-execution-v2.json'; success=read(success_path)
assert failure['actual_exit_code']==1 and success['actual_exit_code']==0
for p,j,helper in ((failure_path,failure,conf1),(success_path,success,conf2)):
 assert j['helper_sha256_before']==j['helper_sha256_after']=={helper.relative_to(ROOT).as_posix():sha(helper)}
 assert sha(ROOT/j['log'])==j['log_sha256']
 assert j['selection_sha256']==sha(selection_path)
assert not (reports/'pages22-config-previous-original-v1.yml').exists()
assert not (reports/'pages22-config-preparation-v1.json').exists()
prep_path=reports/'pages22-config-preparation-v2.json'; prep=read(prep_path)
assert prep['actual_helper_sha256']==sha(conf2)
assert prep['excluded_unreferenced_ledger_metadata']==manifest['excluded_unreferenced_ledger_metadata']
assert prep['actual22_proof_file_count']==1113 and prep['coverage_complete'] is False
assert prep['config_sha256']==sha(ROOT/'reports/book/publication-repo/_config.yml')
assert prep['previous_config_sha256']==sha(ROOT/prep['previous_config'])=='410746b5dbe55b9f760aeabd0939dfc791bfcf59a598b4e7f3d84e1381999bc2'
assert prep['included_file_bytes']<900000000 and prep['excluded_count']==len(prep['exclusions'])==52
assert len(prep['exact_current48_assets'])==31
for name,digest in prep['exact_current48_assets'].items(): assert sha(ROOT/name)==sha(ROOT/'reports/book/publication-repo'/name)==digest==manifest['frozen_inputs_sha256'][name]
for name,digest in prep['required_published_sha256'].items(): assert sha(ROOT/'reports/book/publication-repo'/name)==digest
record={
 'status':'passed_independent_read_only_publication22_v2_helper_and_narrow_config_preparer_review',
 'reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'helper':main2.relative_to(ROOT).as_posix(),'helper_sha256':sha(main2),'errors':[],
 'helper_was_not_executed_by_reviewer':True,'no_git_staging_commit_or_push_performed_by_reviewer':True,
 'original_v1_review':{'file':old.relative_to(ROOT).as_posix(),'sha256':sha(old),'original_reviewed_at_utc':oldbody['reviewed_at_utc'],'entire_original_body_preserved':True},
 'original_v1_helper':{'file':main1.relative_to(ROOT).as_posix(),'sha256':sha(main1)},
 'exact_narrow_main_diff':['Versioned self and peer references','Versioned config preparer/preparation/previous/execution references','Preserve the exact failed configv1 helper/JSON/log','Require actual configv1 exit1 and configv2 exit0'],
 'main_normalizes_byte_exactly_to_original_v1':True,
 'config_preparer':{'file':conf2.relative_to(ROOT).as_posix(),'sha256':sha(conf2),'scope':'Only separates manifest-pinned working owner bytes from frozen published bytes and checks exact JSON equality after removal of the three manifest-pinned unreferenced Applied proof metadata entries. No claims, hypotheses, source/review decisions, times, or other owner fields change. Versioned preservation/config metadata are added.','owner_exact_normalizations':owner_rows},
 'actual_config_v1_failure':{'file':failure_path.relative_to(ROOT).as_posix(),'sha256':sha(failure_path),'actual_exit_code':1,'log':failure['log'],'log_sha256':failure['log_sha256'],'failed_before_previous_or_preparation_outputs':True},
 'actual_config_v2_success':{'file':success_path.relative_to(ROOT).as_posix(),'sha256':sha(success_path),'actual_exit_code':0,'log':success['log'],'log_sha256':success['log_sha256'],'preparation':prep_path.relative_to(ROOT).as_posix(),'preparation_sha256':sha(prep_path)},
 'actual_aggregate22':{'file':audit_path.relative_to(ROOT).as_posix(),'sha256':sha(audit_path),'status':'passed','proof_file_count':1113,'public_theorem_count':9002,'all_actual_check_exits_zero':True},
 'manifest':{'file':manifest_path.relative_to(ROOT).as_posix(),'sha256':sha(manifest_path)},
 'counts':{'baseline21_sources_preserved_and_rehashed':1089,'actual22_sources':1113,'actual22_public_theorems':9002,'source48_assets_rehashed':31,'excluded_metadata_only_entries':3,'config_exclusions':52},
 'preserved_safety_guards':oldbody['code_review'],
 'future_source_scope':oldbody['future_source_scope'],
 'remaining_execution_scope':'This peer executes only its read-only checker. Root must execute the approved staging helper separately and bind the independent actual config/output peer, real staging result and subsequent deployment. The original v1 scaffold review and its earlier pending-audit statement remain historical and are not rewritten.',
 'actual_checker':str(check),'actual_checker_sha256':sha(check),'coverage_complete':False}
with out.open('x') as f: f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'passed','report':str(out.relative_to(ROOT)),'sha256':sha(out),'helper_sha256':sha(main2),'config_helper_sha256':sha(conf2),'counts':record['counts']}))

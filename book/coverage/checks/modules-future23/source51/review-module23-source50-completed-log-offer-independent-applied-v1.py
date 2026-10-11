from pathlib import Path
import json,hashlib,copy
from datetime import datetime,timezone
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future23/source50'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def P(p):
 p=Path(p);return p if p.is_absolute() else R/p
ref=lambda p:{'file':str(Path(p).relative_to(R)) if Path(p).is_relative_to(R) else str(p),'sha256':H(p)}
a=B/'modules-audit23-candidate-source50-additions-v1-reviewed.json';b=B/'modules-audit23-candidate-source50-additions-v2-reviewed.json'
assert H(a)=='6877a893c909451b36949f23df5619d538c1cf3fc238d5f90316b8dd5f16f7f7'
assert H(b)=='444f4a5eaf2e159e7b21eaa08abad326aba562420a5b1ab50d8dd328d47f0e54'
x=json.loads(a.read_text());y=json.loads(b.read_text());c=y['completed_preparation_log_binding_correction']
log=B/'module23-source50-reviewed-offer-preparation-actual-v1.log';record=B/'module23-source50-reviewed-offer-preparation-actual-v1.json';obs=B/'modules23-source50-successful-independent-tool-result-observation-v1.json'
key=str(log.relative_to(R));empty=hashlib.sha256(b'').hexdigest()
assert x['required_evidence_artifacts_sha256'][key]==empty
assert y['required_evidence_artifacts_sha256'][key]==H(log)=='36718a29e5fb86cc46a915ccd36714d3edcda0547f4f99ab4bb3cd4f7c4210aa'
added={str(record.relative_to(R)),str(obs.relative_to(R))}
assert set(y['required_evidence_artifacts_sha256'])-set(x['required_evidence_artifacts_sha256'])==added
assert set(x['required_evidence_artifacts_sha256'])<=set(y['required_evidence_artifacts_sha256'])
for k in x['required_evidence_artifacts_sha256']:
 if k!=key:assert x['required_evidence_artifacts_sha256'][k]==y['required_evidence_artifacts_sha256'][k],k
rev=copy.deepcopy(y);rev['required_evidence_artifacts_sha256']=copy.deepcopy(x['required_evidence_artifacts_sha256']);del rev['completed_preparation_log_binding_correction'];assert rev==x
for k,v in y['required_evidence_artifacts_sha256'].items():assert H(P(k))==v,k
actual=json.loads(record.read_text());assert actual['actual_exit_code']==0 and actual['log_sha256']==H(log)
helper=P(actual['actual_command'][1]);assert H(helper)==actual['actual_checker_sha256_before']==actual['actual_checker_sha256_after']
ob=json.loads(obs.read_text());assert ob['actual_exit_code']==0 and ob['actual_exec_tool_chunk_id']=='c97c88' and ob['actual_completion_tool_chunk_id']=='432018' and ob['actual_exec_session_id']==38812
assert not any(k in ob for k in ['started_at_utc','finished_at_utc','elapsed_seconds'])
prior=P(y['independent_final_candidate_mapping_peer']['file']);assert H(prior)==y['independent_final_candidate_mapping_peer']['sha256']=='01def97eceb62e65e172da12ba8b7d8ab759ddbd8568b514b26ef379ed13c26a'
assert H(P(y['module_ledger']))==y['module_ledger_sha256']=='8cb3ecf6c7f4f82da069c3c0d862297e7bbcbc6468d8550e11b2335ecc1cf8d1'
corrp=Path('/tmp/module23-source50-completed-log-offer-correction-actual-v1.json');corr=json.loads(corrp.read_text());assert corr['actual_exit_code']==0
assert H(P(corr['log']))==corr['log_sha256'];assert H(P(corr['actual_command'][1]))==corr['actual_checker_sha256_before']==corr['actual_checker_sha256_after']
manifest=R/'reports/full-coverage/checkpoint-22-manifest.json';m=json.loads(manifest.read_text());assert len(m['proof_files'])==1113
for k,v in m['proof_files'].items():assert H(R/k)==v['sha256'],k
held={'core.json':'3e7c69fb9a0978c914df20835bed3b2aee2b742702bb07caa6d9d582a16251f7','modules.json':'0ebe910d6d8d9a84338727988c5d415746c3f1f624d6958997bea89645d4b06c','foundations.json':'305229a7e1df78c23bc1af728c7f3f4e0ac09d13c55e4e687fe721160b43bf88','applied.json':'0ee60f1f224d01f443a762e0427d4527d6bd9b1d3ae5ed1d893c67750e331d20'}
for n,v in held.items():assert H(R/'book/coverage'/n)==v,n
report={'status':'passed_independent_evidence_only_offer_correction_review','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/applied_next','errors':[], 'original_offer':ref(a),'new_active_offer':ref(b),'entire_original_offer_recovered_by_exact_reverse_normalization':True,'only_changes':['One required completed raw-log digest replaces the captured empty-log digest.','Two actual completed execution/observed-result evidence references are appended.','Explicit completion-binding correction provenance is appended.'],'all104_current_required_artifact_hashes_verified':len(y['required_evidence_artifacts_sha256']),'candidate_statuses_mathematics_hypotheses_original_review_bodies_and_times_unchanged':True,'entire_prior_peer':json.loads(prior.read_text()),'completed_preparation_actual_execution':ref(record),'completed_raw_log':ref(log),'successful_independent_checker_tool_result_observation':ref(obs),'genuine_isolated_correction_execution':ref(corrp),'genuine_isolated_correction_log':ref(P(corr['log'])),'genuine_isolated_correction_helper':ref(P(corr['actual_command'][1])),'historical_empty_digest_preserved_in_original_offer':True,'protected_selected22':{'manifest':ref(manifest),'proof_source_count':1113,'all_actual_hashes_matched':True},'held_working22_ledgers':held,'actual_checker':ref(Path(__file__)),'scope':'Mechanical evidence closure only. No semantic review, compiler rerun, live ledger build, owner installation, global validator or aggregate23 claim.'}
p=Path('/tmp/modules23-source50-completed-log-offer-independent-applied-confirmation-v1.json');assert not p.exists();p.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'peer':ref(p),'status':'passed','required_artifacts':len(y['required_evidence_artifacts_sha256'])}))

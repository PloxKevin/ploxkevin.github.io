from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/modules-future27/source55'
P=Path('/tmp/modules27-current55-final-canonical-mapping-independent-foundations-confirmation-v1.json')
D=BASE/'modules-audit27-candidate-current55-additions-draft-v1.json'
O=BASE/'modules-audit27-candidate-current55-additions-v1-reviewed.json'
F=BASE/'original-final-canonical-candidate-independent-foundations-peer-v1'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
def check(r):
 p=Path(r['file']);p=p if p.is_absolute() else ROOT/p
 assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'];return p
assert sha(P)=='9b080392cac79851639a76307a94c73c2d289f3326b2315a8d6409f29c9e8f0e'
peer=json.loads(P.read_bytes());assert peer['status']=='passed' and peer['errors']==[]
assert not O.exists() and not F.exists() and sha(D)=='5bd5b8198fe0e2b4a817a714d97dc38645185bf55443ca69de284da331670dc9'
old=json.loads(D.read_bytes());assert peer['offer']==ref(D) and peer['candidate']==old['candidate'] and peer['candidate_interface']==old['candidate_interface']
assert old['counts']=={'new_sources':4,'new_public_exports':87,'whole_exercises':2,'whole_material_units':8}
actualp=check(peer['actual_candidate_builder_execution']);actual=json.loads(actualp.read_bytes());assert type(actual['actual_exit_code']) is int and actual['actual_exit_code']==0
assert actual['helper_sha256_before']==actual['helper_sha256_after']=={old['candidate_builder']['file']:old['candidate_builder']['sha256']}
assert actual['actual_workdir']==str(ROOT) and actual['actual_command'][:2]==['python3',old['candidate_builder']['file']]
builder_log=check({'file':actual['log'],'sha256':actual['log_sha256']})
inputs={str(P):sha(P),**peer['closed_evidence_sha256']}
assert len(inputs)==6
failure_path=BASE/'modules27-current55-reviewed-offer-finalization-actual-v1.json';failure=json.loads(failure_path.read_bytes());assert type(failure['actual_exit_code']) is int and failure['actual_exit_code']==1
for fp in [ROOT/'book/coverage/checks/finalize_modules27_current55_reviewed_offer_v1.py',Path('/tmp/run-finalize-modules27-current55-reviewed-offer-actual-v1.py'),failure_path,Path(failure['raw_log'])]:inputs[str(fp)]=sha(fp)
assert sha(Path(failure['raw_log']))==failure['raw_log_sha256']
for n,h in inputs.items():assert sha(Path(n))==h
for n,h in old['required_evidence_artifacts_sha256'].items():check({'file':n,'sha256':h})
held={n:sha(ROOT/n) for n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/applied-promotions.json','book/coverage/modules.json']}
assert sha(ROOT/'book/coverage/inventory.json')==old['inventory_sha256']
F.mkdir();aliases={}
for n,h in inputs.items():
 src=Path(n);dest=F/src.name;assert not dest.exists();dest.write_bytes(src.read_bytes());assert sha(dest)==h;aliases[n]=ref(dest)
cat=F/'original-closed-byte-aliases-v1.json';cat.write_text(json.dumps({'status':'passed_exact_original_peer_and_prior_actual_finalizer_failure_bytes','original_closed_byte_aliases':aliases,'scope':'Original independent bodies and times retained exactly; canonical aliases only.'},indent=2)+'\n')
new=copy.deepcopy(old)
new['status']='independently_reviewed_isolated_current55_modules27_candidate_ready_for_root_copy'
new['final_independent_candidate_mapping_peer']=aliases[str(P)]
new['actual_isolated_candidate_preparation']=peer['actual_candidate_builder_execution']
new['entire_original_final_candidate_mechanics_peer_body_and_time']=peer
new['preserved_original_reviewed_offer_finalizer1_failure']=failure
new['reviewed_offer_finalizer_delta']='Native builder hashes are an exact one-key map and log names are relative log/log_sha256; reader1 failure preserved before any copies.'
new['final_candidate_mapping_original_byte_aliases']=ref(cat)
new['actual_isolated_candidate_preparation_raw_log']=ref(builder_log)
new['reviewed_offer_finalization27']={'finalized_at_utc':datetime.now(timezone.utc).isoformat(),'original_draft_offer':ref(D),'original_status':old['status'],'original_final_independent_candidate_mapping_peer':old['final_independent_candidate_mapping_peer'],'original_actual_isolated_candidate_preparation':old['actual_isolated_candidate_preparation'],'original_required_evidence_artifacts_sha256':old['required_evidence_artifacts_sha256'],'original_additional_frozen_inputs':old['additional_frozen_inputs'],'finalizer_helper':ref(Path(__file__)),'candidate_or_mathematical_body_changes':False,'owner_installation_claimed':False}
for r in list(aliases.values())+[ref(cat),ref(D),ref(Path(__file__)),ref(actualp),ref(builder_log)]:new['required_evidence_artifacts_sha256'][r['file']]=r['sha256']
new['additional_frozen_inputs']=copy.deepcopy(new['required_evidence_artifacts_sha256'])
inverse=copy.deepcopy(new);meta=inverse.pop('reviewed_offer_finalization27')
for k in ['status','final_independent_candidate_mapping_peer','actual_isolated_candidate_preparation','required_evidence_artifacts_sha256','additional_frozen_inputs']:inverse[k]=copy.deepcopy(meta['original_'+k])
for k in ['entire_original_final_candidate_mechanics_peer_body_and_time','final_candidate_mapping_original_byte_aliases','actual_isolated_candidate_preparation_raw_log','preserved_original_reviewed_offer_finalizer1_failure','reviewed_offer_finalizer_delta']:inverse.pop(k)
assert inverse==old
with O.open('x') as f:f.write(json.dumps(new,indent=2,ensure_ascii=False)+'\n')
for n,h in held.items():assert sha(ROOT/n)==h
assert sha(ROOT/'book/coverage/inventory.json')==old['inventory_sha256'] and sha(check(new['candidate']))==old['mapped_ledger_sha256']
print(json.dumps({'status':'passed_reviewed_offer_finalization_exact_inverse','offer':ref(O),'candidate':new['candidate'],'peer':new['final_independent_candidate_mapping_peer'],'closed_artifacts':len(new['required_evidence_artifacts_sha256'])}))

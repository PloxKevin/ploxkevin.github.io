"""Close the TMP Applied60 offer after the unchanged independent mechanics peer."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json
R=Path('/home/oxrexkevin/SafetyBased')
B=Path('/tmp/applied28-source60-identity-v1')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_bytes())
def path(n):
 p=Path(n);return p if p.is_absolute() else R/p
def ref(p):return {'file':str(p),'sha256':H(p)}
def checked(r):
 assert isinstance(r,dict) and isinstance(r.get('file'),str) and isinstance(r.get('sha256'),str)
 p=path(r['file']);assert H(p)==r['sha256'],str(p);return p
def actual(r):
 p=checked(r);d=J(p);codes=[d[k]for k in ('actual_exit_code','exit_code')if k in d]
 assert codes and all(type(v)is int and v==0 for v in codes)
 if 'log' in d:assert H(path(d['log']))==d['log_sha256']
 return d
D=B/'applied28-source60-identity-additions-draft-v2.json'
P=Path('/tmp/applied60-identity-independent-modules28-closed-v1.json')
assert H(D)=='7f2476de7f7894e6567929a4acf294f5a50ddfb3d31a32e82e3a5332a4d44534'
assert H(P)=='d267fdb10f27fc6cfda1fd5ab7512c15b427831483147539989f6dda9116bd81'
d=J(D);peer=J(P);status='passed_independent_applied28_current60_zero_proof_candidate_mechanics'
assert peer['status']==status and peer['errors']==[] and peer['protection_errors']==[]
assert type(peer['actual_reader_exit_code'])is int and peer['actual_reader_exit_code']==0
assert peer['new_proofs']==peer['new_math_promotions']==0 and peer['coverage_complete']is False
q=peer['reader_decision'];assert q['status']==status and q['errors']==[]
assert q['request']['file']==str(D)and q['request']['sha256']==H(D)
for k in ['candidate','candidate_promotions','candidate_builder','identity_sidecar']:
 assert q[k]==d[k];checked(d[k])
assert q['native_author_preparation']==d['actual_isolated_candidate_preparation']
assert q['original_reviewed55_offer']==d['original_reviewed_source55_offer']
assert q['independent_exact_forward_and_raw_inverse']is True
assert q['all_inherited_evidence_retained_and_read_hashes']==192 and q['all_required_refs_hash_verified']==210
actual(d['actual_isolated_candidate_preparation']);execution=actual(peer['actual_reader_execution'])
assert peer['actual_raw_log']==execution['raw_log'];checked(execution['raw_log']);checked(execution['reader']);assert execution['helper']==peer['helper']and execution['runner']==peer['runner']
assert execution['protection_errors']==[]
assert d['proof_files']=={} and d['new_actual_paired_records']==[] and d['new_material_keys']==[]
closure=copy.deepcopy(d['required_evidence_artifacts_sha256'])
for n,h in closure.items():assert H(path(n))==h,n
assert len(closure)==210
for r in [ref(D),ref(P),peer['actual_reader_execution'],peer['actual_raw_log'],peer['helper'],peer['runner'],execution['reader'],ref(Path(__file__)),ref(Path('/tmp/finalize-applied28-current60-identity-offer-v1.py')),ref(Path('/tmp/run-finalize-applied28-current60-identity-offer-v1.py')),ref(Path('/tmp/applied28-current60-reviewed-offer-finalization-actual-v1.json')),ref(Path('/tmp/applied28-current60-reviewed-offer-finalization-actual-v1.log'))]:
 p=checked(r);n=str(p)
 assert n not in closure or closure[n]==H(p)
 closure[n]=H(p)
sel=J(R/d['base_selection']);assert H(R/d['base_selection'])==d['base_selection_sha256'] and len(sel['proof_files'])==1175
inventory=J(R/d['inventory']);assert H(R/d['inventory'])==d['inventory_sha256']==H(R/'book/coverage/inventory.json')
assets=dict(J(R/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256']);assets.update(inventory['source_sha256']);assert len(assets)==31
protected={n:r['sha256']for n,r in sel['proof_files'].items()};protected.update(assets);protected.update(d['baseline27_owner_sha256'])
def guard():
 for n,h in protected.items():assert H(R/n)==h,n
 for n,h in closure.items():assert H(path(n))==h,n
guard()
out=copy.deepcopy(d);out['status']='independently_reviewed_isolated_applied28_current60_identity_offer'
out['final_independent_candidate_mapping_peer']=ref(P)
out['independent_peer_expected_status']=status
out['independent_peer_actual_execution_pointer']='actual_reader_execution'
out['original_independent_review_body_and_time_preserved_by_exact_ref']=ref(P)
out['original_pre_mechanics_offer']=ref(D)
out['actual_offer_finalizer']=ref(Path(__file__))
out['finalized_at_utc']=datetime.now(timezone.utc).isoformat()
out['required_evidence_artifacts_sha256']=closure
inverse=copy.deepcopy(out)
for k in ['independent_peer_expected_status','independent_peer_actual_execution_pointer','original_independent_review_body_and_time_preserved_by_exact_ref','original_pre_mechanics_offer','actual_offer_finalizer','finalized_at_utc']:inverse.pop(k)
inverse['status']=d['status'];inverse['final_independent_candidate_mapping_peer']=d['final_independent_candidate_mapping_peer'];inverse['required_evidence_artifacts_sha256']=d['required_evidence_artifacts_sha256'];assert inverse==d
F=B/'applied28-current60-identity-offer-reviewed-v2.json';assert not F.exists()
with F.open('x')as f:f.write(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
guard();print(json.dumps({'status':'passed_actual_tmp_applied28_current60_reviewed_offer_finalization','offer':ref(F),'candidate':out['candidate'],'promotions':out['candidate_promotions'],'independent_peer':ref(P),'closed_refs':len(closure),'new_proofs':0,'new_promotions':0,'live_owner_written':False}))

"""Close the unchanged TMP Core60 identity offer with independent actual review."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B=Path('/tmp/core28-current60-identity-v1')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();J=lambda p:json.loads(p.read_bytes());ref=lambda p:{'file':str(p),'sha256':H(p)}
def checked(r):
 p=Path(r['file']);p=p if p.is_absolute()else R/p;assert H(p)==r['sha256'];return p
D=B/'core28-current60-identity-offer-draft-v2.json';P=Path('/tmp/core28-current60-identity-independent-foundations-review-v1.json')
assert H(D)=='dc93c3139da0d07d4708f50de1805e59cd8b3f0607b90fa3ef7556fb258e83a8'and H(P)=='95fc995e2ce0ca0482ea3eb7bcec848ab95c667e72231e4f24acad188bdb0f7b'
d=J(D);peer=J(P);status='passed_independent_exact_forward_inverse_core28_current60_identity_mechanics'
assert peer['status']==status and peer['errors']==[]and peer['candidate']==d['candidate']and peer['offer']==ref(D)
assert peer['identity_sidecar']==d['identity_sidecar']and peer['identity_integrity']==d['identity_integrity']and peer['actual_author_preparation']==d['actual_isolated_candidate_preparation']
assert peer['exact_forward_current60_inventory_binding']is True and peer['exact_inverse_restores_entire_installed27_core']is True
assert peer['new_proof_sources']==peer['new_status_promotions']==0 and peer['whole_exercise18_or_whole737_739_approved']is False
for r in [d['actual_isolated_candidate_preparation'],peer['actual_independent_reader']]:
 a=J(checked(r));assert type(a['actual_exit_code'])is int and a['actual_exit_code']==0
closure=copy.deepcopy(d['required_evidence_artifacts_sha256'])
for n,h in peer['closed_refs_sha256'].items():assert n not in closure or closure[n]==h;closure[n]=h
for r in [ref(D),ref(P),d['candidate'],peer['actual_independent_reader'],peer['actual_independent_reader_raw_log'],peer['independent_checker'],peer['independent_runner'],peer['original_findings'],ref(Path(__file__))]:
 checked(r);assert r['file']not in closure or closure[r['file']]==r['sha256'];closure[r['file']]=r['sha256']
for n,h in closure.items():checked({'file':n,'sha256':h})
sel=J(R/'reports/full-coverage/checkpoint-27-selection.json');inv=J(R/'book/coverage/inventory.json');assert H(R/'book/coverage/inventory.json')==d['inventory_sha256']
assets=dict(J(R/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256']);assets.update(inv['source_sha256']);assert len(assets)==31
owners={r['destination']:r['candidate']['sha256']for r in J(R/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']}
protected={n:r['sha256']for n,r in sel['proof_files'].items()};protected.update(assets);protected.update(owners)
def guard():
 for n,h in protected.items():assert H(R/n)==h,n
 for n,h in closure.items():checked({'file':n,'sha256':h})
guard();out=copy.deepcopy(d);out['status']='independently_reviewed_isolated_core28_current60_identity_offer';out['final_independent_candidate_mapping_peer']=ref(P);out['independent_peer_expected_status']=status;out['independent_peer_actual_finalizer_pointer']=['actual_author_preparation'];out['actual_finalizer']=d['actual_isolated_candidate_preparation'];out['original_pre_mechanics_offer']=ref(D);out['original_independent_review_body_and_time_preserved_by_exact_ref']=ref(P);out['offer_finalizer_helper']=ref(Path(__file__));out['finalized_at_utc']=datetime.now(timezone.utc).isoformat();out['required_evidence_artifacts_sha256']=closure
F=B/'core28-current60-identity-offer-reviewed-v1.json'
with F.open('x')as f:f.write(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
guard();print(json.dumps({'status':'passed_actual_tmp_core28_current60_reviewed_offer_finalization','offer':ref(F),'candidate':out['candidate'],'independent_peer':ref(P),'refs':len(closure),'new_proofs':0,'new_promotions':0,'live_owner_written':False}))

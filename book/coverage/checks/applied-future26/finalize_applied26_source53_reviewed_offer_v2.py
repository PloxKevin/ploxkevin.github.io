from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy
R=Path(__file__).resolve().parents[4];B='book/coverage/checks/applied-future26/source53-v2';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();P=lambda n:Path(n)if Path(n).is_absolute()else R/n;J=lambda n:json.loads(P(n).read_text());ref=lambda n:{'file':n,'sha256':H(P(n))}
def zero(d):
 cs=[d[k]for k in ('actual_exit_code','exit_code')if k in d];assert cs and all(type(x)is int and x==0 for x in cs)
D=B+'/applied-audit26-candidate-source53-additions-draft-v1.json';assert H(P(D))=='18d3353de0cb9e60b8ba02a3eaae4c6849802e2afaaff15cceebe4b57700bb87';o=J(D)
original='/tmp/applied26-source53-identity-independent-modules-confirmation-v1.json';assert H(P(original))=='4179d37bdc87c31d23be65576e2f79aab8259874c892317eb783592930530345';peer=J(original);assert peer['errors']==[] and 'passed'in peer['status'];assert peer['candidate_ledger']==o['candidate']
files=[original,'/tmp/check-foundations-applied26-source53-independent-module-identities-v1.py','/tmp/run-foundations-applied26-source53-identities-independent-modules-actual-v1.py','/tmp/foundations-applied26-source53-identities-independent-modules-actual-v1.json','/tmp/foundations-applied26-source53-identities-independent-modules-actual-v1.log']
aliases={}
for n in files:
 p=P(n);target=P(B+'/original-independent-source53-identity-peer/'+p.name);target.parent.mkdir(parents=True,exist_ok=True);assert not target.exists()
 with target.open('xb')as f:f.write(p.read_bytes())
 assert H(target)==H(p);aliases[n]=ref(str(target.relative_to(R)))
actual=B+'/source53-identity-preparation-actual-v2.json';a=J(actual);zero(a);assert H(P(a['raw_log']))==a['raw_log_sha256'];assert a['helper_sha256_before']==a['helper_sha256_after']==o['candidate_builder']['sha256']
assert H(P(o['mapped_ledger']))==o['mapped_ledger_sha256'] and H(P(o['mapped_promotions']))==o['mapped_promotions_sha256']
interface=B+'/source53-independent-identity-native-peer-interface-v1.json';body={'status':'passed_independent_source53_identity_native_peer_interface','errors':[],'reviewer':peer['reviewer'],'reviewed_at_utc':peer['reviewed_at_utc'],'candidate':peer['candidate_ledger'],'candidate_promotions':peer['candidate_promotions'],'original_native_peer':aliases[original],'entire_original_independent_peer_body_and_time':peer,'immutable_inventory_after':peer['immutable_inventory_after'],'scope':'Transparent candidate_ledger-to-candidate field alias only; entire original independent identity body and time preserved. No semantic redecision or fresh independent execution.'};assert not P(interface).exists();P(interface).write_text(json.dumps(body,indent=2)+'\n')
final=copy.deepcopy(o);updates={'final_independent_candidate_mapping_peer':ref(interface),'original_final_independent_candidate_mapping_peer':ref(original),'independent_review_original_byte_aliases':aliases,'actual_isolated_candidate_preparation':ref(actual),'actual_isolated_candidate_raw_log':ref(a['raw_log'])};oldfields={k:copy.deepcopy(o[k])for k in updates if k in o};newfields=[k for k in updates if k not in o];final.update(updates)
closed={r['file']:r['sha256']for r in aliases.values()};closed.update({actual:H(P(actual)),a['raw_log']:a['raw_log_sha256'],o['candidate_builder']['file']:o['candidate_builder']['sha256'],'book/coverage/checks/applied-future26/run_applied26_source53_identity_actual_v2.py':H(P('book/coverage/checks/applied-future26/run_applied26_source53_identity_actual_v2.py'))})
for k in ('identity_sidecar','identity_integrity'):
 r=o['source53_identity_rebase'][k];closed[r['file']]=r['sha256']
for r in o['preserved_initial_source53_identity_preparation_failure'].values():
 if isinstance(r,dict)and'file'in r:closed[r['file']]=r['sha256']
closed[interface]=H(P(interface))
for name in ['book/coverage/checks/applied-future26/finalize_applied26_source53_reviewed_offer_v1.py',B+'/reviewed-offer-finalization-actual-v1.json',B+'/reviewed-offer-finalization-actual-v1.log']:
 closed[name]=H(P(name))
prior_evidence=copy.deepcopy(o['required_evidence_artifacts_sha256']);prior_extra=copy.deepcopy(o['additional_frozen_inputs']);final['required_evidence_artifacts_sha256']=dict(prior_evidence);final['required_evidence_artifacts_sha256'].update(closed);final['additional_frozen_inputs']=sorted(set(prior_extra)|set(closed))
final['source53_independent_identity_finalization']={'original_draft':ref(D),'original_outer_fields':oldfields,'new_outer_fields':newfields,'original_required_evidence_artifacts_sha256':prior_evidence,'original_additional_frozen_inputs':prior_extra,'entire_original_independent_identity_peer_body_and_time':peer,'preserved_initial_finalizer_native_field_failure':{'helper':ref('book/coverage/checks/applied-future26/finalize_applied26_source53_reviewed_offer_v1.py'),'actual_execution':ref(B+'/reviewed-offer-finalization-actual-v1.json'),'raw_log':ref(B+'/reviewed-offer-finalization-actual-v1.log'),'reason':'Original independent native peer uses candidate_ledger, not candidate. Initial finalizer failed before byte copies or offer write. New finalizer checks exact candidate_ledger and separately preserves a transparent common-field interface.'},'scope':'Final closed peer/actual identity refs only. No mathematical/proof/promotion body or original review time change; original full source52 offer is recoverable through the unchanged identity-rebase inverse.'}
reverse=copy.deepcopy(final);reverse.pop('source53_independent_identity_finalization');reverse.update(oldfields)
for k in newfields:reverse.pop(k)
reverse['required_evidence_artifacts_sha256']=prior_evidence;reverse['additional_frozen_inputs']=prior_extra;assert reverse==o
for n,h in final['required_evidence_artifacts_sha256'].items():assert H(P(n))==h,n
assert H(P('book/coverage/applied.json'))=='0a4ee34e6e3b55391a596c90ea92591eaa6bb3f6a103016c1c01635d225e0a9b'
out=B+'/applied-audit26-candidate-source53-additions-v1-reviewed.json';assert not P(out).exists();P(out).write_text(json.dumps(final,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':'passed','offer':ref(out),'candidate':o['candidate'],'promotions':o['candidate_promotions'],'peer':aliases[original]}))

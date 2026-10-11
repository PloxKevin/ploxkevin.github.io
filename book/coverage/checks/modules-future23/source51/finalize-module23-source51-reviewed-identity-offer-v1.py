from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future23/source51'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());ref=lambda p:{'file':str(Path(p).relative_to(R)),'sha256':H(p)}
def archive(p):
 p=Path(p);q=B/p.name
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:q.write_bytes(p.read_bytes())
 return ref(q)
oldp=R/'book/coverage/checks/modules-future23/source50/modules-audit23-candidate-source50-additions-v2-reviewed.json';assert H(oldp)=='444f4a5eaf2e159e7b21eaa08abad326aba562420a5b1ab50d8dd328d47f0e54';old=J(oldp)
peerp=Path('/tmp/modules23-source51-identity-independent-applied-confirmation-v1.json');assert H(peerp)=='1ffa742014825773202863faae9ddbaab24ca074aeff3a81f7aeedee019e3e4b';peer=J(peerp)
assert peer['errors']==[]
aliases={}
for p in [peerp,Path('/tmp/review-module23-source51-identity-independent-applied-v1.py'),Path('/tmp/modules23-source51-identity-independent-applied-actual-v1.json'),Path('/tmp/modules23-source51-identity-independent-applied-actual-v1.log'),Path('/tmp/modules23-source50-completed-log-offer-independent-applied-confirmation-v1.json'),Path('/tmp/review-module23-source50-completed-log-offer-independent-applied-v1.py'),Path('/tmp/modules23-source50-completed-log-offer-independent-applied-actual-v1.json'),Path('/tmp/modules23-source50-completed-log-offer-independent-applied-actual-v1.log')]:aliases[str(p)]=archive(p)
candidate=B/'modules23-candidate-source51-identity-v1.json';assert H(candidate)=='65e7566b3f3c315ae4cc2297606fe74f8a7136e28d0d4a47ca9cd46fe1b41fbd';c=J(candidate)
exe=B/'modules23-candidate-source51-identity-actual-execution-v3.json';actual=J(exe);assert actual['actual_exit_code']==0 and H(R/actual['log'])==actual['log_sha256']
helper=R/'book/coverage/build_modules23_candidate_source51_identity_v3.py';assert H(helper)==actual['helper_sha256_before']==actual['helper_sha256_after']
out=copy.deepcopy(old);keys=['status','current_inventory','current_inventory_sha256','module_ledger','module_ledger_sha256','module_builder','module_builder_sha256','actual_builder','actual_builder_raw_log','current_identity_binding_validation','independent_final_candidate_mapping_peer','required_evidence_artifacts_sha256']
out.update(status='independently_confirmed_source51_identity_isolated_module23_candidate_ready_for_root_guarded_live_integration',current_inventory=c['current_inventory'],current_inventory_sha256=c['current_inventory_sha256'],module_ledger=ref(candidate)['file'],module_ledger_sha256=H(candidate),module_builder=ref(helper)['file'],module_builder_sha256=H(helper),actual_builder={**ref(exe),'actual_exit_code':0,'execution_kind':'actual_isolated_identity_candidate_builder'},actual_builder_raw_log={'file':actual['log'],'sha256':actual['log_sha256']},current_identity_binding_validation=c['current_identity_binding_validation'],independent_final_candidate_mapping_peer=aliases[str(peerp)])
out['inventory_identity_rebase51']={'original_source50_reviewed_offer':ref(oldp),'original_source50_candidate':c['inventory_identity_rebase51']['original_source50_candidate'],'identity_sidecar':c['inventory_identity_rebase51']['identity_sidecar'],'independent_identity_peer':aliases[str(peerp)],'original_semantic_times_preserved':True,'no_changed_owned_literals':True,'scope':'Only exact current inventory/identity candidate pointers and completed provenance change; seven original approvals/proofs/times remain unchanged.'}
out['source51_identity_copy_aliases']=aliases;out['source51_identity_offer_prepared_at_utc']=datetime.now(timezone.utc).isoformat()
required=out['required_evidence_artifacts_sha256']
closed=[oldp,candidate,helper,B/'unchanged-owned-literal-identity-v1.json',B/'candidate-identity-binding-integrity-v1.json']
closed.extend(R/x['file'] for x in aliases.values())
for version in [1,2,3]:
 closed.extend([B/f'modules23-candidate-source51-identity-actual-execution-v{version}.json',B/f'modules23-candidate-source51-identity-actual-execution-v{version}.log',R/f'book/coverage/build_modules23_candidate_source51_identity_v{version}.py'])
for p in closed:required[ref(p)['file']]=H(p)
reverse=copy.deepcopy(out)
for k in keys:reverse[k]=copy.deepcopy(old[k])
for k in ['inventory_identity_rebase51','source51_identity_copy_aliases','source51_identity_offer_prepared_at_utc']:del reverse[k]
assert reverse==old
for n,d in required.items():assert H(R/n)==d,n
p=B/'modules-audit23-candidate-source51-additions-v1-reviewed.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'offer':ref(p),'candidate':ref(candidate),'scope':'Isolated identity offer only. Required evidence captures only completed commands; this preparation runner/log is not self-enumerated.'}))

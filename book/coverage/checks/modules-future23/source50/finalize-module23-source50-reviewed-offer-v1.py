"""Copy exact peer provenance and prepare a new reversible isolated source50 offer."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
R=Path(__file__).resolve().parents[5]
# Resolve the repository explicitly because this helper resides in a versioned checks directory.
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future23/source50'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());ref=lambda p:{'file':str(Path(p).relative_to(R)),'sha256':H(p)}
oldpath=R/'book/coverage/checks/modules-future23/source49/modules-audit23-candidate-source49-additions-v1-reviewed.json';assert H(oldpath)=='fd9e1e4847135d664cd29c03add3bfd861e32686a3650e3b31a208b20b28bcce';old=J(oldpath)
peerpath=Path('/tmp/modules23-source50-identity-independent-applied-confirmation-v2.json');assert H(peerpath)=='01def97eceb62e65e172da12ba8b7d8ab759ddbd8568b514b26ef379ed13c26a';peer=J(peerpath);assert peer['errors']==[] and peer['exact_inverse_normalization_restores_entire_source49_candidate']
artifacts=[peerpath,Path('/tmp/check-module23-source50-identity-independent-applied-v1.py'),Path('/tmp/check-module23-source50-identity-independent-applied-v2.py'),Path('/tmp/module23-source50-identity-independent-applied-first-checker-failure-observation-v1.json')]
aliases={}
for p in artifacts:
 q=B/p.name
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:q.write_bytes(p.read_bytes())
 aliases[str(p)]=ref(q)
peerref=aliases[str(peerpath)]
candidate=R/peer['current50_candidate']['file'];assert H(candidate)==peer['current50_candidate']['sha256']=='8cb3ecf6c7f4f82da069c3c0d862297e7bbcbc6468d8550e11b2335ecc1cf8d1';c=J(candidate)
assert c['inventory_identity_rebase49']==J(R/old['module_ledger'])['inventory_identity_rebase49']
execution=R/peer['actual_identity_preparation_execution']['file'];ex=J(execution);assert ex['actual_exit_code']==0 and H(execution)==peer['actual_identity_preparation_execution']['sha256'];assert H(R/ex['log'])==ex['log_sha256']
for n,d in old['required_evidence_artifacts_sha256'].items():assert H(R/n)==d
out=copy.deepcopy(old)
changed=['status','current_inventory','current_inventory_sha256','module_ledger','module_ledger_sha256','module_builder','module_builder_sha256','actual_builder','actual_builder_raw_log','current_identity_binding_validation','independent_final_candidate_mapping_peer','required_evidence_artifacts_sha256']
out.update(status='independently_confirmed_source50_identity_isolated_module23_candidate_ready_for_root_guarded_live_integration',current_inventory=c['current_inventory'],current_inventory_sha256=c['current_inventory_sha256'],module_ledger=ref(candidate)['file'],module_ledger_sha256=H(candidate),module_builder=peer['helper']['file'],module_builder_sha256=peer['helper']['sha256'],actual_builder={**ref(execution),'actual_exit_code':0,'execution_kind':'actual_isolated_identity_candidate_builder'},actual_builder_raw_log=peer['actual_identity_preparation_raw_log'],current_identity_binding_validation=peer['identity_guard'],independent_final_candidate_mapping_peer=peerref)
added=['inventory_identity_rebase50','source50_identity_copy_aliases','source50_identity_offer_prepared_at_utc']
out['inventory_identity_rebase50']={'identity_sidecar':peer['identity_sidecar'],'original_source49_reviewed_offer':ref(oldpath),'original_source49_candidate':peer['original49_candidate'],'original_source49_final_candidate_mapping_peer':old['independent_final_candidate_mapping_peer'],'actual_isolated_identity_builder':ref(execution),'independent_identity_peer':peerref,'semantics_and_original_review_times_preserved':True,'no_changed_owned_literals':True,'scope':'Only current inventory/candidate identity pointers and provenance metadata change. Original source48 full semantic peer and all source49 identity layers remain unchanged. No live ledger installation, mathematical compilation, new semantic review or aggregate23 claim.'}
out['source50_identity_copy_aliases']=aliases;out['source50_identity_offer_prepared_at_utc']=datetime.now(timezone.utc).isoformat()
required=out['required_evidence_artifacts_sha256']
for p in B.iterdir():
 if p.is_file() and p.suffix in ('.json','.log','.py'):required[str(p.relative_to(R))]=H(p)
for p in [oldpath,candidate,R/peer['helper']['file'],R/'book/coverage/build_modules23_candidate_source50_identity_v1.py']:required[str(p.relative_to(R))]=H(p)
reverse=copy.deepcopy(out)
for k in changed:reverse[k]=copy.deepcopy(old[k])
for k in added:del reverse[k]
assert reverse==old
assert out['proof_files']==old['proof_files'] and out['counts']==old['counts'] and out['original_full_source_reviews']==old['original_full_source_reviews']
for n,d in out['required_evidence_artifacts_sha256'].items():assert H(R/n)==d
for n,d in peer['live22_owner_ledgers_exact'].items():assert H(R/n)==d
name=B/'modules-audit23-candidate-source50-additions-v1-reviewed.json';assert not name.exists();name.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'offer':ref(name),'candidate':ref(candidate),'peer':peerref,'scope':'Distinct reviewed isolated identity50 offer only; live22 ledger remains exact.'}))

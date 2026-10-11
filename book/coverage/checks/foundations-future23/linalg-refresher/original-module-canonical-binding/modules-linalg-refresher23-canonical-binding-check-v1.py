"""Readonly identity/evidence extension of the unchanged 11-literal semantic peer."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy,re
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/foundations-future23/linalg-refresher'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());ref=lambda p:{'file':str(Path(p).relative_to(R)) if Path(p).is_relative_to(R) else str(p),'sha256':H(p)}
ready_path=B/'eleven-literals-canonical-paired-source50-readiness-v1.json';assert H(ready_path)=='d6d542b7c03a780a65c8882b588fabd68c5bab7842ecf289d4548f783e7ed25f';ready=J(ready_path)
old_path=Path('/tmp/foundations-linalg-refresher-eleven-literals-independent-modules-source-review23-v1.json');assert H(old_path)=='be9f21c01be811f7b8137e0ea6d6638f9f11ad5a6c5e3f489dd6189393939f5f';old=J(old_path)
assert ready['entire_original_independent_peer_body_and_reviewed_time']==old
for original,a in ready['all_original_TMP_byte_copies'].items():assert H(original)==H(R/a['file'])==a['sha256']
request=J(R/ready['original_TMP_request']['file']);assert request==ready['entire_original_TMP_request_body_and_created_time']
assert H(R/ready['original_TMP_request']['file'])==old['original_review_request']['sha256']
source=R/ready['canonical_source']['file'];assert H(source)==ready['canonical_source']['sha256']=='1918ab182f7fe20385966020197f3195abca4d61068ebeb1f21bfc9bd2061f0e'
assert source.read_bytes()==Path('/tmp/foundations-linalg-refresher23-trial2.lean').read_bytes();assert source.read_text()==old['entire_new_TMP_source_body_read'];assert len(re.findall(r'^theorem\s+',source.read_text(),re.M))==ready['public_theorem_count']==23
assert H(R/ready['canonical_source_snapshot']['file'])==ready['canonical_source_snapshot']['sha256']==H(source)
inv49=R/'book/coverage/inventory-after-correction49.json';assert H(inv49)==old['inventory_sha256'];units49={u['key']:u for u in J(inv49)['material_source_units']}
inv50=R/'book/coverage/inventory-after-correction50.json';assert H(inv50)==ready['current_authoritative_source50_inventory']['sha256']=='dec8a34d0313fbc19846489f4d8c2f6e51734a135df6145829993fae0f80d91c';units50={u['key']:u for u in J(inv50)['material_source_units']}
current=R/'book/coverage/inventory.json';current_units={u['key']:u for u in J(current)['material_source_units']}
expected={f'primer-linalg.html::node-{n}' for n in [98,100,101,103,104,108,110,112,117,119,123]}
assert {u['source_unit_key'] for u in old['material_units']}==expected
for u in old['material_units']:
 assert u['entire_inventory_record']==units49[u['source_unit_key']]==units50[u['source_unit_key']]==current_units[u['source_unit_key']]
 assert u['whole_unit_approved'] and u['material_status']=='proved' and u['missing_clauses']==[]
assert H(R/old['source'])==old['source_sha256']
pairs=[]
for p in ready['actual_canonical_pair']:
 assert H(R/p['file'])==p['sha256'];a=J(R/p['file']);assert a['actual_exit_code']==p['actual_exit_code']==0
 assert a['source']==ready['canonical_source']['file'];assert a['source_sha256_before']==a['source_sha256_after']==H(source)
 assert H(R/a['preserved_source'])==a['preserved_source_sha256']==H(source)
 assert a['log']==p['raw_log']['file'] and H(R/a['log'])==a['log_sha256']==p['raw_log']['sha256']
 assert a['actual_pair_helper']==ready['actual_helper']['file'] and a['actual_pair_helper_sha256']==ready['actual_helper']['sha256']
 assert (R/a['log']).read_text().count('warning:')==4
 pairs.append({'actual_record':p,'entire_original_actual_record':a,'raw_log':p['raw_log'],'source_snapshot':{'file':a['preserved_source'],'sha256':a['preserved_source_sha256']}})
assert [p['entire_original_actual_record']['command'] for p in pairs]==[['lake','env','lean','SafeLearning/CompleteFoundationsLinalgRefresher23.lean'],['lake','build','SafeLearning.CompleteFoundationsLinalgRefresher23']]
helper=R/ready['actual_helper']['file'];execution=B/'canonical-pair-helper-actual-execution-source50-v1.json';ex=J(execution);assert ex['actual_exit_code']==0 and H(helper)==ready['actual_helper']['sha256']==ex['helper_sha256_before']==ex['helper_sha256_after'];assert H(R/ex['raw_log'])==ex['raw_log_sha256']
manifest=R/'reports/full-coverage/checkpoint-22-manifest.json';assert H(manifest)==old['protected_selected22']['manifest']['sha256'];m=J(manifest);assert len(m['proof_files'])==1113
for n,d in m['proof_files'].items():assert H(R/n)==d['sha256']
for n,d in old['protected_selected22']['frozen31_source48_asset_sha256'].items():assert H(R/m['snapshot']/n)==d
for n,d in old['protected_selected22']['four_held22_working_ledger_sha256'].items():assert H(R/n)==d
report={'status':'independent_canonical_source_and_actual_pair_binding_confirmation_passed','reviewer':'/root/modules_resume','bound_at_utc':datetime.now(timezone.utc).isoformat(),'original_semantic_review':{**ref(old_path),'original_reviewed_at_utc':old['reviewed_at_utc']},'entire_original_semantic_body_and_review_time':old,'canonical_readiness':ref(ready_path),'canonical_proof_source':ready['canonical_source'],'material_units':copy.deepcopy(old['material_units']),'actual_canonical_pair':pairs,'actual_pair_helper_execution':ref(execution),'original_full_semantic_body_decisions_hypotheses_reasons_declarations_and_time_preserved':True,'original_source49_identity':ref(inv49),'canonical_source50_identity':ref(inv50),'current_unchanged_linalg_identity':{'inventory':ref(current),'all11_entire_unit_records_equal_original49':True},'all1113_selected22_sources_31_frozen48_assets_four_working22_ledgers_exact':True,'actual_checker':str(Path(__file__)),'actual_checker_sha256':H(__file__),'limits':['Only genuine canonical source byte identity and actual paired compiler evidence are added; all original eleven unit decisions and their review time remain exact.','No neighboring node121, parent exercise, live owner integration or aggregate23 is inferred. Historical source49 and current unchanged entire Linalg literal records are explicit.'],'errors':[]}
out=Path('/tmp/foundations-linalg-refresher-eleven-literals-canonical-source-independent-modules-binding23-v1.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'status':report['status'],'report':str(out),'sha256':H(out)}))

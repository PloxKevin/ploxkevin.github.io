from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy
R=Path('/home/oxrexkevin/SafetyBased')
B='book/coverage/checks/root-owner23-reviewed-candidate-bindings-v1.json'
M='book/coverage/checks/future23-core/root23-live-owner-interface-manifest-v1.json'
O=Path('/tmp/root23-live-owner-interface-independent-modules-confirmation-v1.json')
cache={}
def sha(n,fresh=False):
    p=Path(n);assert not p.is_absolute() and str(p)==n and '..' not in p.parts
    assert (R/p).resolve().is_relative_to(R.resolve())
    if fresh or n not in cache:cache[n]=hashlib.sha256((R/p).read_bytes()).hexdigest()
    return cache[n]
def read(n):return json.loads((R/n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
def checked(r):assert sha(r['file'])==r['sha256'];return read(r['file'])
def actual0(n):
    a=read(n);codes=[a[k] for k in ('actual_exit_code','exit_code') if k in a]
    assert codes and all(type(c)is int and c==0 for c in codes)
    assert sha(a['log'])==a['log_sha256']
    before=a.get('helper_sha256_before',a.get('actual_checker_sha256_before'));after=a.get('helper_sha256_after',a.get('actual_checker_sha256_after'))
    assert before==after
    if isinstance(before,dict):
        for p,s in before.items():assert sha(p)==s
    return a
assert not O.exists()
b=read(B);m=read(M);request=checked(m['preparation_request'])
assert sha(B)=='4b6dd0eb2bae622be47e0fd96adf12a4b3c2dc10cc44baf1b34703c6cca8b054'
assert m['status']=='actual_copy_only_owner23_live_interfaces_prepared_for_independent_mechanical_review' and m['errors']==[]
assert m['execution_kind']=='actual_guarded_candidate_integration_copy'
assert set(m['owners'])==set(b['owners'])=={'core','modules','foundations','applied'}
assert m['preparation_helper']['sha256']==sha(m['preparation_helper']['file'])=='f3314d6f8a2263d91f06f5c80fdbe98195aed168697a86f2008c83f6ad237269'
assert m['inventory']==request['inventory']==ref('book/coverage/inventory-after-correction51.json')
assert sha('book/coverage/inventory.json')==m['inventory']['sha256']=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
apply=actual0(request['actual_integration_execution']['file']);assert sha(request['actual_integration_execution']['file'])==request['actual_integration_execution']['sha256']
assert apply['actual_command'][-1]=='--apply'
result=checked(request['integration_result']);assert result['applied'] is True
assert result['binding_manifest_sha256']==sha(B)
replacements={r['destination']:r for r in result['exact_replacements']}
assert len(replacements)==5
for n,r in replacements.items():
    assert sha(n)==r['candidate']['sha256']==sha(r['candidate']['file'])
    assert sha(r['original22_byte_copy'])==r['before_sha256']
integration_evidence={r['file']:r['sha256'] for r in (request['actual_integration_execution'],request['actual_integration_raw_log'],request['integration_result'],request['integration_binding'])}
integration_evidence.update({r['original22_byte_copy']:r['before_sha256'] for r in replacements.values()})
integration_evidence.update(request['historical_dry_run_evidence_sha256'])
assert len(integration_evidence)==12
for n,s in integration_evidence.items():assert sha(n)==s
outputs={}
append_fields={'live_interface_status','live_interface_prepared_at_utc','original_isolated_candidate_offer','actual_guarded_live_integration','original_candidate_mapping_peer','original_candidate_math_review_body_times_and_execution_history_retained','required_live_integration_evidence_sha256'}
inventory=read('book/coverage/inventory.json')
for owner,r in m['owners'].items():
    original=checked(r['original_candidate_offer']);live=checked(r['live_offer']);ledger=checked(r['live_ledger']);candidate=checked(r['candidate_ledger'])
    assert ledger==candidate and r['live_ledger']['file']=='book/coverage/'+owner+'.json'
    assert r['original_candidate_offer']==b['owners'][owner]['reviewed_final_offer']
    assert r['candidate_ledger']==b['owners'][owner]['candidate_ledger']
    assert r['candidate_mapping_peer']==b['owners'][owner]['independent_candidate_mapping_peer']
    assert set(r['appended_live_interface_fields'])==append_fields and not append_fields&set(original)
    expected_changed={'mapped_ledger','mapped_ledger_sha256'} if owner!='modules' else {'module_ledger','module_ledger_sha256'}
    if owner=='applied':expected_changed|={'mapped_promotions','mapped_promotions_sha256'}
    assert set(r['changed_original_fields'])==expected_changed
    reverse=copy.deepcopy(live)
    for k in append_fields:reverse.pop(k)
    for k in expected_changed:reverse[k]=original[k]
    assert reverse==original
    assert live['original_isolated_candidate_offer']==r['original_candidate_offer'] and live['original_candidate_math_review_body_times_and_execution_history_retained'] is True
    assert live['required_live_integration_evidence_sha256']==integration_evidence
    assert live['actual_guarded_live_integration']==m['actual_guarded_live_integration']
    assert set(live['proof_files'])==set(r['expected_owned_proof_sources'])==set(b['owners'][owner]['new_immutable_proof_sources'])
    if owner=='core':
        assert live['source_sha256']==inventory['source_sha256']
        assert set(ledger['source_sha256'])<=set(live['source_sha256'])
        assert all(ledger['source_sha256'][n]==live['source_sha256'][n] for n in ledger['source_sha256'])
    else:assert live['source_sha256']==ledger['source_sha256']
    for n,s in live['source_sha256'].items():assert sha(n)==s
    if owner=='applied':assert sha(live['mapped_promotions'])==live['mapped_promotions_sha256']==original['mapped_promotions_sha256']
    for rsem in b['owners'][owner]['original_full_source_semantic_reviews']:
        sem=checked(rsem);assert sem['status']==rsem['original_review_status'] and sem.get('reviewed_at_utc',sem.get('checked_at_utc'))==rsem['original_review_time']
    outputs[owner]={'live_offer':r['live_offer'],'original_candidate_offer':r['original_candidate_offer'],'live_ledger':r['live_ledger'],'changed_fields':r['changed_original_fields'],'original_entire_offer_reverse_exact':True,'original_semantic_body_and_time_retained':True}
aliases=checked(request['closed_report_original_byte_aliases']);assert 'copied_exactly' in aliases['status']
alias_by_original={a['original']['file']:a for a in aliases['aliases']}
additional=request['additional_frozen_inputs'];assert additional
for n,r in additional.items():assert sha(n)==r['sha256']
for a in aliases['aliases']:
    original=a['original'];canonical=a['canonical_original_byte_copy']
    assert sha(original['file'])==original['sha256']==sha(canonical['file'])==canonical['sha256']
    assert additional[canonical['file']]['sha256']==canonical['sha256']
for r in replacements.values():assert r['original22_byte_copy'] in alias_by_original
assert not set(r['sha256'] for r in additional.values())&set(request['excluded_full_external_reference_sha256'])
assert not any(Path(n).suffix=='.png' for n in additional)
wrappers=['reports/full-coverage/prepare-owner23-interface-request-execution-v1.json','reports/full-coverage/prepare-owner23-live-interfaces-execution-v1.json']
for n in wrappers:actual0(n)
global_name='reports/full-coverage/root-source51-final-owner-integration23-v1.json'
if not (R/global_name).exists():
    candidates=list((R/'reports/full-coverage').glob('*source51*integration23*.json'));assert len(candidates)==1;global_name=str(candidates[0].relative_to(R))
g=read(global_name);assert g['integrity_status']=='passed' and g['errors']==[] and g['inventory_sha256']==m['inventory']['sha256']
assert {r['domain']:r['ledger_sha256'] for r in g['domains']}=={o:r['live_ledger']['sha256'] for o,r in m['owners'].items()}
baseline=checked(b['baseline22_manifest'])
for n,p in baseline['proof_files'].items():assert sha(n)==p['sha256']
for n,s in b['exact_current51_safelearning_assets_sha256'].items():assert sha(n)==s
for n,s in baseline['frozen_inputs_sha256'].items():assert sha(baseline['snapshot']+'/'+n)==s
for owner,r in m['owners'].items():assert sha(r['live_ledger']['file'],True)==r['live_ledger']['sha256']
out={'status':'independent_actual_four_owner23_live_interface_outputs_confirmation_passed','checked_at_utc':datetime.now(timezone.utc).isoformat(),'live_interface_manifest':ref(M),'preparation_request':m['preparation_request'],'actual_integration_execution':request['actual_integration_execution'],'actual_integration_result':request['integration_result'],'actual_interfaces_preparation_execution':ref(wrappers[1]),'actual_request_preparation_execution':ref(wrappers[0]),'fresh_global_integrity':ref(global_name),'owners':outputs,'required_integration_evidence_count':12,'original22_archive_byte_count':5,'exact_original_report_byte_alias_count':len(aliases['aliases']),'additional_input_count':len(additional),'baseline22_selected_proof_count':1113,'baseline22_frozen_input_count':34051,'current51_asset_count':31,'errors':[],'scope':'Actual read-only output mechanics peer. All four original entire candidate offer bodies reverse exactly, retaining original mathematical review times/hypotheses/statuses and candidate compiler histories. Live builder provenance is the genuine reviewed Root integration copy, not a Lean compile. No new mathematical decision, full coverage or aggregate23 pass is inferred.'}
O.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'report':str(O),'sha256':hashlib.sha256(O.read_bytes()).hexdigest()}))

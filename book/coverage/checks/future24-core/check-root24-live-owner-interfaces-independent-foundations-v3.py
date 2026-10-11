from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, runpy

ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE='book/coverage/checks/future24-core/'
REQUEST=BASE+'checkpoint24-live-owner-interface-preparation-request-v1.json'
MANIFEST=BASE+'root24-live-owner-interface-manifest-v1.json'
HELPER='book/coverage/prepare_checkpoint24_live_owner_interfaces_v3.py'
OUT=BASE+'root24-live-owner-interfaces-independent-foundations-observations-v3.json'
def H(name):
    p=Path(name); p=p if p.is_absolute() else ROOT/p
    return hashlib.sha256(p.read_bytes()).hexdigest()
def R(name):return json.loads((ROOT/name).read_text())
def ref(name):return {'file':name,'sha256':H(name)}
def C(value):
    assert H(value['file'])==value['sha256'],value
    return R(value['file'])
def native_zero(d):
    codes=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
    assert codes and all(type(x) is int and x==0 for x in codes)
    assert 'passed' in d['status']
    commands=[d[k] for k in ('actual_command','command') if k in d]
    assert commands and all(x==commands[0] for x in commands)
    return commands[0]

request=R(REQUEST); manifest=R(MANIFEST)
assert H(HELPER)=='5475629dc153523e2ab408ba91165150d1aa37962cd9f67415d4020de19342c5'
assert manifest['preparation_request']==ref(REQUEST) and manifest['preparation_helper']==ref(HELPER)
assert manifest['errors']==[] and set(manifest['owners'])=={'core','foundations','applied','modules'}
assert manifest['status']=='actual_copy_only_owner24_live_interfaces_prepared_for_independent_mechanical_review'
# Run only the already reviewed read-only integration guard, never either writer.
ns=runpy.run_path(str(ROOT/HELPER),run_name='independent_read_only_interface_guard')
binding,result=ns['integration'](request)
execution=R('reports/full-coverage/prepare-owner24-live-interfaces-execution-v1.json')
assert native_zero(execution)==['python3',HELPER,'--request',REQUEST,'--stage','interfaces']
assert execution['actual_workdir']==str(ROOT)
assert execution['helper_sha256_before']==execution['helper_sha256_after']=={HELPER:H(HELPER)}
assert H(execution['log'])==execution['log_sha256']
global_execution=R('reports/full-coverage/owner24-global-integrity-execution-v1.json')
assert native_zero(global_execution)==['python3','book/coverage/validate.py','--output','reports/full-coverage/root-source52-final-owner-integration24-v1.json']
assert H(global_execution['log'])==global_execution['log_sha256']
global_report=R('reports/full-coverage/root-source52-final-owner-integration24-v1.json')
assert global_report['integrity_status']=='passed' and global_report['errors']==[]
assert global_report['inventory_sha256']==request['inventory']['sha256']
assert global_report['mathematical_coverage_complete'] is False
assert len(global_report['domains'])==4
replacement={x['destination']:x for x in result['exact_replacements']}
integration_evidence={x['file']:x['sha256'] for x in [request['actual_integration_execution'],request['actual_integration_raw_log'],request['integration_result'],request['integration_binding']]}
integration_evidence.update({r['original23_byte_copy']:r['before_sha256'] for r in replacement.values()})
integration_evidence.update(request['historical_dry_run_evidence_sha256'])
for p,h in integration_evidence.items():assert H(p)==h
all_sources={}; pairs=[]; owners={}
for owner,row in manifest['owners'].items():
    entry=binding['owners'][owner]
    original=C(row['original_candidate_offer']); live=C(row['live_offer']); ledger=C(row['live_ledger'])
    assert row['original_candidate_offer']==entry['reviewed_final_offer']
    assert row['candidate_ledger']==entry['candidate_ledger']
    assert row['candidate_mapping_peer']==entry['independent_candidate_mapping_peer']
    assert row['live_offer']['file']==request['live_offer_destinations'][owner]
    assert row['live_ledger']=={'file':'book/coverage/'+owner+'.json','sha256':row['candidate_ledger']['sha256']}
    assert (ROOT/row['live_ledger']['file']).read_bytes()==(ROOT/row['candidate_ledger']['file']).read_bytes()
    assert next(x for x in global_report['domains'] if x['domain']==owner)['ledger_sha256']==row['live_ledger']['sha256']
    assert set(row['expected_owned_proof_sources'])==set(original['proof_files'])==set(entry['new_immutable_proof_sources'])
    reverse=copy.deepcopy(live)
    assert set(row['appended_live_interface_fields'])==set(live)-set(original)
    assert len(set(row['changed_original_fields']))==len(row['changed_original_fields'])
    assert {k for k in original if original[k]!=live[k]} <= set(row['changed_original_fields'])
    expected_changed=[] if owner=='core' else [entry['offer_candidate_path_pointer'][0],entry['offer_candidate_sha256_pointer'][0]]
    if owner=='applied':expected_changed+=['mapped_promotions','mapped_promotions_sha256','required_live_integration_evidence_sha256']
    assert row['changed_original_fields']==expected_changed
    for k in row['appended_live_interface_fields']:reverse.pop(k)
    for k in row['changed_original_fields']:reverse[k]=original[k]
    assert reverse==original and row['original_body_reversible_exact'] is True
    assert live['status']==original['status']
    assert live['original_isolated_candidate_offer']==row['original_candidate_offer']
    assert live['original_candidate_mapping_peer']==row['candidate_mapping_peer']
    assert live['actual_guarded_live_integration']==manifest['actual_guarded_live_integration']
    assert live['original_candidate_math_review_body_times_and_execution_history_retained'] is True
    assert live['actual_guarded_live_integration']=={'execution_kind':ns['KIND'],'actual_execution':request['actual_integration_execution'],'raw_log':request['actual_integration_raw_log'],'actual_helper':binding['helper'],'binding_manifest':request['integration_binding'],'integration_result':request['integration_result'],'scope':ns['SCOPE']}
    assert live['live_interface_status']=='current52_exact_reviewed_candidate_copy_pending_global_integrity_and_fresh24_audit'
    expected_evidence=dict(original.get('required_live_integration_evidence_sha256',{}))
    for p,h in integration_evidence.items():
        assert p not in expected_evidence or expected_evidence[p]==h
        expected_evidence[p]=h
    assert live['required_live_integration_evidence_sha256']==expected_evidence
    for p,h in expected_evidence.items():assert H(p)==h
    if owner=='core':
        assert live['candidate_ledger']==original['candidate_ledger']
        assert live['mapped_ledger']==row['live_ledger']['file'] and live['mapped_ledger_sha256']==row['live_ledger']['sha256']
    else:
        key=entry['offer_candidate_path_pointer'][0]
        assert live[key]==row['live_ledger']['file'] and live[key+'_sha256']==row['live_ledger']['sha256']
    if owner=='applied':
        companion=entry['companion_candidates'][0]
        assert live['mapped_promotions']==companion['held23_asset']
        assert live['mapped_promotions_sha256']==companion['candidate']['sha256']==H(companion['held23_asset'])
        assert (ROOT/companion['candidate']['file']).read_bytes()==(ROOT/companion['held23_asset']).read_bytes()
    imports=live.get('required_external_import_dependencies',{})
    assert isinstance(imports,dict)
    for p,h in imports.items():assert H(p)==h
    ns['source_identity'](owner,live,ledger)
    for original_review in entry['original_full_source_semantic_reviews']:
        d=C({'file':original_review['file'],'sha256':original_review['sha256']})
        assert d['status']==original_review['original_review_status']
        assert original_review['original_review_time'] in d.values()
    for source,meta in entry['new_immutable_proof_sources'].items():
        assert source not in all_sources and H(source)==meta['sha256']
        all_sources[source]=meta['sha256'];assert len(meta['actual_pair'])==2
        for n,pair in enumerate(meta['actual_pair']):
            d=C({'file':pair['file'],'sha256':pair['sha256']})
            expected=['lake','env','lean',str(Path(source).relative_to('verification/lean'))] if n==0 else ['lake','build','SafeLearning.'+Path(source).stem]
            assert native_zero(d)==pair['actual_command']==expected
            assert d['source']==pair['actual_source']==source
            assert d['actual_workdir']==pair['actual_workdir']==str(ROOT/'verification/lean')
            assert d['source_sha256_before']==d['source_sha256_after']==meta['sha256']
            log=pair['canonical_raw_log'];assert H(log['file'])==log['sha256']
            log_hashes=[d[k] for k in ('log_sha256','raw_log_sha256','original_log_sha256') if k in d]
            assert log_hashes and all(h==log['sha256'] for h in log_hashes)
            assert any(d[k]==log['file'] for k in ('log','raw_log') if k in d)
            if 'source_snapshot' in d:assert H(d['source_snapshot'])==d['source_snapshot_sha256']==meta['sha256']
            pairs.append({'owner':owner,'source':source,'record':{'file':pair['file'],'sha256':pair['sha256']},'raw_log':log})
    owners[owner]={'live_offer':row['live_offer'],'live_ledger':row['live_ledger'],'original_offer':row['original_candidate_offer'],'exact_entire_original_body_reversed':True,'changed_fields':row['changed_original_fields'],'appended_fields':row['appended_live_interface_fields'],'new_source_count':len(entry['new_immutable_proof_sources'])}
assert len(all_sources)==13 and len(pairs)==26
for p,meta in request['additional_frozen_inputs'].items():
    assert isinstance(meta,dict) and set(meta)=={'sha256','scope'}
    assert meta['scope']=='immutable_audit_or_local_source_evidence'
    assert H(p)==meta['sha256'],(p,meta)
assert len(request['additional_frozen_inputs'])==2215
assert isinstance(request['excluded_full_external_reference_sha256'],list)
assert len(request['excluded_full_external_reference_sha256'])==len(set(request['excluded_full_external_reference_sha256']))==12
assert all(isinstance(x,str) and len(x)==64 for x in request['excluded_full_external_reference_sha256'])
for key in ('selection_helper','content_retainer','actual_source52_apply','actual_source52_postwrite','closed_report_original_byte_aliases'):
    assert H(request[key]['file'])==request[key]['sha256']
baseline=R('reports/full-coverage/checkpoint-23-selection.json')
assert not set(all_sources)&set(baseline['proof_files']) and len(baseline['proof_files'])==1131
old_manifest=R('reports/full-coverage/checkpoint-23-manifest.json')
for p in baseline['proof_files']:assert H(p)==old_manifest['working_inputs_sha256'][p]
observations={'status':'independent_actual_four_owner24_live_interface_output_review_passed','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'errors':[],'live_interface_manifest':ref(MANIFEST),'helper_sha256':H(HELPER),'preparation_request':ref(REQUEST),'actual_interface_execution':ref('reports/full-coverage/prepare-owner24-live-interfaces-execution-v1.json'),'actual_interface_raw_log':ref(execution['log']),'actual_root_integration':manifest['actual_guarded_live_integration'],'global_integrity':ref('reports/full-coverage/root-source52-final-owner-integration24-v1.json'),'owners':owners,'all26_original_actual_canonical_records':pairs,'exact_request_additional_alias_count':2215,'exact_baseline_selected_source_count':1131,'excluded_external_reference_hashes':request['excluded_full_external_reference_sha256'],'scope':'Read-only actual output mechanics and source/evidence identity. Original whole/component mathematical decisions, entire offer bodies, reviewer times and failure histories are preserved; no compilation, selection24, aggregate24, Pages24 or new mathematical approval is asserted.'}
with (ROOT/OUT).open('x') as f:f.write(json.dumps(observations,indent=2)+'\n')
print(json.dumps({'status':observations['status'],'owners':4,'sources':13,'canonical_records':26,'additional_exact_files':2215,'baseline_sources':1131,'output':OUT}))

"""Independently read genuine native26 interface outputs; never run a producer."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,importlib.util,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
MANIFEST='book/coverage/checks/future26-core/root26-live-owner-interface-manifest-v1.json'
REQUEST='book/coverage/checks/future26-core/checkpoint26-live-owner-interface-preparation-request-v1.json'
HELPER='book/coverage/prepare_checkpoint26_live_owner_interfaces_v3.py';HELPER_SHA='b621995200290d40f4a3505385042ef04efa8d9f39bb830cf64776dbfd98bd52'
CODE_PEER='book/coverage/checks/future26-core/owner26-live-interface-and-request-helpers-independent-foundations-review-v1.json';CODE_PEER_SHA='58bddf154ec9cca9b8435d9b10e819ba7ac465ca1c9837794a673d1ecf93fffa'
OUT=Path('/tmp/owner26-actual-live-interfaces-independent-foundations-observation-v1.json')
def safe(n):
 assert isinstance(n,str) and n and not Path(n).is_absolute() and str(Path(n))==n and '..' not in Path(n).parts
 p=ROOT/n;assert p.resolve().is_relative_to(ROOT.resolve());return p
def sha(n):return hashlib.sha256(safe(n).read_bytes()).hexdigest()
def read(n):return json.loads(safe(n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
def checked(r):
 assert isinstance(r,dict) and set(r)=={'file','sha256'} and re.fullmatch('[0-9a-f]{64}',r['sha256']) and sha(r['file'])==r['sha256'];return read(r['file'])
def zero(d):
 values=[d[k] for k in ('actual_exit_code','exit_code') if k in d];assert values and all(type(v)is int and v==0 for v in values)
def alias(d,keys):
 v=[d[k] for k in keys if k in d];assert v and all(x==v[0] for x in v);return v[0]
def actual(name,command,helper):
 d=read(name);zero(d);assert alias(d,('actual_command','command'))==command
 assert alias(d,('actual_workdir','working_directory','cwd'))==str(ROOT)
 before=alias(d,('helper_sha256_before','actual_helper_sha256_before'));after=alias(d,('helper_sha256_after','actual_helper_sha256_after'));assert before==after
 if isinstance(before,dict):assert before[helper]==sha(helper)
 else:assert before==sha(helper)
 log=alias(d,('log','raw_log'));assert sha(log)==alias(d,('log_sha256','raw_log_sha256','original_log_sha256'))
 return d,ref(log)
assert sha(HELPER)==HELPER_SHA and sha(CODE_PEER)==CODE_PEER_SHA
codepeer=read(CODE_PEER);assert 'passed' in codepeer['status'] and codepeer['errors']==[] and codepeer['helper_sha256']==HELPER_SHA
request=read(REQUEST);manifest=read(MANIFEST);binding=checked(request['integration_binding']);result=checked(request['integration_result'])
assert manifest['status']=='actual_copy_only_owner26_live_interfaces_prepared_for_independent_mechanical_review' and manifest['errors']==[]
assert manifest['preparation_request']==ref(REQUEST) and manifest['preparation_helper']==ref(HELPER)
assert manifest['inventory']==request['inventory']==ref('book/coverage/inventory-after-correction53.json')
assert sha('book/coverage/inventory.json')==manifest['inventory']['sha256']=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
assert set(manifest['owners'])==set(binding['owners'])=={'core','foundations','applied','modules'}
assert manifest['original_math_body_review_times_and_actual_candidate_builds_retained'] is True
# Read the reviewed producer's pure integration validator, then independently
# check the produced whole-offer reverses and all native pair records below.
spec=importlib.util.spec_from_file_location('read_only_interface26_output_guard',safe(HELPER));module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
validated_binding,validated_result=module.integration(request);assert validated_binding==binding and validated_result==result
actual_interface,interface_log=actual('reports/full-coverage/prepare-owner26-live-interfaces-execution-v1.json',['python3',HELPER,'--request',REQUEST,'--stage','interfaces'],HELPER)
request_helper=request.get('preparation_helper',{'file':'book/coverage/checks/prepare_root_owner26_interfaces_request_v3.py'})['file']
actual_request,request_log=actual('reports/full-coverage/prepare-owner26-interface-request-execution-v1.json',['python3',request_helper],request_helper)
globalname='reports/full-coverage/root-source53-final-owner-integration26-v1.json';globalbody=read(globalname)
assert globalbody['integrity_status']=='passed' and globalbody['errors']==[] and globalbody['inventory_sha256']==manifest['inventory']['sha256']
assert {r['domain'] for r in globalbody['domains']}==set(binding['owners'])
assert result['applied'] is True and result['all44111_frozen25_inputs_exact'] is True and result['all1156_selected25_root_source_hashes_exact'] is True
replacements={r['destination']:r for r in result['exact_replacements']};assert len(result['exact_replacements'])==len(replacements)==5
assert set(replacements)=={'book/coverage/'+x+'.json' for x in binding['owners']}|{'book/coverage/applied-promotions.json'}
original_manifest=read('reports/full-coverage/checkpoint-25-manifest.json')
assert len(original_manifest['proof_files'])==1156 and len(original_manifest['frozen_inputs_sha256'])==44111
assets={n:sha(n) for n in original_manifest['frozen_inputs_sha256'] if n.startswith('SafeLearning/')};assert len(assets)==31 and assets==binding['exact_current53_safelearning_assets_sha256']
records={};pair_count=0;proofs={};semantics=[]
for owner,row in manifest['owners'].items():
 entry=binding['owners'][owner];original=checked(row['original_candidate_offer']);live=checked(row['live_offer']);ledger=checked(row['live_ledger'])
 assert row['original_candidate_offer']==entry['reviewed_final_offer']==live['original_isolated_candidate_offer']
 assert row['candidate_ledger']==entry['candidate_ledger'] and row['live_ledger']==ref('book/coverage/'+owner+'.json')
 assert row['live_ledger']['sha256']==row['candidate_ledger']['sha256'] and checked(row['candidate_ledger'])==ledger
 assert next(r for r in globalbody['domains'] if r['domain']==owner)['ledger_sha256']==row['live_ledger']['sha256']
 assert row['original_body_reversible_exact'] is True
 assert len(row['changed_original_fields'])==len(set(row['changed_original_fields'])) and len(row['appended_live_interface_fields'])==len(set(row['appended_live_interface_fields']))
 assert set(row['changed_original_fields']).isdisjoint(row['appended_live_interface_fields'])
 reverse=copy.deepcopy(live)
 for field in row['appended_live_interface_fields']:assert field not in original;reverse.pop(field)
 for field in row['changed_original_fields']:assert field in original;reverse[field]=original[field]
 assert reverse==original
 assert live['mapped_ledger']=='book/coverage/'+owner+'.json' and live['mapped_ledger_sha256']==row['live_ledger']['sha256']
 if owner=='modules':assert live['module_ledger']==live['mapped_ledger'] and live['module_ledger_sha256']==live['mapped_ledger_sha256']
 if owner=='applied':assert live['mapped_promotions']=='book/coverage/applied-promotions.json' and live['mapped_promotions_sha256']==sha(live['mapped_promotions'])==original['mapped_promotions_sha256']
 assert row['candidate_mapping_peer']==entry['independent_candidate_mapping_peer']==live['original_candidate_mapping_peer']
 peer=checked(row['candidate_mapping_peer']);assert 'passed' in peer['status'] and peer.get('errors',[])==[]
 assert sorted(original['proof_files'])==row['expected_owned_proof_sources'] and original['proof_files']==live['proof_files']
 assert live['actual_guarded_live_integration']==manifest['actual_guarded_live_integration'] and live['original_candidate_math_review_body_times_and_execution_history_retained'] is True
 for n,h in live['required_live_integration_evidence_sha256'].items():assert sha(n)==h
 if 'required_live_integration_evidence_sha256' in original:
  assert all(live['required_live_integration_evidence_sha256'][n]==h for n,h in original['required_live_integration_evidence_sha256'].items())
 imports=live.get('required_external_import_dependencies',{});assert isinstance(imports,dict)
 for n,h in imports.items():assert sha(n)==h
 if owner=='core':assert live['source_sha256']==read('book/coverage/inventory.json')['source_sha256'] and all(ledger['source_sha256'][n]==live['source_sha256'][n] for n in ledger['source_sha256'])
 else:assert live['source_sha256']==ledger['source_sha256']
 for n,h in live['source_sha256'].items():assert sha(n)==h
 raw='book/coverage/'+owner+'.json';rr=replacements[raw]
 assert rr['candidate']==entry['candidate_ledger'] and rr['before_sha256']==entry['held25_ledger_sha256']==original_manifest['working_inputs_sha256'][raw]
 assert sha(rr['original25_byte_copy'])==rr['before_sha256']
 for semantic in entry['original_full_source_semantic_reviews']:
  d=checked({'file':semantic['file'],'sha256':semantic['sha256']});assert d['status']==semantic['original_review_status'] and d.get('reviewed_at_utc',d.get('checked_at_utc'))==semantic['original_review_time'] and d.get('errors',[])==[];semantics.append(semantic)
 for source,p in entry['new_immutable_proof_sources'].items():
  assert source not in proofs and sha(source)==p['sha256'];proofs[source]=p['sha256'];assert len(p['actual_pair'])==2
  for actual_pair in p['actual_pair']:
   d=checked({'file':actual_pair['file'],'sha256':actual_pair['sha256']});zero(d)
   assert d['source']==source and d['source_sha256_before']==d['source_sha256_after']==p['sha256']
   assert alias(d,('command','actual_command'))==actual_pair['actual_command'] and d['actual_workdir']==actual_pair['actual_workdir']==str(ROOT/'verification/lean')
   assert sha(actual_pair['canonical_raw_log']['file'])==actual_pair['canonical_raw_log']['sha256']==alias(d,('log_sha256','raw_log_sha256'));pair_count+=1
 records[owner]={'original_offer':row['original_candidate_offer'],'live_offer':row['live_offer'],'live_ledger':row['live_ledger'],'changed_original_fields':row['changed_original_fields'],'appended_live_interface_fields':row['appended_live_interface_fields'],'whole_body_and_original_mathematical_times_reversed_exact':True}
assert len(proofs)==11 and pair_count==22
promotions=replacements['book/coverage/applied-promotions.json'];assert sha(promotions['original25_byte_copy'])==promotions['before_sha256']==original_manifest['working_inputs_sha256']['book/coverage/applied-promotions.json']
assert sha(promotions['destination'])==promotions['candidate']['sha256']==sha(promotions['candidate']['file'])
assert sha(HELPER)==HELPER_SHA and sha(CODE_PEER)==CODE_PEER_SHA
assert not OUT.exists();body={'status':'independent_actual_four_owner26_live_interface_exact_body_and_provenance_review_passed','errors':[],'reviewer':'Independent Foundations agent','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'live_interface_manifest':ref(MANIFEST),'helper_sha256':HELPER_SHA,'actual_request':ref(REQUEST),'actual_interface_execution':ref('reports/full-coverage/prepare-owner26-live-interfaces-execution-v1.json'),'actual_interface_raw_log':interface_log,'actual_request_execution':ref('reports/full-coverage/prepare-owner26-interface-request-execution-v1.json'),'actual_request_raw_log':request_log,'integration_binding':request['integration_binding'],'actual_integration_execution':request['actual_integration_execution'],'integration_result':request['integration_result'],'actual_global_integrity':ref(globalname),'owners':records,'original_full_mathematical_review_status_and_times_preserved':semantics,'exact_current53_assets_sha256':assets,'new_sources':11,'public_exports':134,'actual_original_canonical_pair_records':22,'old44111_content_and1156_sources_bound_by_genuine_guarded_apply':True,'coverage_complete':False,'scope':'Read-only review of genuine request/interface/copy/global outputs, exact entire-offer reverses, all eleven unchanged sources and22 original canonical records. No fresh mathematics, compiler, aggregate26, production selection, PUB/Git/Pages or live delivery is inferred.'};OUT.write_text(json.dumps(body,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':'passed','observation':str(OUT),'sha256':hashlib.sha256(OUT.read_bytes()).hexdigest()}))

from pathlib import Path
import copy,json,hashlib
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=ROOT/'book/coverage/prepare_checkpoint25_live_owner_interfaces_v2.py'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
realj=lambda n:json.loads((ROOT/n).read_text())
ns={'__name__':'independent_in_memory_code_fixture','__file__':str(HELPER)}
exec(compile(HELPER.read_text(),str(HELPER),'exec'),ns)
store={};outputs=[];fx='book/coverage/checks/future25-core/independent-owner25-interface-code-fixture-only/'
def put(n,d):store[n]=(json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode();return {'file':n,'sha256':digest(n)}
def digest(n):return hashlib.sha256(store[n]).hexdigest() if n in store else H(ROOT/n)
def read(n):return json.loads(store[n]) if n in store else realj(n)
def write(n,d):assert n not in store;put(n,d);outputs.append(n)
ns.update(sha=digest,read=read,write_new=write)
manifest=realj('reports/full-coverage/checkpoint-24-manifest.json')
observation=realj('book/coverage/checks/future25-core/checkpoint25-native-final-owner-binding-request-observation-v1.json')
paths={o:r['file']for o,r in observation['production_binding_input_template_without_independent_helper_peer']['offers'].items()}
binding={'status':'all_four_reviewed_current52_owner_candidates_bound_ready_for_root_execution','helper':{'file':'book/coverage/checks/root_integrate_owner25_candidates_v2.py','sha256':digest('book/coverage/checks/root_integrate_owner25_candidates_v2.py')},'owners':{}}
rows=[]
for owner,n in paths.items():
 o=read(n);keys=['candidate_ledger','file'] if owner=='core' else ['module_ledger'] if owner=='modules' else ['mapped_ledger'];hkeys=['candidate_ledger','sha256'] if owner=='core' else [keys[0]+'_sha256'];cand={'file':ns['pointer'](o,keys),'sha256':ns['pointer'](o,hkeys)}
 ledger='book/coverage/'+owner+'.json';archive=fx+'old-'+owner+'.json';store[archive]=(ROOT/ledger).read_bytes();store[ledger]=(ROOT/cand['file']).read_bytes()
 peerkey='final_independent_candidate_peer'if owner=='core'else'independent_final_candidate_mapping_peer'if owner=='modules'else'final_independent_candidate_mapping_peer'
 peer=o[peerkey]
 entry={'candidate_ledger':cand,'held24_ledger_sha256':manifest['working_inputs_sha256'][ledger],'independent_candidate_mapping_peer':peer,'reviewed_final_offer':{'file':n,'sha256':digest(n)},'offer_candidate_path_pointer':keys,'offer_candidate_sha256_pointer':hkeys}
 binding['owners'][owner]=entry;rows.append({'destination':ledger,'candidate':cand,'before_sha256':manifest['working_inputs_sha256'][ledger],'original24_byte_copy':archive})
 if owner=='applied':
  pp=o['mapped_promotions'];live='book/coverage/applied-promotions.json';arc=fx+'old-promotions.json';store[arc]=(ROOT/live).read_bytes();store[live]=(ROOT/pp).read_bytes();entry['companion_candidates']=[{'candidate':{'file':pp,'sha256':digest(pp)},'held24_asset':live}];rows.append({'destination':live,'candidate':entry['companion_candidates'][0]['candidate'],'before_sha256':manifest['working_inputs_sha256'][live],'original24_byte_copy':arc})
bref=put(fx+'binding.json',binding);log=fx+'synthetic-integration.log';store[log]=b'explicitly synthetic code fixture, never actual execution\n'
eref=put(fx+'synthetic-execution.json',{'actual_exit_code':0,'command':['python3',binding['helper']['file'],bref['file'],'--apply'],'actual_workdir':str(ROOT),'helper_sha256_before':binding['helper']['sha256'],'helper_sha256_after':binding['helper']['sha256'],'log_sha256':digest(log)})
result={'status':'four_exact_reviewed_owner25_candidate_bytes_integrated_pending_fresh_global_integrity_and_aggregate25_audit','applied':True,'actual_helper':binding['helper']['file'],'actual_helper_sha256':binding['helper']['sha256'],'binding_manifest':bref['file'],'binding_manifest_sha256':bref['sha256'],'inventory_sha256':ns['INVENTORY_SHA'],'all40485_frozen24_inputs_exact':True,'all1144_selected24_root_source_hashes_exact':True,'exact_replacements':rows}
rref=put(fx+'synthetic-result.json',result)
req={'status':'root_authorized_postintegration_owner25_interface_preparation','inventory':{'file':ns['INVENTORY'],'sha256':ns['INVENTORY_SHA']},'live_interface_helper':{'file':str(HELPER.relative_to(ROOT)),'sha256':H(HELPER)},'integration_binding':bref,'actual_integration_execution':eref,'actual_integration_raw_log':{'file':log,'sha256':digest(log)},'integration_result':rref,'live_offer_destinations':{o:fx+'live-'+o+'.json' for o in paths},'interface_manifest_destination':fx+'interfaces.json','production_plan_destination':fx+'plan.json','selection_helper':{'file':ns['SELECTOR'],'sha256':digest(ns['SELECTOR'])},'content_retainer':{'file':ns['RETAINER'],'sha256':digest(ns['RETAINER'])},'additional_frozen_inputs':[],'excluded_full_external_reference_sha256':{},'prior_checkpoint24_selection_provenance':{},'actual_source52_apply':{'file':'reports/full-coverage/source52-apply-execution-v1.json','sha256':digest('reports/full-coverage/source52-apply-execution-v1.json')},'actual_source52_postwrite':{'file':'book/coverage/checks/root-source-batch52/postwrite-source-integrity-v1.json','sha256':digest('book/coverage/checks/root-source-batch52/postwrite-source-integrity-v1.json')}}
reqref=put(fx+'request.json',req)
if __name__=='__main__':
 out=ns['interfaces'](reqref['file']);print('interfaces passed',out['sha256'],len(outputs))
 mi={'file':out['interface_manifest'],'sha256':out['sha256']};pr=put(fx+'synthetic-output-peer.json',{'status':'synthetic_fixture_passed','errors':[],'live_interface_manifest':mi});gr=put(fx+'synthetic-global.json',{'integrity_status':'passed','errors':[],'inventory_sha256':ns['INVENTORY_SHA'],'domains':[{'domain':o,'ledger_sha256':digest('book/coverage/'+o+'.json')}for o in paths]})
 p=ns['plan'](reqref['file'],mi,pr,gr);print('plan passed',p)

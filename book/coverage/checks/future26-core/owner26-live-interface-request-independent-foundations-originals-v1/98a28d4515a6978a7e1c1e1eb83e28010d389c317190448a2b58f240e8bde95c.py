"""Independent code/native-shape review with isolated synthetic integration fixtures."""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
IF='book/coverage/prepare_checkpoint26_live_owner_interfaces_v3.py';IFS='b621995200290d40f4a3505385042ef04efa8d9f39bb830cf64776dbfd98bd52'
REQ='book/coverage/checks/prepare_root_owner26_interfaces_request_v3.py';RS='a566569476988ae4966ddc10c792999414bcdfd76a16c10ce249e70324e862b7'
OUT=Path('/tmp/owner26-live-interface-request-independent-foundations-observation-v2.json')
sha=lambda n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def ref(n):return {'file':n,'sha256':sha(n)}
assert sha(IF)==IFS and sha(REQ)==RS
itree=ast.parse((ROOT/IF).read_text());rtree=ast.parse((ROOT/REQ).read_text());compile(itree,IF,'exec');compile(rtree,REQ,'exec')
ns={'__file__':str(ROOT/IF),'__name__':'isolated_interface_code_review'};exec(compile(itree,IF,'exec'),ns)
fixtures=[]
def reject(label,fn):
 try:fn()
 except (AssertionError,KeyError,ValueError,TypeError):fixtures.append(label);return
 raise AssertionError('accepted invalid fixture '+label)
for n in ['/tmp/escape','../escape','book/coverage/../core.json','book//coverage/core.json','./book/coverage/core.json','']:
 reject('safe rejects '+repr(n),lambda n=n:ns['safe'](n))
assert ns['safe']('book/coverage/core.json')==ROOT/'book/coverage/core.json';fixtures.append('canonical relative safe path accepted')
# Request pre-copy guards and exact old-YAML archives are inspected, not produced.
constants={}
for node in rtree.body:
 if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name):
  try:constants[node.targets[0].id]=ast.literal_eval(node.value)
  except (TypeError,ValueError):pass
assert len(constants['EXACT_ARCHIVED_YAML_INPUTS'])==2
for n,h in constants['EXACT_ARCHIVED_YAML_INPUTS'].items():assert sha(n)==h
fixtures.append('two exact closed25 YAML aliases exist with native pinned bytes')
mkdir=next(n.lineno for n in ast.walk(rtree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='mkdir')
assert any(isinstance(n,ast.Assert) and 'digest not in set(excluded)' in ast.unparse(n.test) and n.lineno<mkdir for n in ast.walk(rtree))
assert any(isinstance(n,ast.Assert) and 'type(c) is int' in ast.unparse(n.test) and n.lineno<mkdir for n in ast.walk(rtree))
assert 'prepare-owner26-interface-request-execution-' in (ROOT/REQ).read_text()
assert 'prepare_checkpoint26_live_owner_interfaces_v3.py' in (ROOT/REQ).read_text()
assert not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in {'replace','unlink','remove','rmtree'} for n in ast.walk(rtree))
fixtures.append('source/evidence/full-external guards precede request alias creation; in-flight wrapper excluded; no old input mutation')
# Native offers except prospective Core are original full current files. Their entire bodies are preserved in synthetic tests.
names={'foundations':'book/coverage/checks/foundations-future26/source53/foundations-audit26-candidate-source53-additions-v1-reviewed.json','applied':'book/coverage/checks/applied-future26/source53-v2/applied-audit26-candidate-source53-additions-v1-reviewed.json','modules':'book/coverage/checks/modules-future26/source53/modules-audit26-candidate-source53-additions-v1-reviewed.json'}
offers={o:json.loads((ROOT/n).read_text()) for o,n in names.items()}
corecandidate='book/coverage/checks/future26-core/composed-source53-v3/core26-source53-composed-candidate-v1.json';coreledger=json.loads((ROOT/corecandidate).read_text());inventory=json.loads((ROOT/ns['INVENTORY']).read_text())
coreoffer='book/coverage/checks/future26-core/composed-source53-v3/core-audit26-candidate-source53-additions-v1-reviewed.json'
if (ROOT/coreoffer).exists():offers['core']=json.loads((ROOT/coreoffer).read_text());core_native=True
else:offers['core']={'mapped_ledger':corecandidate,'mapped_ledger_sha256':sha(corecandidate),'source_sha256':inventory['source_sha256'],'proof_files':{x['source']['file']:{'sha256':x['source']['sha256']} for x in coreledger['future26_composed_candidate_binding']['new_proof_sources']},'original_body_fixture':{'time':'held','scope':'prospective flat native finalizer schema only'}};core_native=False
names['core']=coreoffer
man=json.loads((ROOT/'reports/full-coverage/checkpoint-25-manifest.json').read_text())
def digest(d):return hashlib.sha256(json.dumps(d,sort_keys=True).encode()).hexdigest()
files={};hashes={};binding={'status':'all_four_reviewed_current53_owner_candidates_bound_ready_for_root_execution','owners':{},'helper':ref('book/coverage/checks/root_integrate_owner26_candidates_v2.py')}
for o,offer in offers.items():
 ledger=coreledger if o=='core' else json.loads((ROOT/offer['mapped_ledger']).read_text());candidate={'file':offer['mapped_ledger'],'sha256':offer['mapped_ledger_sha256']}
 peer={'file':'book/coverage/checks/future26-core/SYNTHETIC-'+o+'-peer.json','sha256':digest({'status':'passed','errors':[]})};files[peer['file']]={'status':'passed','errors':[]};hashes[peer['file']]=peer['sha256']
 offerref={'file':names[o],'sha256':sha(names[o]) if (ROOT/names[o]).exists() else digest(offer)};files[names[o]]=offer;hashes[names[o]]=offerref['sha256']
 files[candidate['file']]=ledger;hashes[candidate['file']]=candidate['sha256'];files['book/coverage/'+o+'.json']=ledger;hashes['book/coverage/'+o+'.json']=candidate['sha256']
 binding['owners'][o]={'candidate_ledger':candidate,'held25_ledger_sha256':man['working_inputs_sha256']['book/coverage/'+o+'.json'],'reviewed_final_offer':offerref,'independent_candidate_mapping_peer':peer,'offer_candidate_path_pointer':['mapped_ledger'],'offer_candidate_sha256_pointer':['mapped_ledger_sha256'],'companion_candidates':[]}
 if o=='applied':
  dest='book/coverage/applied-promotions.json';hashes[dest]=offer['mapped_promotions_sha256'];hashes[offer['mapped_promotions']]=offer['mapped_promotions_sha256'];binding['owners'][o]['companion_candidates']=[{'held25_asset':dest,'candidate':{'file':offer['mapped_promotions'],'sha256':offer['mapped_promotions_sha256']}}]
 for n,h in offer['source_sha256'].items():hashes[n]=h
bindingname='book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json';files[bindingname]=binding;hashes[bindingname]=digest(binding)
execname='reports/full-coverage/SYNTHETIC-owner26-apply.json';logname='reports/full-coverage/SYNTHETIC-owner26-apply.log';hashes[logname]='f'*64
execution={'actual_exit_code':0,'exit_code':0,'actual_command':['python3',binding['helper']['file'],bindingname,'--apply'],'command':['python3',binding['helper']['file'],bindingname,'--apply'],'actual_workdir':str(ROOT),'helper_sha256_before':{binding['helper']['file']:binding['helper']['sha256']},'helper_sha256_after':{binding['helper']['file']:binding['helper']['sha256']},'log_sha256':hashes[logname],'raw_log_sha256':hashes[logname]}
files[execname]=execution;hashes[execname]=digest(execution)
result={'status':'four_exact_reviewed_owner26_candidate_bytes_integrated_pending_fresh_global_integrity_and_aggregate26_audit','applied':True,'actual_helper':binding['helper']['file'],'actual_helper_sha256':binding['helper']['sha256'],'binding_manifest':bindingname,'binding_manifest_sha256':hashes[bindingname],'inventory_sha256':ns['INVENTORY_SHA'],'all44111_frozen25_inputs_exact':True,'all1156_selected25_root_source_hashes_exact':True,'exact_replacements':[]}
for o,e in binding['owners'].items():
 dest='book/coverage/'+o+'.json';archive='reports/full-coverage/owner25-originals-before-owner26-integration-v1/'+o+'.json';hashes[archive]=e['held25_ledger_sha256'];result['exact_replacements'].append({'destination':dest,'candidate':e['candidate_ledger'],'before_sha256':e['held25_ledger_sha256'],'original25_byte_copy':archive})
offer=offers['applied'];archive='reports/full-coverage/owner25-originals-before-owner26-integration-v1/applied-promotions.json';hashes[archive]=man['working_inputs_sha256']['book/coverage/applied-promotions.json'];result['exact_replacements'].append({'destination':'book/coverage/applied-promotions.json','candidate':{'file':offer['mapped_promotions'],'sha256':offer['mapped_promotions_sha256']},'before_sha256':hashes[archive],'original25_byte_copy':archive})
resultname='reports/full-coverage/SYNTHETIC-owner26-result.json';files[resultname]=result;hashes[resultname]=digest(result)
request={'status':'root_authorized_postintegration_owner26_interface_preparation','inventory':{'file':ns['INVENTORY'],'sha256':ns['INVENTORY_SHA']},'live_interface_helper':ref(IF),'integration_binding':{'file':bindingname,'sha256':hashes[bindingname]},'actual_integration_execution':{'file':execname,'sha256':hashes[execname]},'actual_integration_raw_log':{'file':logname,'sha256':hashes[logname]},'integration_result':{'file':resultname,'sha256':hashes[resultname]},'live_offer_destinations':{o:'book/coverage/checks/future26-core/SYNTHETIC-live-'+o+'.json' for o in offers},'interface_manifest_destination':'book/coverage/checks/future26-core/SYNTHETIC-interface-manifest.json'}
requestname='book/coverage/checks/future26-core/SYNTHETIC-request.json';files[requestname]=request
realread=ns['read'];realsha=ns['sha']
ns['read']=lambda n:files[n] if n in files else realread(n)
ns['sha']=lambda n:digest(outputs[n]) if n in outputs else hashes[n] if n in hashes else realsha(n)
outputs={};ns['write_new']=lambda n,d:outputs.setdefault(n,copy.deepcopy(d))
# Synthetic positive fixture: no filesystem writes, no synthetic install asserted real.
res=ns['interfaces'](requestname);manifest=outputs[request['interface_manifest_destination']]
assert len(outputs)==5 and set(manifest['owners'])==set(offers)
for o,record in manifest['owners'].items():
 live=outputs[request['live_offer_destinations'][o]];reverse=copy.deepcopy(live)
 for key in record['appended_live_interface_fields']:reverse.pop(key)
 for key in record['changed_original_fields']:reverse[key]=offers[o][key]
 assert reverse==offers[o] and live['mapped_ledger']=='book/coverage/'+o+'.json'
 if o=='modules':assert live['module_ledger']==live['mapped_ledger']
fixtures.append('synthetic full four-offer entire-body/time reverse including flat Core/two Module pointers/Applied promotions')
# Changed positive normalization scopes only; all synthetic data remain in memory.
originalimports=offers['modules'].get('required_external_import_dependencies')
offers['modules']['required_external_import_dependencies']=['verification/lean/SafeLearning/CompleteFoundationsSpectralModels.lean']
outputs.clear();ns['interfaces'](requestname);assert isinstance(outputs[request['live_offer_destinations']['modules']]['required_external_import_dependencies'],dict)
offers['modules']['required_external_import_dependencies']=originalimports
fixtures.append('synthetic unique import list normalized and original list retained reversibly')
originalrequired=offers['applied'].get('required_live_integration_evidence_sha256');hadrequired='required_live_integration_evidence_sha256' in offers['applied']
offers['applied']['required_live_integration_evidence_sha256']={'book/coverage/checks/root_integrate_owner26_candidates_v2.py':binding['helper']['sha256']}
outputs.clear();ns['interfaces'](requestname);assert 'book/coverage/checks/root_integrate_owner26_candidates_v2.py' in outputs[request['live_offer_destinations']['applied']]['required_live_integration_evidence_sha256']
fixtures.append('synthetic pre-existing Applied live-evidence merges without original body/time loss')
offers['applied']['required_live_integration_evidence_sha256']={logname:'0'*64}
reject('synthetic conflicting prior Applied live-evidence rejected',lambda:ns['interfaces'](requestname))
if hadrequired:offers['applied']['required_live_integration_evidence_sha256']=originalrequired
else:offers['applied'].pop('required_live_integration_evidence_sha256')
for key,bad in [('actual_exit_code',False),('exit_code',1),('exit_code',False),('actual_command',['python3',binding['helper']['file'],bindingname]),('command',['python3',binding['helper']['file'],bindingname]),('raw_log_sha256','0'*64),('actual_workdir','/tmp')]:
 prior=execution[key];execution[key]=bad;reject('synthetic integration rejects '+key+'='+repr(bad),lambda:ns['integration'](request));execution[key]=prior
before=execution['helper_sha256_after'];execution['helper_sha256_after']={binding['helper']['file']:'0'*64};reject('synthetic integration changed helper rejected',lambda:ns['integration'](request));execution['helper_sha256_after']=before
for key,bad in [('applied',False),('inventory_sha256','0'*64),('binding_manifest_sha256','0'*64),('all44111_frozen25_inputs_exact',False),('all1156_selected25_root_source_hashes_exact',False)]:
 before=result[key];result[key]=bad;reject('synthetic integration result rejects '+key,lambda:ns['integration'](request));result[key]=before
before=result['exact_replacements'];result['exact_replacements']=before[:-1];reject('synthetic missing fifth promotions replacement rejected',lambda:ns['integration'](request));result['exact_replacements']=before
row=result['exact_replacements'][0];before=row['before_sha256'];row['before_sha256']='0'*64;reject('synthetic old archive authorization digest rejected',lambda:ns['integration'](request));row['before_sha256']=before
# Current native held files unchanged; actual installation/interface outputs do not yet exist.
for o,n in names.items():
 if (ROOT/n).exists():assert sha(n)==(ref(n)['sha256'])
assert sha(IF)==IFS and sha(REQ)==RS
report={'status':'independent_owner26_live_interface_and_request_code_fixtures_passed','errors':[],'reviewer':'independent_foundations_agent','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':IFS,'helpers_sha256':{IF:IFS,REQ:RS},'helpers':{IF:ref(IF),REQ:ref(REQ)},'fixture_count':len(fixtures),'fixture_results':fixtures,'core_fixture_uses_genuine_final_offer':core_native,'synthetic_integration_fixture_scope_explicit':True,'whole_native_three_final_offer_bodies_reversed_exactly_in_memory':True,'four_actual_builder_or_compiler_records_fabricated':False,'actual_integration_or_live_interfaces_executed':False,'scope':'Full code/request delta review and isolated synthetic future-install accept/reject/reversal tests only. Existing three native final offers and their original body/time are read unchanged; Core uses actual flat finalizer contract. Reader0 is not an actual install, producer, global integrity, Lean or publication result.'}
assert not OUT.exists();OUT.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':'passed','observation':str(OUT),'sha256':hashlib.sha256(OUT.read_bytes()).hexdigest(),'fixtures':len(fixtures)}))

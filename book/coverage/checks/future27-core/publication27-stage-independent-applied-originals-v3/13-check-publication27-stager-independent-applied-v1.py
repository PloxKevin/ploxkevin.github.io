from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,shutil,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=Path('/tmp/root_stage_publication27_v1.py')
OUT=Path('/tmp/publication27-stager-independent-applied-observations-v1.json')
assert hashlib.sha256(HELPER.read_bytes()).hexdigest()=='aa77939ae82cd1b19b5e91135b014539e18f124ec7a0e3b981df31fc2975545f'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
fixtures=[]
code=compile(HELPER.read_text(),str(HELPER),'exec')
with tempfile.TemporaryDirectory(prefix='publication27-readonly-full-prepare-fixtures-') as td:
 root=Path(td)/'root';pub=Path(td)/'pub';root.mkdir();pub.mkdir()
 ns={'__name__':'fixture_module','__file__':str(HELPER)};exec(code,ns)
 ns['ROOT']=root;ns['PUB']=pub;selfn=ns['SELF'];(root/selfn).parent.mkdir(parents=True);shutil.copyfile(HELPER,root/selfn);ns['__file__']=str(root/selfn)
 ns['dirty']=lambda:set();ns['staged']=lambda:set()
 def put(n,d,where=root):
  p=where/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d if isinstance(d,bytes) else (json.dumps(d,separators=(',',':'))+'\n').encode());return p
 def cp(n):put(n,(root/n).read_bytes(),pub)
 proof={f'verification/lean/SafeLearning/Fixture{i}.lean':{'sha256':hashlib.sha256(b'-- synthetic fixture only\n').hexdigest()} for i in range(1175)}
 for n in proof:put(n,b'-- synthetic fixture only\n');cp(n)
 owners={};removed={o:[] for o in ('core','foundations','applied','modules')}
 removed['applied']=['verification/lean/SafeLearning/ExcludedMetadataA.lean','verification/lean/SafeLearning/ExcludedMetadataB.lean','verification/lean/SafeLearning/ExcludedMetadataC.lean']
 for o in removed:
  n='book/coverage/'+o+'.json';body={'proof_files':{p:{'unchanged_unreferenced_fixture':True} for p in removed[o]},'entire_other_original_metadata':{'owner':o}}
  put(n,body);owners[n]=sha(root/n);body['proof_files']={};put(n,body,pub)
 for n in ('book/coverage/inventory.json','book/coverage/material-corrections.json'):
  put(n,(ROOT/n).read_bytes());cp(n)
 assets={}
 for i in range(31):
  n=f'SafeLearning/fixture-asset-{i}.html';put(n,b'<p>synthetic asset only</p>\n');cp(n);assets[n]=sha(root/n)
 keep='reports/full-coverage/synthetic-retained-original.json';put(keep,b'{"synthetic_original":true}\n');cp(keep);keep_sha=sha(root/keep)
 oldfrozen={f'original26/old-{i}.json':keep_sha for i in range(47277)}
 bindingn='book/coverage/checks/synthetic-original-content-map.json'
 put(bindingn,{'original_input_count':47277,'input_bindings':[{'original_frozen_path':p,'sha256':h,'retained_input':keep} for p,h in oldfrozen.items()]})
 selection={'proof_files':proof,'proof_file_count':1175,'new_file_count':8,'coverage_complete':False,'previous_frozen_input_content_binding':{'file':bindingn,'sha256':sha(root/bindingn)}}
 put(ns['SELECTION'],selection);ns['EXPECTED_SELECTION']=sha(root/ns['SELECTION'])
 prior={'proof_files':dict(list(proof.items())[:1167]),'frozen_inputs_sha256':oldfrozen,'excluded_unreferenced_ledger_metadata':removed}
 put('reports/full-coverage/checkpoint-26-manifest.json',prior)
 frozen={**assets,**{n:sha(pub/n) for n in owners},**{n:sha(root/n) for n in ('book/coverage/inventory.json','book/coverage/material-corrections.json')},keep:keep_sha}
 for n,h in frozen.items():put('reports/full-coverage/checkpoint-27/'+n,(pub/n).read_bytes());assert sha(root/('reports/full-coverage/checkpoint-27/'+n))==h
 audit={'status':'passed','proof_sha256':{n:r['sha256'] for n,r in proof.items()},'proof_file_count':1175,'theorem_count':9644,'declarations':[{'name':f'Fixture.name{i}'} for i in range(9644)],'axiom_dependencies':{f'Fixture.name{i}':['propext'] for i in range(9644)},'allowed_standard_axioms':['propext','Classical.choice','Quot.sound'],'checks':[{'exit_code':0,'evidence_mode':'fresh_kernel_replay' if i<8 else 'reused_identical_module_and_transitive_local_imports'} for i in range(1175)]}
 put(ns['AUDIT'],audit)
 manifest={'selection_sha256':ns['EXPECTED_SELECTION'],'snapshot':'reports/full-coverage/checkpoint-27','status':'formal_verification_passed_partial_coverage','proof_files':proof,'successful_verification':{'report':ns['AUDIT'],'report_sha256':sha(root/ns['AUDIT'])},'frozen_inputs_sha256':frozen,'working_inputs_sha256':owners,'excluded_unreferenced_ledger_metadata':removed}
 put(ns['MANIFEST'],manifest)
 ledgern='reports/full-coverage/publication-checks/ledger-checkpoint-27.json'
 put(ledgern,{'integrity_status':'passed','errors':[],'mathematical_coverage_complete':False,'inventory_sha256':frozen['book/coverage/inventory.json'],'domains':[{'domain':o,'ledger_sha256':sha(pub/('book/coverage/'+o+'.json'))} for o in removed]})
 config_n='reports/full-coverage/pages27-config-preparation-v1.json';config_peer_n='book/coverage/checks/future27-core/pages27-config-independent-modules-output-v3.json'
 put('_config.yml',b'# synthetic native config\n',pub)
 config={'status':'passed_exact_pages27_archival_configuration_preparation_requires_actual_pages_build','coverage_complete':False,'exclusions':[f'archive/retired-{i}' for i in range(124)],'excluded_count':124,'website_budget_bytes':850000000,'config_sha256':sha(pub/'_config.yml'),'required_publication_files_sha256':assets,'helper':{'file':'book/coverage/checks/root_prepare_pages27_config_v3.py','sha256':'a'*64}}
 put(config_n,config)
 config_peer={'status':'passed','errors':[],'config_sha256':config['config_sha256'],'excluded_count':124,'closed_evidence_sha256':{},'original_closed_byte_aliases':{}}
 put(config_peer_n,config_peer)
 progress={'verified_checkpoint':{'proof_files':1175,'theorems':9644,'coverage_complete':False},'current_documented_material_corrections':55,'live_delivery_status':'checkpoint27_awaiting_actual_pages_and_live_checks'}
 put('book/coverage/progress.json',progress);put('reports/full-coverage/README.md',b'Synthetic audited status, delivery pending.\n')
 doc_n='reports/full-coverage/progress-checkpoint27-preparation-update-v2.json'
 put(doc_n,{'status':'passed_actual_checkpoint27_audit_documentation_prepared_delivery_pending','current_progress':{'file':'book/coverage/progress.json','sha256':sha(root/'book/coverage/progress.json')},'current_readme':{'file':'reports/full-coverage/README.md','sha256':sha(root/'reports/full-coverage/README.md')}})
 browser_n='reports/full-coverage/browser-checkpoint-27.json'
 put(browser_n,{'status':'passed_actual_changed_pages_and_exact_unchanged_evidence','source_sha256':assets,'page_count':29,'verified_viewport_count':145,'fresh_verified_viewport_count':10,'retained_verified_viewport_count':135,'screenshot_count':48})
 peer_n='book/coverage/checks/synthetic-stage-code-peer.json'
 put(peer_n,{'status':'passed_independent_checkpoint27_publication_stager_full_code_review','errors':[],'helper_sha256':sha(root/selfn)})
 helper_n='book/coverage/checks/synthetic-actual-helper.py';put(helper_n,b'# fixture helper, never executed\n')
 actual_n='reports/full-coverage/synthetic-current-execution.json';log_n='reports/full-coverage/synthetic-current-execution.log';put(log_n,b'Synthetic isolated fixture, not production.\n')
 actual={'status':'passed','actual_exit_code':0,'exit_code':0,'actual_workdir':str(root),'actual_command':['python3',helper_n],'helper_sha256_before':{helper_n:sha(root/helper_n)},'helper_sha256_after':{helper_n:sha(root/helper_n)},'log':log_n,'log_sha256':sha(root/log_n)}
 put(actual_n,actual)
 expected={n:sha(root/n) for n in (selfn,'book/coverage/progress.json','reports/full-coverage/README.md',actual_n,log_n,helper_n,config_n,config_peer_n,doc_n,browser_n,bindingn)}
 preparedn='reports/full-coverage/publication-prepared-27-files.json';prepared=sorted(set(frozen)|set(proof)|{keep});put(preparedn,prepared)
 plan_n='book/coverage/checks/synthetic-explicit-stage-plan.json'
 base_plan={'status':'root_explicit_audited27_publication_stage_inputs','helper':{'file':selfn,'sha256':sha(root/selfn)},'coverage_complete':False,'independent_helper_review':{'file':peer_n,'sha256':sha(root/peer_n)},'supplemental_inputs_sha256':expected,'actual_execution_records':[actual_n]}
 def run(plan=None):
  put(plan_n,base_plan if plan is None else plan);return ns['prepare'](plan_n)
 run();fixtures.append({'fixture':'complete synthetic native1175/9644/47277/31/3-prune prepare adapter','result':'accepted','scope':'Synthetic counts/objects and one repeated retained alias only; no production audit/peer/PUB/Git result inferred.'})
 def reject(label,fn):
  try:fn()
  except (AssertionError,KeyError,ValueError,TypeError,FileNotFoundError):fixtures.append({'fixture':label,'result':'rejected'});return
  raise AssertionError('unexpected acceptance '+label)
 def observe(label,fn):
  fn();fixtures.append({'fixture':label,'result':'accepted_requires_changes'})
 p=copy.deepcopy(base_plan);p['actual_execution_records']=[];observe('all actual current-family execution gates omitted',lambda:run(p))
 bad=copy.deepcopy(config_peer);bad['status']='failed';put(config_peer_n,bad);p=copy.deepcopy(base_plan);p['supplemental_inputs_sha256'][config_peer_n]=sha(root/config_peer_n);observe('config output peer explicitly failed with errors empty',lambda:run(p));put(config_peer_n,config_peer)
 bad=copy.deepcopy(config_peer);bad['closed_evidence_sha256']={'missing-original.json':'0'*64};put(config_peer_n,bad);p=copy.deepcopy(base_plan);p['supplemental_inputs_sha256'][config_peer_n]=sha(root/config_peer_n);observe('config output peer broken closed evidence is not validated',lambda:run(p));put(config_peer_n,config_peer)
 bad=copy.deepcopy(actual);bad['status']='failed';bad['command']=['python3','wrong-helper.py'];put(actual_n,bad);p=copy.deepcopy(base_plan);p['supplemental_inputs_sha256'][actual_n]=sha(root/actual_n);observe('execution status failed and conflicting command alias accepted',lambda:run(p));put(actual_n,actual)
 put('_config.yml',b'# stale unrelated Root config overwrites checked PUB config\n');p=copy.deepcopy(base_plan);p['supplemental_inputs_sha256']['_config.yml']=sha(root/'_config.yml');observe('supplemental Root _config.yml differs from approved native config',lambda:run(p))
 put(preparedn,prepared+['../outside-publication.json']);observe('prepared explicit whitelist contains parent traversal',run);put(preparedn,prepared)
 for label,value in [('actual boolFalse',False),('actual nonzero',1)]:
  bad=copy.deepcopy(actual);bad['actual_exit_code']=value;put(actual_n,bad);p=copy.deepcopy(base_plan);p['supplemental_inputs_sha256'][actual_n]=sha(root/actual_n);reject(label,lambda p=p:run(p));put(actual_n,actual)
 p=copy.deepcopy(base_plan);p['supplemental_inputs_sha256']['book/coverage/core.json']=sha(root/'book/coverage/core.json');reject('raw working owner overwrite in supplemental map',lambda:run(p))
 p=copy.deepcopy(base_plan);p['supplemental_inputs_sha256']['verification/lean/New.lean']='a'*64;reject('new proof source selected through supplemental map',lambda:run(p))
 bad=copy.deepcopy(audit);bad['axiom_dependencies']['Fixture.name0']=['sorryAx'];put(ns['AUDIT'],bad);reject('nonstandard axiom',run);put(ns['AUDIT'],audit)
 bad=copy.deepcopy(audit);bad['checks'][0]['exit_code']=False;put(ns['AUDIT'],bad);reject('boolFalse audit exit',run);put(ns['AUDIT'],audit)
 bad=copy.deepcopy(browser_n) if False else None
 old=ns['BUDGET'];ns['BUDGET']=1;reject('wrong/insufficient native budget',run);ns['BUDGET']=old
 assert not (root/ns['REPORT']).exists() and not (pub/ns['REPORT']).exists()
 result={'status':'requires_changes_independent_checkpoint27_publication_stager_full_code_and_native_fixture_review','errors':['Missing mandatory exact actual execution families/commands/status and alias checks','Failed config output peer and broken closed evidence accepted','Supplemental Root _config.yml can overwrite validated publication config','Prepared whitelist paths are not canonical/safe validated'],'helper':{'file':str(HELPER),'sha256':sha(HELPER)},'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'fixture_count':len(fixtures),'fixtures':fixtures,'producer_execution':False,'production_pub_or_git_mutation':False,'scope':'Exact full prepare() function executed in a synthetic TMP root/pub. Counts and future native records are explicitly synthetic adapters. Dirty/staged queries are mocked empty read-only sets; no real Git operation, no Root helper main or filesystem producer run.'}
 with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'fixtures':len(fixtures),'result':str(OUT),'sha256':sha(OUT)}))

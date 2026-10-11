from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,shutil,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=Path('/tmp/root_stage_publication27_v3.py')
OUT=Path('/tmp/publication27-stager-independent-applied-observations-v3.json')
assert hashlib.sha256(HELPER.read_bytes()).hexdigest()=='5878ca3465dca6deec70b467cdf14c4f33fa27c0ad8e5a18c3b9d4014059d69c'
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
 frozen={**{n:sha(root/n) for n in proof},**assets,**{n:sha(pub/n) for n in owners},**{n:sha(root/n) for n in ('book/coverage/inventory.json','book/coverage/material-corrections.json')},keep:keep_sha}
 for n,h in frozen.items():put('reports/full-coverage/checkpoint-27/'+n,(pub/n).read_bytes());assert sha(root/('reports/full-coverage/checkpoint-27/'+n))==h
 audit={'status':'passed','proof_sha256':{n:r['sha256'] for n,r in proof.items()},'proof_file_count':1175,'theorem_count':9644,'declarations':[{'name':f'Fixture.name{i}'} for i in range(9644)],'axiom_dependencies':{f'Fixture.name{i}':['propext'] for i in range(9644)},'allowed_standard_axioms':['propext','Classical.choice','Quot.sound'],'checks':[{'exit_code':0,'evidence_mode':'fresh_kernel_replay' if i<8 else 'reused_identical_module_and_transitive_local_imports'} for i in range(1175)]}
 put(ns['AUDIT'],audit)
 manifest={'selection_sha256':ns['EXPECTED_SELECTION'],'snapshot':'reports/full-coverage/checkpoint-27','status':'formal_verification_passed_partial_coverage','proof_files':proof,'successful_verification':{'report':ns['AUDIT'],'report_sha256':sha(root/ns['AUDIT'])},'frozen_inputs_sha256':frozen,'working_inputs_sha256':owners,'excluded_unreferenced_ledger_metadata':removed}
 put(ns['MANIFEST'],manifest)
 ledgern='reports/full-coverage/publication-checks/ledger-checkpoint-27.json'
 put(ledgern,{'integrity_status':'passed','errors':[],'mathematical_coverage_complete':False,'inventory_sha256':frozen['book/coverage/inventory.json'],'domains':[{'domain':o,'ledger_sha256':sha(pub/('book/coverage/'+o+'.json'))} for o in removed]})
 config_n='reports/full-coverage/pages27-config-preparation-v1.json';config_peer_n='book/coverage/checks/future27-core/pages27-config-independent-modules-output-v5.json'
 put('_config.yml',b'# synthetic native config\n',pub)
 config={'status':'passed_exact_pages27_archival_configuration_preparation_requires_actual_pages_build','coverage_complete':False,'exclusions':[f'archive/retired-{i}' for i in range(129)],'excluded_count':129,'website_budget_bytes':850000000,'config_sha256':sha(pub/'_config.yml'),'required_publication_files_sha256':assets,'helper':{'file':'book/coverage/checks/root_prepare_pages27_config_v5.py','sha256':'d7e2a4764f4678d6e7dc7c6443a732fc60224b733633db3a1646628801ebd101'}}
 put(config_n,config)
 config_peer={'status':'passed_independent_actual_checkpoint27_pages_configuration','helper':config['helper'],'errors':[],'config_sha256':config['config_sha256'],'excluded_count':129,'closed_evidence_sha256':{},'original_closed_byte_aliases':{}}
 put(config_peer_n,config_peer)
 progress={'verified_checkpoint':{'proof_files':1175,'theorems':9644,'coverage_complete':False},'current_documented_material_corrections':55,'live_delivery_status':'checkpoint27_awaiting_actual_pages_and_live_checks','live_delivery_evidence':None}
 put('book/coverage/progress.json',progress);put('reports/full-coverage/README.md',b'Synthetic audited status, delivery pending.\n')
 doc_n='reports/full-coverage/progress-checkpoint27-preparation-update-v2.json'
 put(doc_n,{'status':'passed_actual_checkpoint27_audit_documentation_prepared_delivery_pending','current_progress':{'file':'book/coverage/progress.json','sha256':sha(root/'book/coverage/progress.json')},'current_readme':{'file':'reports/full-coverage/README.md','sha256':sha(root/'reports/full-coverage/README.md')}})
 browser_n='reports/full-coverage/browser-checkpoint-27.json'
 put(browser_n,{'status':'passed_actual_changed_pages_and_exact_unchanged_evidence','source_sha256':assets,'page_count':29,'verified_viewport_count':145,'fresh_verified_viewport_count':10,'retained_verified_viewport_count':135,'screenshot_count':48})
 peer_n='book/coverage/checks/synthetic-stage-code-peer.json'
 put(peer_n,{'status':'passed_independent_checkpoint27_publication_stager_full_code_review','errors':[],'helper_sha256':sha(root/selfn)})
 execution_names=[];all_expected={};native_records={}
 for native_n,old_command in ns['REQUIRED_EXECUTIONS'].items():
  command=[v.replace(str(ROOT),str(root)) if isinstance(v,str) else v for v in old_command]
  command=[ns['EXPECTED_SELECTION'] if v=='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd' else v for v in command]
  ns['REQUIRED_EXECUTIONS'][native_n]=command
  helper_n=command[1]
  if helper_n==config['helper']['file']:put(helper_n,(ROOT/helper_n).read_bytes())
  elif not (root/helper_n).exists():put(helper_n,b'# synthetic fixture helper, never executed\n')
  log_n=Path(native_n).with_suffix('.log').as_posix();put(log_n,b'Synthetic exact-family wrapper adapter; no producer execution.\n')
  native={'status':'passed','actual_exit_code':0,'exit_code':0,'actual_workdir':str(root),'actual_command':command,'command':command,'helper_sha256_before':{helper_n:sha(root/helper_n)},'helper_sha256_after':{helper_n:sha(root/helper_n)},'log':log_n,'raw_log':log_n,'log_sha256':sha(root/log_n),'raw_log_sha256':sha(root/log_n)}
  put(native_n,native);native_records[native_n]=native;execution_names.append(native_n)
  all_expected.update({n:sha(root/n) for n in (native_n,log_n,helper_n)})
 closure_n='book/coverage/checks/synthetic-closed-independent-review.json';put(closure_n,{'scope':'Synthetic isolated closure only'})
 original_alias='/tmp/synthetic-config-original.json';aliases={original_alias+'::'+sha(root/closure_n):{'file':closure_n,'sha256':sha(root/closure_n)}}
 config_peer['closed_evidence_sha256']={original_alias:sha(root/closure_n)};put(config_peer_n,config_peer)
 production_n='book/coverage/checks/future27-core/modules-checkpoint27-production-output-independent-confirmation-v1.json'
 production={'status':'passed','errors':[],'selection':{'file':ns['SELECTION'],'sha256':ns['EXPECTED_SELECTION']},'proof_files':1175,'new_sources':8,'public_theorem_or_lemma_exports':9644,'old_frozen_paths_retained_exact':47277,'all_claim_declarations_selected':True,'coverage_complete':False,'actual_aggregate_or_publication_claim':False,'closed_evidence_sha256':{closure_n:sha(root/closure_n)}}
 put(production_n,production)
 # Only the hardcoded production peer SHA is changed in loaded fixture code, so it binds this honest synthetic peer. All guard function logic is exact.
 adapted_code=HELPER.read_text().replace("=='d2d887d743e2760825e765580bbb0f12f83829636b6e9696e40abe33cc2830c8'","=='"+sha(root/production_n)+"'")
 exact_fn_ns={'__name__':'fixture_module','__file__':str(root/selfn)};exec(compile(adapted_code,str(HELPER),'exec'),exact_fn_ns)
 for k in ['ROOT','PUB','EXPECTED_SELECTION','REQUIRED_EXECUTIONS','dirty','staged']:exact_fn_ns[k]=ns[k]
 ns=exact_fn_ns
 expected={n:sha(root/n) for n in (selfn,'book/coverage/progress.json','reports/full-coverage/README.md',config_n,config_peer_n,doc_n,browser_n,bindingn,closure_n,production_n)};expected.update(all_expected)
 preparedn='reports/full-coverage/publication-prepared-27-files.json'
 external=['reports/full-coverage/README.md','reports/full-coverage/integration-27.json',ns['MANIFEST'],ns['SELECTION'],'reports/full-coverage/checkpoint-27-ledger-manifest.json',browser_n,'reports/full-coverage/browser-corrections-27-inputs.json','reports/full-coverage/browser-corrections-27.json','reports/full-coverage/browser-corrections-27.log']
 for directory in ['reports/full-coverage/lean-checkpoint-27','reports/full-coverage/browser-artifacts-27']:(root/directory).mkdir(parents=True,exist_ok=True)
 external += [p.relative_to(root).as_posix() for directory in ('reports/full-coverage/lean-checkpoint-27','reports/full-coverage/browser-artifacts-27') for p in (root/directory).glob('*') if p.is_file()]
 prepared=sorted(set(frozen)|{n for n in external if (root/n).is_file()})
 for n in prepared:
  if not (pub/n).exists():cp(n)
 put(preparedn,prepared)
 plan_n='book/coverage/checks/synthetic-explicit-stage-plan.json'
 base_plan={'status':'root_explicit_audited27_publication_stage_inputs','helper':{'file':selfn,'sha256':sha(root/selfn)},'coverage_complete':False,'independent_helper_review':{'file':peer_n,'sha256':sha(root/peer_n)},'supplemental_inputs_sha256':expected,'actual_execution_records':execution_names,'original_byte_aliases':aliases,'prepared_file_list':{'file':preparedn,'sha256':sha(root/preparedn)}}
 def run(plan=None):
  put(plan_n,base_plan if plan is None else plan);return ns['prepare'](plan_n)
 run();fixtures.append({'fixture':'complete synthetic native1175/9644/47277/31/3-prune full prepare adapter','result':'accepted','scope':'Synthetic counts/objects and one repeated retained alias only. Fixed production peer SHA, selection SHA and absolute verify ROOT are explicit synthetic adapters; all guard logic is exact. No production audit/peer/PUB/Git result inferred.'})
 def reject(label,fn):
  try:fn()
  except (AssertionError,KeyError,ValueError,TypeError,FileNotFoundError):fixtures.append({'fixture':label,'result':'rejected'});return
  raise AssertionError('unexpected acceptance '+label)
 def accepted(label,fn):fn();fixtures.append({'fixture':label,'result':'accepted'})
 # Narrow repair fixtures compose the entire measured v2 planned suite and separate genuine counterexample.
 oldsource=Path('/tmp/root_stage_publication27_v2.py').read_text()
 expectedsource=oldsource.replace("SELF='book/coverage/checks/root_stage_publication27_v2.py'","SELF='book/coverage/checks/root_stage_publication27_v3.py'").replace(" assert d['helper_sha256_before']==d['helper_sha256_after'] and d['helper_sha256_after']", " assert type(d['helper_sha256_before']) is dict and type(d['helper_sha256_after']) is dict\n assert d['helper_sha256_before']==d['helper_sha256_after'] and d['helper_sha256_after']\n assert command[1] in d['helper_sha256_after']")
 assert HELPER.read_text()==expectedsource
 previous=json.loads(Path('/tmp/publication27-stager-independent-applied-observations-v2.json').read_bytes());assert previous['fixture_count']==61
 p=copy.deepcopy(base_plan);p['supplemental_inputs_sha256'][keep]='0'*64;reject('frozen supplemental path digest override',lambda:run(p))
 p=copy.deepcopy(base_plan);p['actual_execution_records']=[];reject('exact seventeen-family requirement retained',lambda:run(p))
 p=copy.deepcopy(base_plan);p['prepared_file_list']['sha256']='0'*64;reject('exact prepared-path-list digest gate retained',lambda:run(p))
 n=execution_names[0];original=native_records[n];command=ns['REQUIRED_EXECUTIONS'][n]
 for n1,c in ns['REQUIRED_EXECUTIONS'].items():accepted('designated helper current pinned for native family '+n1,lambda n=n1,c=c:ns['actual'](n,c))
 unrelated='book/coverage/checks/unrelated-fixture.py';put(unrelated,b'# not the executed helper; fixture only\n')
 bad=copy.deepcopy(original);bad['helper_sha256_before']=bad['helper_sha256_after']={unrelated:sha(root/unrelated)};put(n,bad);reject('exact command but designated helper omitted and unrelated file pinned',lambda:ns['actual'](n,command));put(n,original)
 for field in ['helper_sha256_before','helper_sha256_after']:
  bad=copy.deepcopy(original);bad[field]=list(bad[field].items());put(n,bad);reject('helper map must be exact dict: '+field,lambda:ns['actual'](n,command));put(n,original)
 bad=copy.deepcopy(original);bad['helper_sha256_before']=bad['helper_sha256_after']=[];put(n,bad);reject('matching non-dict helper maps',lambda:ns['actual'](n,command));put(n,original)
 bad=copy.deepcopy(original);bad['actual_exit_code']=False;put(n,bad);reject('strict boolFalse native exit retained',lambda:ns['actual'](n,command));put(n,original)
 bad=copy.deepcopy(original);bad['command']=['python3','wrong.py'];put(n,bad);reject('conflicting command alias retained',lambda:ns['actual'](n,command));put(n,original)
 bad=copy.deepcopy(original);bad['raw_log_sha256']='0'*64;put(n,bad);reject('conflicting raw log hash alias retained',lambda:ns['actual'](n,command));put(n,original)
 link='book/coverage/checks/synthetic-closed-symlink.json';(root/link).symlink_to(root/closure_n)
 altered=copy.deepcopy(aliases);next(iter(altered.values()))['file']=link;expected_link={**expected,link:sha(root/closure_n)}
 reject('typed canonical absolute-original alias resolves final symlink',lambda:ns['closed_peer'](config_peer_n,config_peer['status'],altered,expected_link))
 (root/link).unlink()
 with tempfile.TemporaryDirectory(prefix='publication27-alias-escape-') as other:
  (root/'escape').symlink_to(other,target_is_directory=True)
  reject('typed alias parent symlink escapes root',lambda:ns['safe'](root,'escape/closed.json'))
  (root/'escape').unlink()
 reject('absolute original lacking explicit digest-qualified alias',lambda:ns['closed_peer'](config_peer_n,config_peer['status'],{},expected))
 bad=copy.deepcopy(config_peer);bad['status']='failed';put(config_peer_n,bad);reject('strict independent output status retained',lambda:ns['closed_peer'](config_peer_n,config_peer['status'],aliases,expected));put(config_peer_n,config_peer)
 # Exact 129 native exclusion gate is unchanged by the repair. Exercise it as the full producer prepare logic, with future synthetic count honestly recorded.
 bad=copy.deepcopy(config);bad['exclusions']=bad['exclusions'][:-1];bad['excluded_count']=128;put(config_n,bad);reject('full native config exclusion count128 rejects under required129',run);put(config_n,config)
 assert not (root/ns['REPORT']).exists() and not (pub/ns['REPORT']).exists()
 # Exact current native read-only family checks; no call to prepare() or main() in real Root/PUB.
 actual_ns={'__name__':'native_readonly_module','__file__':str(HELPER)};exec(code,actual_ns)
 native_observations=[]
 for n,command in actual_ns['REQUIRED_EXECUTIONS'].items():
  if (ROOT/n).exists():
   d=actual_ns['actual'](n,command);native_observations.append({'file':n,'sha256':sha(ROOT/n),'status':d['status'],'actual_exit_code':d.get('actual_exit_code'),'helper_names':sorted(d['helper_sha256_after']),'raw_log_sha256':d['log_sha256']})
   assert command[1] in d['helper_sha256_after'],('actual designated command helper absent',n)
 # Audit main() AST: explicit -f NUL whitelist, no conditional production paths, rehash current config after copies before Git staging.
 tree=ast.parse(HELPER.read_text());main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main');m=ast.unparse(main)
 assert "'add', '-f', '--pathspec-from-file=-', '--pathspec-file-nul'" in m
 assert 'config_sha' in m and m.index("sha(safe(PUB, '_config.yml'))")<m.index("'add', '-f'")
 result={'status':'passed_independent_checkpoint27_publication_stager_full_code_and_native_fixture_review','errors':[],'helper':{'file':str(HELPER),'sha256':sha(HELPER)},'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'fixture_count':len(fixtures),'fixtures':fixtures,'entire_prior_v2_fixture_observations':previous,'prior61_fixture_scope_preserved':True,'actual_native_read_only_families':native_observations,'producer_execution':False,'production_pub_or_git_mutation':False,'scope':'Full source/delta read and exact full prepare() logic in synthetic TMP root/PUB. The verifier ROOT, selection hash and hardcoded production peer hash are explicitly synthetic fixture adapters. Counts and repeated47,277 logical content rows represent one physical retained alias, not a production output claim. Exact actual()/closed_peer()/safe() guard functions are exercised directly. Dirty/staged queries are mocked empty; actual 17 available current native wrappers are read only and designated helper keys independently checked. No real Git operation, Root main(), publication preparation or copy executed.'}
 with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'fixtures':len(fixtures),'result':str(OUT),'sha256':sha(OUT),'actual_native_families':len(native_observations)}))

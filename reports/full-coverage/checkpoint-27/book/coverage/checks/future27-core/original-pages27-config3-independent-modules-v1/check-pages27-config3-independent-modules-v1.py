from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,importlib.util,tempfile,copy,subprocess,ast
R=Path('/home/oxrexkevin/SafetyBased');SOURCE=Path('/tmp/root_prepare_pages27_config_v3.py');OLD=Path('/tmp/root_prepare_pages27_config_v2.py');RESULT=Path('/tmp/pages27-config3-independent-modules-check-result-v1.json');assert not RESULT.exists()
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(SOURCE)=='bd6e79efaeaec954549be2e8d0158ee494244c955874aa1a7441eca601caf2cb'
assert H(OLD)=='12e7fb58ddd16dda549445f48a23f03ac2ac473992ce5b7306e27761ffc30f6a'
spec=importlib.util.spec_from_file_location('pages27config3_independent',SOURCE);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
assert m.HELPER=='book/coverage/checks/root_prepare_pages27_config_v3.py' and m.EXPORT_HELPER=='book/coverage/export_audit27_v3.py' and H(R/m.EXPORT_HELPER)==m.EXPORT_HELPER_SHA
assert len(m.NEW_LITERAL_EXCLUSIONS)==8 and len(m.RETIRED_COMPLETED26_FILES)==2 and len(m.DUPLICATE_INVENTORIES)==4
original_code=SOURCE.read_text();restored=original_code.replace("HELPER='book/coverage/checks/root_prepare_pages27_config_v3.py'\nEXPORT_HELPER='book/coverage/export_audit27_v3.py'\nEXPORT_HELPER_SHA='f1f99c8ae8809dcebf715b308b0d40e5c03bca650cd7db72532269adef1ed8a4'", "HELPER='book/coverage/checks/root_prepare_pages27_config_v2.py'")
restored=restored.replace(" assert audit['proof_sha256']=={n:r['sha256'] for n,r in selection['proof_files'].items()}\n success=manifest['successful_verification']\n assert success['report']==audit_name and success['report_sha256']==sha(safe(root,audit_name))\n assert success['proof_file_count']==1175 and success['theorem_count']==9644\n assert type(success['all_check_exit_codes']) is int and success['all_check_exit_codes']==0\n",'').replace(" assert sha(safe(root,EXPORT_HELPER))==EXPORT_HELPER_SHA\n",'').replace("['python3',EXPORT_HELPER,'--snapshot'", "['python3','book/coverage/export_audit.py','--snapshot'").replace(" assert len(browser['qa_source_sha256'])==2\n for n,h in browser['qa_source_sha256'].items():same(root,pub,n,h);required[n]=h\n", " assert all(sha(safe(root,n))==h for n,h in browser['qa_source_sha256'].items())\n")
assert restored==OLD.read_text(),'full original2 restored by only reviewed delta'
# The actual retirement roots/publication/GitHEAD and original hashes are checked
# independently. No future27 report or producer result is synthesized as native.
native={}
for n,h in m.RETIRED_COMPLETED26_FILES.items():m.tracked_exact(R,m.PUB,n,h);native[n]=h
for n,h in m.DUPLICATE_INVENTORIES.items():assert H(R/n)==h;native[n]=h
assert H(m.PUB/'_config.yml')==m.BEFORE
native_config=(m.PUB/'_config.yml').read_bytes();assert native_config.decode()==m.HEADER+''.join('  - '+n+'\n' for n in sorted({x[4:] for x in native_config.decode().splitlines() if x.startswith('  - ')}))
old_manifest=json.loads((R/'reports/full-coverage/checkpoint-26-manifest.json').read_bytes());assert len(old_manifest['excluded_unreferenced_ledger_metadata']['applied'])==3
for n,h in json.loads((R/'reports/full-coverage/browser-checkpoint-26.json').read_bytes())['qa_source_sha256'].items():m.same(R,m.PUB,n,h);native[n]=h
fixtures=[]
def passed(name):fixtures.append({'name':name,'result':'passed','kind':'isolated synthetic code fixture'})
def reject(name,f):
 try:f()
 except(AssertionError,ValueError,KeyError,subprocess.CalledProcessError):passed(name);return
 raise AssertionError('unexpected accepted fixture: '+name)
for v in [False,True,0.0,None,'0',1,-1]:reject('strict_exit_reject_'+repr(v),lambda v=v:m.zero({'actual_exit_code':v}))
reject('conflicting_present_exit_aliases',lambda:m.zero({'actual_exit_code':0,'exit_code':1}));m.zero({'actual_exit_code':0,'exit_code':0});passed('integer_zero_aliases_accept')
for n in ['../escape','/absolute','a//b','a/../b','a*','a?','a[0]','a{b','nul\x00x']:
 reject('canonical_name_reject_'+repr(n),lambda n=n:m.canonical_name(n))
for n in ['reports/full-coverage/lean-checkpoint-26/verification-original.json','reports/full-coverage/browser-artifacts-25/a.png','reports/full-coverage/browser-artifacts-26/a.png','reports/full-coverage/browser-artifacts-27/a.png']:
 assert m.kept(n,{x[4:] for x in native_config.decode().splitlines() if x.startswith('  - ')}|m.NEW_LITERAL_EXCLUSIONS);passed('required_download_inclusion_'+n)
# Full native implementation with isolated synthetic future artifacts. Only
# fingerprint fixture constants (inventories, retirement files) are substituted;
# real source55 two page bytes, exporter3 and original116 config bytes are copied.
base=Path(tempfile.mkdtemp(prefix='pages27-config3-full-fixture-'));root=base/'root';pub=base/'pub';root.mkdir();pub.mkdir();m.ROOT=root;m.PUB=pub
for d in [root,pub]:(d/'_config.yml').write_bytes(native_config)
def put(n,b,both=True):
 for d in ([root,pub] if both else [root]):
  p=d/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return hashlib.sha256(b).hexdigest()
def js(n,d,both=True):return put(n,(json.dumps(d,sort_keys=True,separators=(',',':'))+'\n').encode(),both)
def body(n):return json.loads((root/n).read_bytes())
put(m.HELPER,SOURCE.read_bytes());put(m.EXPORT_HELPER,(R/m.EXPORT_HELPER).read_bytes())
assets={}
actual_assets={n:h for n,h in old_manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(actual_assets)==31
for n in actual_assets:
 b=(R/n).read_bytes() if n in ['SafeLearning/lyapunov-mpc.html','SafeLearning/verification.html'] else ('fixture '+n).encode();assets[n]=put(n,b)
m.INVENTORY55=put('book/coverage/inventory.json',b'fixture-current55-inventory');m.CORRECTIONS55=put('book/coverage/material-corrections.json',b'fixture-current55-corrections')
m.DUPLICATE_INVENTORIES={n:put(n,b'fixture-'+n.encode()) for n in m.DUPLICATE_INVENTORIES}
m.RETIRED_COMPLETED26_FILES={n:js(n,{'fixture':'exact retired bytes '+n}) for n in m.RETIRED_COMPLETED26_FILES}
subprocess.run(['git','init','-q'],cwd=pub,check=True)
subprocess.run(['git','add','--',*m.RETIRED_COMPLETED26_FILES],cwd=pub,check=True)
subprocess.run(['git','-c','user.name=Isolated Fixture','-c','user.email=fixture@example.invalid','-c','commit.gpgsign=false','commit','-qm','isolated retired exact fixture'],cwd=pub,check=True)
qa={n:put(n,('fixture '+n).encode()) for n in ['qa/learning_review.mjs','qa/book_browser_checks.mjs']}
proofs={'verification/lean/SafeLearning/Fixture'+str(i)+'.lean':{'sha256':hashlib.sha256(str(i).encode()).hexdigest()} for i in range(1175)}
sel={'proof_files':proofs,'proof_file_count':1175,'new_file_count':8};selname='reports/full-coverage/checkpoint-27-selection.json';selsha=js(selname,sel)
audname='reports/full-coverage/lean-checkpoint-27/verification-original.json';aud={'status':'passed','proof_file_count':1175,'theorem_count':9644,'proof_sha256':{n:r['sha256'] for n,r in proofs.items()},'declarations':['Fixture.'+str(i) for i in range(9644)],'axiom_dependencies':[[] for i in range(9644)],'checks':[{'exit_code':0,'evidence_mode':'fresh_kernel_replay' if i<8 else 'reused_identical_module_and_transitive_local_imports'} for i in range(1175)]};audsha=js(audname,aud)
js('reports/full-coverage/lean-checkpoint-26/verification-original.json',{'status':'synthetic baseline download fixture'})
js('reports/full-coverage/integration-27.json',{'status':'synthetic integration download fixture'})
snapshot='reports/full-coverage/checkpoint-27';frozen=dict(assets);frozen.update({'book/coverage/inventory.json':m.INVENTORY55,'book/coverage/material-corrections.json':m.CORRECTIONS55});frozen.update(m.DUPLICATE_INVENTORIES)
removed={owner:list(old_manifest['excluded_unreferenced_ledger_metadata'][owner]) for owner in ['core','foundations','applied','modules']};working={}
for owner in removed:
 n='book/coverage/'+owner+'.json';w={'proof_files':{'fixture-selected.lean':{'status':'synthetic'}}|{x:{'status':'synthetic unreferenced'} for x in removed[owner]},'body_and_time':'unchanged synthetic whole record'}
 working[n]=js(n,w,False);f=copy.deepcopy(w)
 for x in removed[owner]:f['proof_files'].pop(x)
 p=pub/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((json.dumps(f,sort_keys=True,separators=(',',':'))+'\n').encode());frozen[n]=H(p)
n='book/coverage/applied-promotions.json';working[n]=frozen[n]=js(n,{'body_and_time':'unchanged synthetic promotions'})
for n,h in frozen.items():
 p=root/snapshot/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((pub/n).read_bytes())
oldfixture={'excluded_unreferenced_ledger_metadata':removed};js('reports/full-coverage/checkpoint-26-manifest.json',oldfixture)
# Retirement fixture bytes must be updated after the actual-oldmanifest metadata
# fixture, then re-committed so the unchanged real tracked_exact path is exercised.
m.RETIRED_COMPLETED26_FILES['reports/full-coverage/checkpoint-26-manifest.json']=H(root/'reports/full-coverage/checkpoint-26-manifest.json')
subprocess.run(['git','add','--',*m.RETIRED_COMPLETED26_FILES],cwd=pub,check=True);subprocess.run(['git','-c','user.name=Isolated Fixture','-c','user.email=fixture@example.invalid','-c','commit.gpgsign=false','commit','-qm','isolated retired manifest metadata fixture'],cwd=pub,check=True)
manifest={'status':'formal_verification_passed_partial_coverage','snapshot':snapshot,'selection_sha256':selsha,'proof_files':proofs,'frozen_inputs_sha256':frozen,'working_inputs_sha256':working,'excluded_unreferenced_ledger_metadata':removed,'successful_verification':{'report':audname,'report_sha256':audsha,'proof_file_count':1175,'theorem_count':9644,'all_check_exit_codes':0}};manname='reports/full-coverage/checkpoint-27-manifest.json';js(manname,manifest)
def execution(name,command,extra=None):
 log=name.removesuffix('.json')+'.log';lh=put(log,b'isolated synthetic actual-record fixture log');d={'actual_exit_code':0,'actual_command':command,'actual_workdir':str(root),'log':log,'log_sha256':lh};d.update(extra or {});js(name,d)
for stem,cmd in [('verify-checkpoint27',['python3','reports/full-coverage/checkpoint-27/verification/lean/verify.py','--reuse-kernel-from',str(root/'reports/full-coverage/checkpoint-26')]),('export-checkpoint27',['python3',m.EXPORT_HELPER,'--snapshot','reports/full-coverage/checkpoint-27','--output','reports/full-coverage/lean-checkpoint-27']),('prepare-publication27',['python3','book/coverage/prepare_publication.py','27'])]:execution('reports/full-coverage/'+stem+'-execution-v1.json',cmd)
freshreport='reports/full-coverage/browser-source55-27-v1.json';freshsha=js(freshreport,{'status':'synthetic fresh browser fixture'})
freshname='reports/full-coverage/browser-source55-27-v1-execution.json';execution(freshname,['node','qa/learning_review.mjs','--report',freshreport,'--artifacts','reports/full-coverage/browser-artifacts-source55-27-v1','lyapunov-mpc.html','verification.html'],{'source_sha256_before':assets,'source_sha256_after':assets,'qa_source_sha256':qa,'report':freshreport,'report_sha256':freshsha})
browser={'status':'passed_actual_changed_pages_and_exact_unchanged_evidence','page_count':29,'requested_viewport_count':145,'verified_viewport_count':145,'fresh_verified_viewport_count':10,'retained_verified_viewport_count':135,'screenshot_count':48,'skipped_capture_target_count':10,'source_sha256':assets,'qa_source_sha256':qa,'actual_execution':freshname,'actual_execution_sha256':H(root/freshname)};browsername='reports/full-coverage/browser-checkpoint-27.json';js(browsername,browser)
aliases=[]
for i in range(48):
 n='reports/full-coverage/browser-artifacts-27/capture-'+str(i)+'.png';h=put(n,('synthetic capture'+str(i)).encode());x={'file':n,'sha256':h,'evidence_mode':'fresh_actual_source55_browser_execution' if i<4 else 'retained_exact_unchanged_source_and_QA_original26_record'}
 if i<4:x['original']='reports/full-coverage/browser-artifacts-source55-27-v1/capture-'+str(i)+'.png';put(x['original'],(pub/n).read_bytes())
 aliases.append(x)
js('reports/full-coverage/browser-corrections-27-inputs.json',{'actual_execution':{'file':freshname,'sha256':H(root/freshname)},'screenshot_aliases':aliases})
def absent():assert all(not (d/n).exists() for d in [root,pub] for n in [m.REPORT,m.BACKUP,m.BACKUP_RECORD]);assert H(pub/'_config.yml')==m.BEFORE
old,after,report,outputs=m.prepare(root,pub);absent();assert report['excluded_count']==124 and report['selected_sources']==1175 and report['theorem_exports']==9644 and report['screenshot_downloads']==48 and len(report['new_literal_exclusions'])==8
assert set(outputs)=={m.REPORT,m.BACKUP,m.BACKUP_RECORD} and outputs[m.BACKUP]==native_config
assert report['prospective_included_website_bytes_including_native_records']==report['prospective_included_website_bytes_before_new_native_records']+sum(len(x) for x in outputs.values()) and report['prospective_included_website_bytes_including_native_records']<m.BUDGET
assert all(n in report['required_publication_files_sha256'] for n in qa);passed('full_readonly_prepare_all_native_shape_gates_and_exact_serialized_byte_budget')
def mutation(name,n,change):
 p=root/n;before=p.read_bytes();d=json.loads(before);change(d);p.write_bytes((json.dumps(d,sort_keys=True,separators=(',',':'))+'\n').encode())
 try:reject(name,lambda:m.prepare(root,pub));absent()
 finally:p.write_bytes(before)
mutation('same_count_different_audit_source_map_rejected',audname,lambda d:d['proof_sha256'].__setitem__(next(iter(proofs)),'0'*64))
mutation('manifest_successful_report_hash_drift_rejected',manname,lambda d:d['successful_verification'].__setitem__('report_sha256','0'*64))
mutation('bool_false_manifest_success_exit_rejected',manname,lambda d:d['successful_verification'].__setitem__('all_check_exit_codes',False))
mutation('wrong_browser_fresh_count_rejected',browsername,lambda d:d.__setitem__('fresh_verified_viewport_count',9))
mutation('wrong_actual_export_command_rejected','reports/full-coverage/export-checkpoint27-execution-v1.json',lambda d:d['actual_command'].__setitem__(1,'book/coverage/export_audit.py'))
mutation('actual_conflicting_command_alias_rejected','reports/full-coverage/export-checkpoint27-execution-v1.json',lambda d:d.__setitem__('command',['false']))
mutation('actual_bool_false_exit_rejected','reports/full-coverage/export-checkpoint27-execution-v1.json',lambda d:d.__setitem__('actual_exit_code',False))
mutation('changed_three_metadata_removal_scope_rejected',manname,lambda d:d['excluded_unreferenced_ledger_metadata']['applied'].pop())
for n in [next(iter(qa)),aliases[0]['file'],aliases[0]['original']]:
 p=pub/n;b=p.read_bytes();p.write_bytes(b+b'drift')
 try:reject('publication_exact_bytes_reject_'+n,lambda:m.prepare(root,pub));absent()
 finally:p.write_bytes(b)
oldbudget=m.BUDGET;m.BUDGET=1
try:reject('prewrite_exact_serialized_native_budget_overflow_rejected',lambda:m.prepare(root,pub));absent()
finally:m.BUDGET=oldbudget
for n in [m.REPORT,m.BACKUP,m.BACKUP_RECORD]:
 p=root/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'existing')
 try:reject('unused_output_destination_guard_'+n,lambda:m.prepare(root,pub))
 finally:p.unlink()
absent();old2,after2,report2,outputs2=m.prepare(root,pub);assert old2==old and after2==after;passed('all_rejections_preserve_original_config_and_leave_all_outputs_absent')
closed={str(SOURCE):H(SOURCE),str(OLD):H(OLD),m.EXPORT_HELPER:m.EXPORT_HELPER_SHA,**native}
result={'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':'book/coverage/checks/root_prepare_pages27_config_v3.py','sha256':H(SOURCE)},'helper_sha256':H(SOURCE),'source_reviewed':{'file':str(SOURCE),'sha256':H(SOURCE)},'original_unexecuted_helper2':{'file':str(OLD),'sha256':H(OLD)},'entire_original_helper2_restored_by_exact_reviewed_delta':True,'required_literal_exclusions':124,'new_literal_exclusions':sorted(m.NEW_LITERAL_EXCLUSIONS),'selected_sources':1175,'public_theorems':9644,'fixtures':fixtures,'fixture_count':len(fixtures),'native_retirement_root_publication_tracked_HEAD_exact':native,'actual_original_current_configuration_sha256':m.BEFORE,'fixture_serialized_native_records_bytes':sum(len(v) for v in outputs.values()),'fixture_budget_bytes':report['prospective_included_website_bytes_including_native_records'],'fixture_directory':str(base),'closed_evidence_sha256':closed,'actual_production_execution_claim':False,'scope':'Independent full helper3 code/native historical archive contracts and isolated synthetic full future27 prepare/reject fixtures. No future audit/browser/PUB preparation/configuration producer executed. Synthetic record/retirement/inventory fingerprint inputs are explicitly substituted only in isolated fixture module; real current55 two page bytes/export3/original116 config bytes and native old26 ROOT/PUB/trackedHEAD archives independently checked. Every actual future27 audit/export/prepare/browser result and actual budget remain required before producer.'}
RESULT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'passed','result':str(RESULT),'sha256':H(RESULT),'fixtures':len(fixtures)}))

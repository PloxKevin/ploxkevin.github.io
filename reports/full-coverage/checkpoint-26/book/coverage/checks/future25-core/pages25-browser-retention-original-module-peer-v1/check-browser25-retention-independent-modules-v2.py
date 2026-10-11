from pathlib import Path
from datetime import datetime,timezone
import importlib.util,json,hashlib,copy,ast
R=Path('/home/oxrexkevin/SafetyBased');H='book/coverage/checks/root_retain_browser25_exact24_v2.py';OLD='book/coverage/checks/root_retain_browser25_exact24_v1.py';OUT=Path('/tmp/browser25-exact-retention-independent-modules-review-v1.json')
def hashp(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((R/n).read_text())
def ref(n):return {'file':n,'sha256':hashp(R/n)}
def zero(d):
 vals=[d[k] for k in ('actual_exit_code','exit_code') if k in d];assert vals and all(type(x)is int and x==0 for x in vals)
assert not OUT.exists();assert hashp(R/H)=='9e33b019d0aeb245535f39d15222923190695972a98c9fb70f67d40d9e0908a5'
spec=importlib.util.spec_from_file_location('retention',R/H);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
new=(R/H).read_text();old=(R/OLD).read_text();reverse=new.replace("    page_qa = {Path(n).name: h for n, h in qa.items()}\n    assert len(page_qa) == len(qa) == 2\n",'').replace("assert page['qa_source_sha256'] == page_qa","assert page['qa_source_sha256'] == qa")
assert reverse==old
r=read(m.ORIGINAL);assert hashp(R/m.ORIGINAL)==m.ORIGINAL_SHA
manifest=read('reports/full-coverage/checkpoint-25-manifest.json');assert manifest['status']=='formal_verification_passed_partial_coverage'
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')};qa=r['qa_source_sha256'];assert len(assets)==31 and len(qa)==2
for n,h in assets.items():assert hashp(R/n)==hashp(m.PUB/n)==h
for n,h in qa.items():assert hashp(R/n)==hashp(m.PUB/n)==h
shots={s['path']:hashp(R/s['path']) for p in r['pages'] for s in p['screenshots'] if s['status']=='passed'}
assert m.validate(r,assets,qa,shots)==(48,10)
a=read(r['actual_execution']);zero(a);assert hashp(R/r['actual_execution'])==r['actual_execution_sha256'];assert hashp(R/a['log'])==a['log_sha256'];assert a['source_sha256_before']==a['source_sha256_after']==assets
assert hashp(R/r['fresh_run_inputs'])==r['fresh_run_inputs_sha256']
fixtures=[]
def reject(label,mutator):
 rr=copy.deepcopy(r);aa=copy.deepcopy(assets);qq=copy.deepcopy(qa);ss=copy.deepcopy(shots);mutator(rr,aa,qq,ss)
 try:m.validate(rr,aa,qq,ss)
 except (AssertionError,KeyError):fixtures.append({'name':label,'expected':'reject','actual':'reject'});return
 raise AssertionError(label)
for key,val in [('status','passed'),('coverage_complete',True),('page_count',28),('requested_viewport_count',144),('verified_viewport_count',144),('fresh_verified_viewport_count',0),('retained_verified_viewport_count',145),('screenshot_count',47),('skipped_capture_target_count',9)]:reject('mutated_'+key,lambda rr,aa,qq,ss,k=key,v=val:rr.__setitem__(k,v))
reject('asset_changed',lambda rr,aa,qq,ss:aa.__setitem__(next(iter(aa)),'0'*64))
reject('asset_missing',lambda rr,aa,qq,ss:aa.pop(next(iter(aa))))
reject('QA_changed',lambda rr,aa,qq,ss:qq.__setitem__(next(iter(qq)),'0'*64))
reject('page_status',lambda rr,aa,qq,ss:rr['pages'][0].__setitem__('status','failed'))
reject('page_errors',lambda rr,aa,qq,ss:rr['pages'][0].__setitem__('errors',['error']))
reject('page_QA_fullpaths_rejected',lambda rr,aa,qq,ss:rr['pages'][0].__setitem__('qa_source_sha256',qq))
reject('page_QA_hash_changed',lambda rr,aa,qq,ss:rr['pages'][0]['qa_source_sha256'].__setitem__('learning_review.mjs','0'*64))
reject('viewport_missing',lambda rr,aa,qq,ss:rr['pages'][0]['viewports'].pop())
reject('viewport_clipped',lambda rr,aa,qq,ss:rr['pages'][0]['viewports'][0].__setitem__('clipped',['x']))
reject('viewport_overflow',lambda rr,aa,qq,ss:rr['pages'][0]['viewports'][0].__setitem__('documentWidth',321))
reject('shot_changed',lambda rr,aa,qq,ss:ss.__setitem__(next(iter(ss)),'0'*64))
reject('shot_missing',lambda rr,aa,qq,ss:ss.pop(next(iter(ss))))
reject('shot_status_error',lambda rr,aa,qq,ss:rr['pages'][0]['screenshots'][0].__setitem__('status','failed'))
reject('QA_same_basename_collision',lambda rr,aa,qq,ss:(qq.clear(),qq.update({'x/learning_review.mjs':'a','y/learning_review.mjs':'b'}),rr.__setitem__('qa_source_sha256',copy.deepcopy(qq))))
for bad in ['', '../qa/x', '/tmp/x', 'qa//x']:
 try:m.safe(bad)
 except AssertionError:fixtures.append({'name':'noncanonical_path_'+repr(bad),'expected':'reject','actual':'reject'})
 else:raise AssertionError(bad)
for bad in [False,True,1,None,'0']:
 try:zero({'actual_exit_code':bad})
 except AssertionError:fixtures.append({'name':'strict_actual_exit_'+repr(bad),'expected':'reject','actual':'reject'})
 else:raise AssertionError(bad)
# The actual main must guard prior completion and use exact new Root/PUB writes.
main=next(x for x in ast.parse(new).body if isinstance(x,ast.FunctionDef) and x.name=='main');assert sum(isinstance(x,ast.Call) and isinstance(x.func,ast.Attribute) and x.func.attr=='open' and x.args and isinstance(x.args[0],ast.Constant) and x.args[0].value=='xb' for x in ast.walk(main))==2
assert 'No new browser execution, screenshot or visual inspection is claimed' in new
first=json.loads(Path('/tmp/browser25-retention-native-independent-modules-actual-v1.json').read_text());assert first['actual_exit_code']==1;assert "page['qa_source_sha256'] == qa" in Path(first['raw_log']).read_text()
body={'status':'passed_independent_exact_retention25_helper_native24_contract_and_fixtures','errors':[],'checked_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(H),'helper_sha256':hashp(R/H),'original_unexecuted_helper':ref(OLD),'original_browser_report':ref(m.ORIGINAL),'manifest':ref('reports/full-coverage/checkpoint-25-manifest.json'),'actual_original_browser':ref(r['actual_execution']),'native_contract_passed':True,'exact_only_delta':'Per-page two basename QA hashes are bijectively normalized from the original top-level two canonical QA paths; all other helper bytes reverse exactly to v1.','fixture_count':len(fixtures),'fixtures':fixtures,'retained_viewports':145,'fresh_viewports':0,'screenshots':48,'skipped_targets':10,'original_first_reader_failure':{'file':'/tmp/browser25-retention-native-independent-modules-actual-v1.json','sha256':hashp(Path('/tmp/browser25-retention-native-independent-modules-actual-v1.json'))},'scope':'Read-only helper code/native prior evidence/fixtures. The producer main and browser were not executed. The native report whole body, prior times and manual visual inspection limitations remain unchanged; actual retention output is a separate required check.'}
OUT.write_text(json.dumps(body,indent=2)+'\n');print(json.dumps({'report':str(OUT),'sha256':hashp(OUT)}))

from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,struct
R=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/browser28-independent-modules28-reader-v1.json');START=datetime.now(timezone.utc).isoformat()
def h(n):return hashlib.sha256((R/n).read_bytes()).hexdigest()
def j(n):return json.loads((R/n).read_bytes())
def ref(n):return {'file':n,'sha256':h(n)}
def checked(r):assert h(r['file'])==r['sha256'];return j(r['file'])
merged_name='reports/full-coverage/browser-checkpoint-28.json';inputs_name='reports/full-coverage/browser-corrections-28-inputs.json';merge_native_name='reports/full-coverage/browser28-evidence-merge-execution-v1.json'
merged,inputs,merge_native=map(j,[merged_name,inputs_name,merge_native_name]);fresh=checked(inputs['fresh_original_report']);old=checked(inputs['retained_original_report']);native=checked(inputs['actual_execution']);outer=checked(inputs['actual_outer_helper_execution']);manual=checked(inputs['new_eight_capture_review']);checked(inputs['historical_original48_capture_review'])
changed={'lyapunov-mpc.html','verification.html','primer-probability.html','lipsdp.html'}
expected_command=['node','qa/learning_review.mjs','--report','reports/full-coverage/browser-source60-28-v1.json','--artifacts','reports/full-coverage/browser-artifacts-source60-28-v1','lyapunov-mpc.html','verification.html','primer-probability.html','lipsdp.html']
def actual_check(n,command):
 assert n['status']=='passed' and type(n['actual_exit_code']) is int and n['actual_exit_code']==0
 assert n['actual_command']==command and n['actual_workdir']==str(R) and h(n['log'])==n['log_sha256']
actual_check(native,expected_command);actual_check(outer,['python3','book/coverage/checks/root_browser_source60_run28_v1.py']);actual_check(merge_native,['python3','book/coverage/checks/root_prepare_browser28_v1.py'])
for n in [outer,merge_native]:
 assert n['helper_sha256_before']==n['helper_sha256_after']
 for f,s in n['helper_sha256_after'].items():assert h(f)==s
assert native['report_sha256']==inputs['fresh_original_report']['sha256'] and native['source_sha256_before']==native['source_sha256_after']==inputs['source_sha256']
assert inputs['entire_original_actual_body_and_time']==native and len(native['source_sha256_before'])==31
for n,s in native['source_sha256_before'].items():assert h(n)==s and h(native['site']+'/'+Path(n).name)==s
assert native['qa_source_sha256']==inputs['qa_source_sha256']==old['qa_source_sha256']
for n,s in native['qa_source_sha256'].items():assert h(n)==s
assert {n for n,s in native['source_sha256_before'].items() if old['source_sha256'][n]!=s}=={'SafeLearning/'+x for x in changed}
assert {p['file'] for p in fresh}==changed and len(fresh)==4
oldpages={p['file']:p for p in old['pages']};freshpages={p['file']:p for p in fresh};expectedpages=[freshpages[n] if n in changed else oldpages[n] for n in sorted(oldpages)];assert len(expectedpages)==29
def merged_check(m):
 assert m['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence' and m['coverage_complete'] is False
 assert (m['page_count'],m['requested_viewport_count'],m['verified_viewport_count'],m['fresh_verified_viewport_count'],m['retained_verified_viewport_count'],m['screenshot_count'],m['skipped_capture_target_count'])==(29,145,145,20,125,48,10)
 assert m['pages']==expectedpages and m['source_sha256']==native['source_sha256_before'] and m['qa_source_sha256']==native['qa_source_sha256']
 assert m['actual_execution']==inputs['actual_execution']['file'] and m['actual_execution_sha256']==inputs['actual_execution']['sha256'] and m['fresh_run_inputs']==inputs_name and m['fresh_run_inputs_sha256']==h(inputs_name)
 assert m['manual_visual_inspection']['horizontal_scroll_interaction_verified'] is False and m['manual_visual_inspection']['whole_page_visual_approval'] is False
merged_check(merged)
screens=[];freshscreens=[];skipped=0
for p in expectedpages:
 assert p['status']=='passed' and p['errors']==[] and p['source_sha256']==native['source_sha256_before']['SafeLearning/'+p['file']]
 assert {v['width'] for v in p['viewports']}=={320,390,768,820,1280} and all(not v['clipped'] and v['documentWidth']<=v['width'] for v in p['viewports'])
 mode='fresh_actual_source60_browser_execution' if p['file'] in changed else 'retained_exact_unchanged_source_and_QA_original27_record'
 assert inputs['pages'][p['file']]==merged['evidence_modes'][p['file']]=={'evidence_mode':mode,'original_report':inputs['fresh_original_report'] if p['file'] in changed else inputs['retained_original_report']}
 for s in p['screenshots']:
  if s['status']=='skipped':skipped+=1;continue
  assert s['status']=='passed' and s['source_sha256']==p['source_sha256'] and h(s['path'])==s['sha256']
  b=(R/s['path']).read_bytes();assert b[:8]==b'\x89PNG\r\n\x1a\n' and len(b)==s['bytes'] and struct.unpack('>I',b[16:20])[0]==round(s['dimensions']['width'])
  screens.append(s)
  if p['file'] in changed:freshscreens.append(s)
assert len(screens)==48 and len(freshscreens)==8 and skipped==10
assert len(inputs['screenshot_aliases'])==48 and len({a['file'] for a in inputs['screenshot_aliases']})==48
for a in inputs['screenshot_aliases']:assert h(a['original'])==h(a['file'])==a['sha256']
assert manual['status']=='completed_actual_eight_original_image_inspections_of_captured_regions' and manual['reviewer']=='Root' and manual['inspected_captures']==freshscreens
assert manual['horizontal_scroll_interaction_verified'] is False and manual['whole_page_visual_approval'] is False and manual['mobile_right_crop_count']==4
assert merged['manual_visual_inspection']['new_original_eight_review']==inputs['new_eight_capture_review'] and merged['manual_visual_inspection']['original_checkpoint27_review_closure']==inputs['historical_original48_capture_review']
fixtures=[]
def reject(name,base,mutate,validate):
 d=copy.deepcopy(base);mutate(d)
 try:validate(d)
 except (AssertionError,KeyError,TypeError,ValueError):fixtures.append({'case':name,'rejected':True});return
 raise AssertionError('Accepted '+name)
reject('bool browser exit',native,lambda d:d.update(actual_exit_code=False),lambda d:actual_check(d,expected_command))
reject('wrong browser command',native,lambda d:d.update(actual_command=['true']),lambda d:actual_check(d,expected_command))
reject('wrong browser cwd',native,lambda d:d.update(actual_workdir='/tmp'),lambda d:actual_check(d,expected_command))
reject('wrong browser raw log hash',native,lambda d:d.update(log_sha256='0'*64),lambda d:actual_check(d,expected_command))
reject('retained count incorrectly fresh',merged,lambda d:d.update(fresh_verified_viewport_count=145),merged_check)
reject('retained original page mutated',merged,lambda d:d['pages'][0].update(status='foreign'),merged_check)
reject('wrong current source hash',merged,lambda d:d['source_sha256'].update({'SafeLearning/lipsdp.html':'0'*64}),merged_check)
reject('scroll interaction inferred',merged,lambda d:d['manual_visual_inspection'].update(horizontal_scroll_interaction_verified=True),merged_check)
reject('whole page visual approval inferred',merged,lambda d:d['manual_visual_inspection'].update(whole_page_visual_approval=True),merged_check)
assert not OUT.exists()
d={'status':'passed_independent_browser28_native_result_and_exact_retained_evidence_review','errors':[],'reader_started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'merged_report':ref(merged_name),'inputs':ref(inputs_name),'actual_merge_execution':ref(merge_native_name),'actual_fresh_browser_execution':inputs['actual_execution'],'actual_browser_outer_execution':inputs['actual_outer_helper_execution'],'fresh_report':inputs['fresh_original_report'],'original_retained27_report':inputs['retained_original_report'],'actual_20_fresh_checks':True,'all125_entire_old_viewport_records_retained_exact':True,'all31_current_source_and_two_QA_bytes_exact':True,'all48_screenshot_original_and_alias_bytes_exact':True,'original_Root_eight_capture_review':inputs['new_eight_capture_review'],'original_Root_review_body_time_and_four_mobile_crop_limits_preserved':True,'additional_independent_visual_image_inspection_claimed':False,'horizontal_scroll_interaction_verified':False,'whole_page_visual_approval':False,'original_browser_command_result_and_times_preserved':True,'negative_fixtures':fixtures,'production_browser_rerun_or_artifact_or_owner_write':False,'coverage_complete':False,'scope':'Independent exact native/current-source/QA/report/merge/retained125/screenshot-byte audit. The original Root manual eight-region review is preserved as an original explicitly limited review; this reader adds no visual or mathematical correctness claim.'}
OUT.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'reader_sha256':hashlib.sha256(OUT.read_bytes()).hexdigest(),'negative_fixtures':len(fixtures),'fresh':20,'retained':125,'screenshots':48}))

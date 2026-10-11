"""Bind twenty fresh viewport checks to exact unchanged checkpoint27 evidence."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,shutil
ROOT=Path(__file__).resolve().parents[3]
REPORTS=ROOT/'reports/full-coverage'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_bytes())
def ref(n):return {'file':n,'sha256':sha(ROOT/n)}
fresh_name='reports/full-coverage/browser-source60-28-v1.json'
actual_name='reports/full-coverage/browser-source60-28-v1-execution.json'
old_name='reports/full-coverage/browser-checkpoint-27.json'
closure=ROOT/'reports/full-coverage/browser-corrections-27-inputs.json'
assert closure.is_file()
fresh,actual,old=read(fresh_name),read(actual_name),read(old_name)
assert type(actual['actual_exit_code']) is int and actual['actual_exit_code']==0
assert actual['status']=='passed' and actual['report_sha256']==sha(ROOT/fresh_name)
assert sha(ROOT/actual['log'])==actual['log_sha256']
assert actual['source_sha256_before']==actual['source_sha256_after']
sources=actual['source_sha256_before'];qa=actual['qa_source_sha256']
assert len(sources)==31 and all(sha(ROOT/n)==h for n,h in sources.items())
assert sha(ROOT/'book/coverage/inventory.json')=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
outer_name='reports/full-coverage/browser28-source60-helper-execution-v1.json';outer=read(outer_name)
assert type(outer['actual_exit_code']) is int and outer['actual_exit_code']==0 and outer['status']=='passed'
assert sha(ROOT/outer['log'])==outer['log_sha256']
assert outer['helper_sha256_before']==outer['helper_sha256_after']
assert all(sha(ROOT/n)==h for n,h in outer['helper_sha256_after'].items())
old_inputs=json.loads(closure.read_bytes())
assert sha(ROOT/old_inputs['new_four_capture_review']['file'])==old_inputs['new_four_capture_review']['sha256']
assert old['manual_visual_inspection']['status']=='all48_actual_captured_regions_inspected_with_explicit_scope_limits'
assert old['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence'
assert qa==old['qa_source_sha256'] and all(sha(ROOT/n)==h for n,h in qa.items())
changed={'lyapunov-mpc.html','verification.html','primer-probability.html','lipsdp.html'}
assert sources.keys()==old['source_sha256'].keys()
assert {n for n in sources if sources[n]!=old['source_sha256'][n]}=={'SafeLearning/'+n for n in changed}
assert {p['file'] for p in fresh}==changed
oldpages={p['file']:p for p in old['pages']};newpages={p['file']:p for p in fresh}
assert len(oldpages)==29
artifact=REPORTS/'browser-artifacts-28';output=REPORTS/'browser-checkpoint-28.json'
inputs=REPORTS/'browser-corrections-28-inputs.json';manual=REPORTS/'source60-eight-captured-regions-manual-review28-v1.json'
assert not any(p.exists() for p in [artifact,output,inputs,manual])
pages,modes,aliases,fresh_captures=[],{},[],[]
skipped=0
for name in sorted(oldpages):
 p=newpages[name] if name in changed else oldpages[name]
 assert p['status']=='passed' and p['errors']==[]
 assert {v['width'] for v in p['viewports']}=={320,390,768,820,1280}
 assert all(not v['clipped'] and v['documentWidth']<=v['width'] for v in p['viewports'])
 assert p['source_sha256']==sources['SafeLearning/'+name]
 assert p['qa_source_sha256']=={Path(n).name:h for n,h in qa.items()}
 pages.append(p)
 modes[name]={'evidence_mode':'fresh_actual_source60_browser_execution' if name in changed else 'retained_exact_unchanged_source_and_QA_original27_record','original_report':ref(fresh_name if name in changed else old_name)}
 for c in p['screenshots']:
  if c['status']=='skipped':skipped+=1;continue
  assert c['status']=='passed' and c['source_sha256']==p['source_sha256']
  assert sha(ROOT/c['path'])==c['sha256']
  aliases.append({'original':c['path'],'file':str((artifact/Path(c['path']).name).relative_to(ROOT)),'sha256':c['sha256'],'evidence_mode':modes[name]['evidence_mode']})
  if name in changed:fresh_captures.append(c)
assert len(aliases)==48 and len(fresh_captures)==8 and skipped==10
assert len({r['file'] for r in aliases})==48
artifact.mkdir()
for r in aliases:
 shutil.copyfile(ROOT/r['original'],ROOT/r['file']);assert sha(ROOT/r['file'])==r['sha256']
with manual.open('x') as f:
 f.write(json.dumps({'status':'completed_actual_eight_original_image_inspections_of_captured_regions','reviewer':'Root','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'inspected_captures':fresh_captures,'inspection_method':'view_image with original detail for each of the eight actual captures','observations':{'lyapunov-mpc.html':'All captured application prose and opened exercises are readable. The mobile geometric-sum formula is cropped on its right side in this static capture.','verification.html':'All captured application prose and opened exercises are readable. The mobile display of the ReLU formula is cropped on its right side in this static capture.','primer-probability.html':'The captured worked examples, warning and four opened exercise/hint/solution cards are readable. Several long mobile probability and Gaussian displays continue outside the initial right edge.','lipsdp.html':'The captured commissioning calculation and two opened exercise/hint/solution cards are readable, including the corrected scaling quotient. The initial mobile ReLU display continues outside the right edge.'},'mobile_right_crop_count':4,'horizontal_scroll_interaction_verified':False,'whole_page_visual_approval':False,'scope':'Only the four captured book-lab regions at390/1280 widths. Earlier corrected original paragraphs outside these regions and whole chapters were not visually inspected by these captures.'},ensure_ascii=False,indent=2)+'\n')
inputs.write_text(json.dumps({'actual_execution':ref(actual_name),'actual_outer_helper_execution':ref(outer_name),'entire_original_actual_body_and_time':actual,'fresh_original_report':ref(fresh_name),'retained_original_report':ref(old_name),'source_sha256':sources,'qa_source_sha256':qa,'pages':modes,'screenshot_aliases':aliases,'historical_original48_capture_review':ref(str(closure.relative_to(ROOT))),'new_eight_capture_review':ref(str(manual.relative_to(ROOT)))},indent=2)+'\n')
output.write_text(json.dumps({'status':'passed_actual_changed_pages_and_exact_unchanged_evidence','created_at_utc':datetime.now(timezone.utc).isoformat(),'page_count':29,'requested_viewport_count':145,'verified_viewport_count':145,'fresh_verified_viewport_count':20,'retained_verified_viewport_count':125,'source_sha256':sources,'qa_source_sha256':qa,'actual_execution':actual_name,'actual_execution_sha256':sha(ROOT/actual_name),'fresh_run_inputs':str(inputs.relative_to(ROOT)),'fresh_run_inputs_sha256':sha(inputs),'pages':pages,'evidence_modes':modes,'screenshot_count':48,'skipped_capture_target_count':10,'manual_visual_inspection':{'status':'all48_actual_captured_regions_inspected_with_explicit_scope_limits','fresh_actual_captures':8,'retained_exact_capture_count':40,'new_original_eight_review':ref(str(manual.relative_to(ROOT))),'original_checkpoint27_review_closure':ref(str(closure.relative_to(ROOT))),'horizontal_scroll_interaction_verified':False,'whole_page_visual_approval':False},'coverage_complete':False,'limits':['Twenty new actual viewport checks cover all four changed current60 pages. The other125 original checks retain their commands and times after exact source and QA matches.','Manual review covers captured application regions; some mobile formulas are cropped in those images. Horizontal scroll interaction and whole-page visual approval are not claimed.','Browser checks do not establish mathematical correctness.']},indent=2)+'\n')
print(json.dumps({'status':'passed','pages':29,'fresh_viewports':20,'retained_viewports':125,'screenshots':48,'fresh_images_inspected':8,'retained_images_inspected':40}))

"""Bind the actual Source53 run to exact unchanged checkpoint25 evidence."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / 'reports/full-coverage'
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(name): return json.loads((ROOT/name).read_text())
def reference(name): return {'file': name, 'sha256': sha(ROOT/name)}

fresh_name = 'reports/full-coverage/browser-source53-26-v1.json'
actual_name = 'reports/full-coverage/browser-source53-26-v1-execution.json'
old_name = 'reports/full-coverage/browser-checkpoint-25.json'
actual, old, fresh = read(actual_name), read(old_name), read(fresh_name)
assert type(actual['actual_exit_code']) is int and actual['actual_exit_code'] == 0
assert actual['status'] == 'passed' and actual['report_sha256'] == sha(ROOT/fresh_name)
assert sha(ROOT/actual['log']) == actual['log_sha256']
assert actual['source_sha256_before'] == actual['source_sha256_after']
sources = actual['source_sha256_before']
assert len(sources) == 31 and all(sha(ROOT/n) == h for n, h in sources.items())
assert old['status'] == 'passed_actual_exact_retained24_browser_evidence_for_unchanged25_assets'
assert old['fresh_verified_viewport_count'] == 0 and old['retained_verified_viewport_count'] == 145
assert actual['qa_source_sha256'] == old['qa_source_sha256']
qa = actual['qa_source_sha256']
assert len(qa) == 2 and all(sha(ROOT/n) == h for n, h in qa.items())
original24 = old['original_browser_report_body']
assert original24 == read(old['original_browser_report']['file'])
assert sha(ROOT/old['original_browser_report']['file']) == old['original_browser_report']['sha256']
assert original24['status'] == 'passed_actual_changed_pages_and_exact_unchanged_evidence'
assert original24['source_sha256'] == old['source_sha256']
assert original24['qa_source_sha256'] == qa
changed = {'lyapunov-mpc.html'}
assert sources.keys() == old['source_sha256'].keys()
assert {n for n in sources if sources[n] != old['source_sha256'][n]} == {'SafeLearning/'+n for n in changed}
assert {p['file'] for p in fresh} == changed
old_pages = {p['file']: p for p in original24['pages']}
fresh_pages = {p['file']: p for p in fresh}
assert set(old_pages) == {n.removeprefix('SafeLearning/') for n in sources if n.endswith('.html')}
assert len(old_pages) == 29
artifact_dir = REPORTS/'browser-artifacts-26'
output = REPORTS/'browser-checkpoint-26.json'
inputs = REPORTS/'browser-corrections-26-inputs.json'
assert not any(p.exists() for p in (artifact_dir, output, inputs))
pages, modes, screenshots, skipped = [], {}, [], 0
for name in sorted(old_pages):
    page = fresh_pages[name] if name in changed else old_pages[name]
    assert page['status'] == 'passed' and page['errors'] == []
    assert {v['width'] for v in page['viewports']} == {320,390,768,820,1280}
    assert all(not v['clipped'] and v['documentWidth'] <= v['width'] for v in page['viewports'])
    assert page['source_sha256'] == sources['SafeLearning/'+name]
    assert page['qa_source_sha256'] == {Path(n).name: h for n, h in qa.items()}
    pages.append(page)
    modes[name] = {'evidence_mode': 'fresh_actual_source53_browser_execution' if name in changed else 'retained_actual_original_record_after_exact_page_and_QA_hash_match',
                   'original_report': reference(fresh_name if name in changed else old_name)}
    for capture in page['screenshots']:
        if capture['status'] == 'skipped':
            skipped += 1
            continue
        assert capture['status'] == 'passed'
        assert capture['source_sha256'] == page['source_sha256']
        assert sha(ROOT/capture['path']) == capture['sha256']
        alias = str((artifact_dir/Path(capture['path']).name).relative_to(ROOT))
        screenshots.append({'original': capture['path'], 'file': alias, 'sha256': capture['sha256']})
assert len(screenshots) == 48 and skipped == 10
assert len({r['file'] for r in screenshots}) == len(screenshots)
manual_name = 'reports/full-coverage/source53-six-paragraph-content-manual-review26-v1.json'
assert sha(ROOT/manual_name) == '44e380bda0d0c0a6945c7980eca2d15da069b027280dd2144a48082d29620719'
manual = read(manual_name)
assert len(manual['inspected_captures']) == 6
assert len({c['path'] for c in manual['inspected_captures']}) == 6
assert manual['status'] == 'passed_actual_six_scoped_content_image_inspections'
assert manual['source_sha256'] == sources['SafeLearning/lyapunov-mpc.html']
for capture in manual['inspected_captures']:
    assert sha(ROOT/capture['path']) == capture['sha256']
artifact_dir.mkdir()
for row in screenshots:
    shutil.copyfile(ROOT/row['original'], ROOT/row['file'])
    assert sha(ROOT/row['file']) == row['sha256']
inputs.write_text(json.dumps({'actual_execution': reference(actual_name), 'original_actual_body': actual,
    'fresh_original_report': reference(fresh_name), 'retained_original_report': reference(old_name),
    'original_checkpoint25_body': old, 'source_sha256': sources, 'qa_source_sha256': qa,
    'pages': modes, 'screenshot_aliases': screenshots}, indent=2)+'\n')
output.write_text(json.dumps({'status': 'passed_actual_changed_pages_and_exact_unchanged_evidence',
    'created_at_utc': datetime.now(timezone.utc).isoformat(), 'page_count': 29,
    'requested_viewport_count': 145, 'verified_viewport_count': 145,
    'fresh_verified_viewport_count': 5, 'retained_verified_viewport_count': 140,
    'source_sha256': sources, 'qa_source_sha256': qa,
    'actual_execution': actual_name, 'actual_execution_sha256': sha(ROOT/actual_name),
    'fresh_run_inputs': str(inputs.relative_to(ROOT)), 'fresh_run_inputs_sha256': sha(inputs),
    'pages': pages, 'evidence_modes': modes, 'screenshot_count': 48,
    'skipped_capture_target_count': 10, 'manual_visual_inspection': {
        'status': 'whole_48_capture_manual_review_remains_pending',
        'original_checkpoint24_review_body': original24['manual_visual_inspection'],
        'scoped_changed_prose_review': reference(manual_name),
        'limits': 'Six desktop/mobile paragraph captures were inspected; this does not approve all 48 application screenshots.'},
    'coverage_complete': False,
    'limits': ['One changed Source53 page has five fresh actual viewport checks. Twenty-eight unchanged pages retain their original records and times after exact source and QA hash checks.',
               'Checkpoint25 retained browser evidence and added no fresh run.',
               'Browser checks do not establish mathematical correctness.']}, indent=2)+'\n')
print(json.dumps({'status': 'passed', 'pages': 29, 'fresh_viewports': 5, 'retained_viewports': 140, 'screenshots': 48, 'skipped': 10}))

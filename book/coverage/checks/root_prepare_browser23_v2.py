"""Bind fresh corrected pages and exact unchanged browser22 records without retiming."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / 'reports/full-coverage'
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def read(name):
    return json.loads((ROOT/name).read_text())
fresh_name = 'reports/full-coverage/browser-source51-23-v1.json'
actual_name = 'reports/full-coverage/browser-source51-23-v1-execution.json'
old_name = 'reports/full-coverage/browser-checkpoint-22.json'
actual, old, fresh = read(actual_name), read(old_name), read(fresh_name)
assert actual['actual_exit_code'] == 0 and actual['status'] == 'passed'
assert actual['report_sha256'] == sha(ROOT/fresh_name)
assert actual['source_sha256_before'] == actual['source_sha256_after']
source_hashes = actual['source_sha256_before']
assert all(sha(ROOT/name) == digest for name, digest in source_hashes.items())
assert old['status'] == 'passed_exact_retained_browser_evidence_no_new_execution'
assert actual['qa_source_sha256'] == old['qa_source_sha256']
assert all(sha(ROOT/name) == digest for name, digest in actual['qa_source_sha256'].items())
changed = {'cmdp.html','lyapunov-mpc.html'}
assert old['source_sha256'].keys() == source_hashes.keys()
assert {n for n in source_hashes if source_hashes[n] != old['source_sha256'][n]} == {'SafeLearning/'+n for n in changed}
assert {page['file'] for page in fresh} == changed
old_pages = {page['file']: page for page in old['pages']}
fresh_pages = {page['file']: page for page in fresh}
assert {name.removeprefix('SafeLearning/') for name in source_hashes if name.endswith('.html')} == set(old_pages)
artifact_dir = REPORTS/'browser-artifacts-23'
assert not artifact_dir.exists()
pages, modes, screenshots, skipped = [], {}, [], 0
for name in sorted(old_pages):
    page = fresh_pages[name] if name in changed else old_pages[name]
    assert page['status'] == 'passed' and not page['errors']
    assert {v['width'] for v in page['viewports']} == {320, 390, 768, 820, 1280}
    assert all(not v['clipped'] and v['documentWidth'] <= v['width'] for v in page['viewports'])
    assert page['source_sha256'] == source_hashes['SafeLearning/'+name]
    if name not in changed:
        assert old['source_sha256']['SafeLearning/'+name] == source_hashes['SafeLearning/'+name]
    modes[name] = dict(evidence_mode='fresh_source51_browser_execution' if name in changed else 'retained_actual_prior_execution_after_exact_page_and_QA_hash_match', original_report=fresh_name if name in changed else old_name, original_report_sha256=sha(ROOT/(fresh_name if name in changed else old_name)))
    pages.append(page)
    for capture in page['screenshots']:
        if capture['status'] == 'skipped':
            skipped += 1
            continue
        assert capture['status'] == 'passed'
        path = ROOT/capture['path']
        assert sha(path) == capture['sha256'] and capture['source_sha256'] == page['source_sha256']
        screenshots.append(dict(original=capture['path'], file=str((artifact_dir/path.name).relative_to(ROOT)), sha256=capture['sha256']))
assert len(pages) == 29 and len(screenshots) == 48 and skipped == 10
artifact_dir.mkdir()
for row in screenshots:
    shutil.copyfile(ROOT/row['original'], ROOT/row['file'])
    assert sha(ROOT/row['file']) == row['sha256']
for source, target in ((ROOT/fresh_name, REPORTS/'browser-corrections-23.json'), (ROOT/actual['log'], REPORTS/'browser-corrections-23.log')):
    assert not target.exists()
    shutil.copyfile(source, target)
inputs = REPORTS/'browser-corrections-23-inputs.json'
assert not inputs.exists()
inputs.write_text(json.dumps(dict(actual_execution=actual_name, actual_execution_sha256=sha(ROOT/actual_name), original_execution_metadata=actual, fresh_original_report=fresh_name, fresh_original_report_sha256=sha(ROOT/fresh_name), retained_original_report=old_name, retained_original_report_sha256=sha(ROOT/old_name), source_sha256=source_hashes, qa_source_sha256=actual['qa_source_sha256'], pages=modes, screenshot_aliases=screenshots), indent=2)+'\n')
output = REPORTS/'browser-checkpoint-23.json'
assert not output.exists()
output.write_text(json.dumps(dict(status='passed_actual_changed_pages_and_exact_unchanged_evidence', created_at_utc=datetime.now(timezone.utc).isoformat(), page_count=29, requested_viewport_count=145, verified_viewport_count=145, fresh_verified_viewport_count=10, retained_verified_viewport_count=135, source_sha256=source_hashes, qa_source_sha256=actual['qa_source_sha256'], actual_execution=actual_name, actual_execution_sha256=sha(ROOT/actual_name), fresh_run_inputs=str(inputs.relative_to(ROOT)), fresh_run_inputs_sha256=sha(inputs), pages=pages, evidence_modes=modes, screenshot_count=48, skipped_capture_target_count=10, manual_visual_inspection=dict(status='new_captures_pending_manual_visual_review', inherited_review='reports/full-coverage/browser-contact-sheet19-v2-top-regions.png', limits='The inherited top-region review remains historical; new captures have no manual visual pass.'), coverage_complete=False, limits=['Two corrected source51 pages have new actual browser checks. Twenty-seven unchanged pages retain their original actual source44/source47 records without new run times.', 'Browser checks do not establish mathematical correctness.']), indent=2)+'\n')
print(json.dumps(dict(status='passed', pages=29, fresh_viewports=10, retained_viewports=135, screenshots=48, skipped=10)))

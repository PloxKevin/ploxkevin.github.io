"""Retain genuine browser evidence after exact source/QA/artifact hash checks.

No browser execution or new visual inspection is claimed by this binding.
"""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, shutil

ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / 'reports/full-coverage'
OLD = 'reports/full-coverage/browser-checkpoint-21.json'
OUT = REPORTS / 'browser-checkpoint-22.json'
INPUTS = REPORTS / 'browser-corrections-22-inputs.json'
ARTIFACTS = REPORTS / 'browser-artifacts-22'

def sha(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()

def read(name):
    return json.loads((ROOT / name).read_text())

for path in (OUT, INPUTS, ARTIFACTS, REPORTS / 'browser-corrections-22.json', REPORTS / 'browser-corrections-22.log'):
    assert not path.exists(), path
old_bytes = (ROOT / OLD).read_bytes()
old = read(OLD)
assert old['status'] == 'passed_actual_changed_pages_and_exact_unchanged_evidence'
assert old['verified_viewport_count'] == 145 and len(old['pages']) == 29
assert len(old['source_sha256']) == 31 and len(old['qa_source_sha256']) == 2
for name, digest in old['source_sha256'].items():
    assert sha(name) == digest, name
for name, digest in old['qa_source_sha256'].items():
    assert sha(name) == digest, name
assert sha(old['actual_execution']) == old['actual_execution_sha256']
assert sha(old['fresh_run_inputs']) == old['fresh_run_inputs_sha256']
captures, skipped = [], 0
for page in old['pages']:
    assert page['status'] == 'passed' and not page['errors']
    assert page['source_sha256'] == old['source_sha256']['SafeLearning/' + page['file']]
    assert {v['width'] for v in page['viewports']} == {320, 390, 768, 820, 1280}
    assert all(not v['clipped'] and v['documentWidth'] <= v['width'] for v in page['viewports'])
    for capture in page['screenshots']:
        if capture['status'] == 'skipped':
            skipped += 1
            continue
        assert capture['status'] == 'passed'
        assert capture['source_sha256'] == page['source_sha256']
        assert sha(capture['path']) == capture['sha256']
        target = ARTIFACTS / Path(capture['path']).name
        captures.append(dict(original=capture['path'], file=str(target.relative_to(ROOT)), sha256=capture['sha256']))
assert len(captures) == 48 and skipped == 10
assert len({r['file'] for r in captures}) == len(captures)
ARTIFACTS.mkdir()
for row in captures:
    shutil.copyfile(ROOT / row['original'], ROOT / row['file'])
    assert sha(row['file']) == row['sha256']
originals = {}
for suffix in ('json', 'log'):
    source = 'reports/full-coverage/browser-corrections-21.' + suffix
    target = 'reports/full-coverage/browser-corrections-22.' + suffix
    shutil.copyfile(ROOT / source, ROOT / target)
    assert sha(source) == sha(target)
    originals[source] = sha(source)
bindings = dict(status='passed_exact_retention_no_new_browser_execution',
    checked_at_utc=datetime.now(timezone.utc).isoformat(), original_report=OLD, original_report_sha256=sha(OLD),
    source_sha256=old['source_sha256'], qa_source_sha256=old['qa_source_sha256'],
    original_actual_execution=old['actual_execution'], original_actual_execution_sha256=old['actual_execution_sha256'],
    original_actual_correction_files_sha256=originals, screenshot_aliases=captures,
    fresh_browser_executions=0, retained_verified_viewports=145,
    scope='Exact current31 source assets and both QA helpers match the genuine checkpoint21 browser evidence. Original page decisions, captures, skips and execution times remain unchanged.')
INPUTS.write_text(json.dumps(bindings, indent=2) + '\n')
result = copy.deepcopy(old)
result.update(status='passed_exact_retained_browser_evidence_no_new_execution',
    created_at_utc=datetime.now(timezone.utc).isoformat(), fresh_verified_viewport_count=0,
    retained_verified_viewport_count=145, fresh_run_inputs=str(INPUTS.relative_to(ROOT)),
    fresh_run_inputs_sha256=sha(str(INPUTS.relative_to(ROOT))),
    original_report=dict(file=OLD, sha256=sha(OLD)),
    evidence_modes={p['file']: dict(evidence_mode='retained_actual_prior_execution_after_exact_page_and_QA_hash_match',
        original_report=OLD, original_report_sha256=sha(OLD)) for p in old['pages']},
    limits=old['limits'] + ['Checkpoint22 retains all145 actual browser checks after exact source/QA/artifact matching. No new browser run or manual visual pass is claimed.'])
OUT.write_text(json.dumps(result, indent=2) + '\n')
assert (ROOT / OLD).read_bytes() == old_bytes
for name, digest in old['source_sha256'].items():
    assert sha(name) == digest, name
for name, digest in old['qa_source_sha256'].items():
    assert sha(name) == digest, name
print(json.dumps(dict(status='passed_exact_browser21_evidence_retained', fresh_browser_runs=0,
    retained_verified_viewports=145, screenshots=48, skipped=10,
    report=str(OUT.relative_to(ROOT)), report_sha256=sha(str(OUT.relative_to(ROOT))))))

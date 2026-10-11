"""Retain exact completed browser evidence after all source and QA hashes match.

This performs a read-only evidence check and writes new retention metadata.
It does not execute a browser or claim new screenshots or visual inspection.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / 'reports/book/publication-repo'
ORIGINAL = 'reports/full-coverage/browser-checkpoint-24.json'
ORIGINAL_SHA = '94749a4dfbab2dd12bdcdb213e9d42b8abdb3ff1a682729fa0978c0cd59f8625'
OUTPUT = 'reports/full-coverage/browser-checkpoint-25.json'

def safe(name):
    assert isinstance(name, str) and name and not Path(name).is_absolute()
    assert '..' not in Path(name).parts and str(Path(name)) == name
    p = ROOT / name
    assert p.resolve().is_relative_to(ROOT.resolve())
    return p

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(name): return json.loads(safe(name).read_text())

def validate(original, assets, qa, screenshot_hashes):
    assert original['status'] == 'passed_actual_changed_pages_and_exact_unchanged_evidence'
    assert original['coverage_complete'] is False
    assert len(assets) == 31 and original['source_sha256'] == assets
    assert original['qa_source_sha256'] == qa and len(qa) == 2
    assert original['page_count'] == len(original['pages']) == 29
    assert original['requested_viewport_count'] == original['verified_viewport_count'] == 145
    assert original['fresh_verified_viewport_count'] == 5
    assert original['retained_verified_viewport_count'] == 140
    page_qa = {Path(n).name: h for n, h in qa.items()}
    assert len(page_qa) == len(qa) == 2
    shots = []; skips = 0
    for page in original['pages']:
        assert page['status'] == 'passed' and page['errors'] == []
        assert page['qa_source_sha256'] == page_qa
        assert len(page['viewports']) == 5
        for viewport in page['viewports']:
            assert viewport['clipped'] == []
            assert viewport['documentWidth'] <= viewport['width']
        for shot in page['screenshots']:
            if shot['status'] == 'passed':
                assert screenshot_hashes[shot['path']] == shot['sha256']
                shots.append(shot['path'])
            else:
                assert shot['status'].startswith('skipped')
                skips += 1
    assert len(shots) == original['screenshot_count'] == 48
    assert skips == original['skipped_capture_target_count'] == 10
    return len(shots), skips

def main():
    assert not safe(OUTPUT).exists() and not (PUB / OUTPUT).exists()
    assert sha(safe(ORIGINAL)) == ORIGINAL_SHA
    original = read(ORIGINAL)
    manifest_name = 'reports/full-coverage/checkpoint-25-manifest.json'
    manifest = read(manifest_name)
    assert manifest['status'] == 'formal_verification_passed_partial_coverage'
    assets = {n: h for n, h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
    qa = {n: sha(safe(n)) for n in original['qa_source_sha256']}
    for n, h in assets.items(): assert sha(safe(n)) == sha(PUB / n) == h
    for n, h in qa.items(): assert sha(safe(n)) == sha(PUB / n) == h
    screenshots = {shot['path']: sha(safe(shot['path']))
                   for page in original['pages'] for shot in page['screenshots']
                   if shot['status'] == 'passed'}
    shots, skips = validate(original, assets, qa, screenshots)
    actual = read(original['actual_execution'])
    assert sha(safe(original['actual_execution'])) == original['actual_execution_sha256']
    codes = [actual[k] for k in ('actual_exit_code', 'exit_code') if k in actual]
    assert codes and all(type(c) is int and c == 0 for c in codes)
    logs = [actual[k] for k in ('log', 'raw_log') if k in actual]
    hashes = [actual[k] for k in ('log_sha256', 'raw_log_sha256') if k in actual]
    assert logs and hashes and all(x == logs[0] for x in logs) and all(x == hashes[0] for x in hashes)
    assert sha(safe(logs[0])) == hashes[0]
    assert sha(safe(original['fresh_run_inputs'])) == original['fresh_run_inputs_sha256']
    result = dict(status='passed_actual_exact_retained24_browser_evidence_for_unchanged25_assets',
        checked_at_utc=datetime.now(timezone.utc).isoformat(),
        page_count=29, requested_viewport_count=145, verified_viewport_count=145,
        fresh_verified_viewport_count=0, retained_verified_viewport_count=145,
        screenshot_count=shots, skipped_capture_target_count=skips,
        source_sha256=assets, qa_source_sha256=qa,
        original_browser_report={'file': ORIGINAL, 'sha256': ORIGINAL_SHA},
        original_browser_report_body=original,
        screenshot_files_sha256=screenshots,
        manifest={'file': manifest_name, 'sha256': sha(safe(manifest_name))},
        coverage_complete=False,
        scope='All 145 completed browser viewport checks are retained from checkpoint24 after exact current31 source and QA matching. No new browser execution, screenshot or visual inspection is claimed. Original execution fields, times, evidence modes and manual visual limitations remain unchanged in the embedded original body.')
    payload = (json.dumps(result, indent=2) + '\n').encode()
    # Repeat the source/report guards before either new metadata file is created.
    assert sha(safe(ORIGINAL)) == ORIGINAL_SHA
    for n, h in assets.items(): assert sha(safe(n)) == sha(PUB / n) == h
    for n, h in qa.items(): assert sha(safe(n)) == sha(PUB / n) == h
    for n, h in screenshots.items(): assert sha(safe(n)) == h
    safe(OUTPUT).parent.mkdir(parents=True, exist_ok=True)
    with safe(OUTPUT).open('xb') as out: out.write(payload)
    (PUB / OUTPUT).parent.mkdir(parents=True, exist_ok=True)
    with (PUB / OUTPUT).open('xb') as out: out.write(payload)
    assert sha(safe(OUTPUT)) == sha(PUB / OUTPUT)
    print(json.dumps({'status': 'passed', 'retained_viewports': 145, 'fresh_viewports': 0,
                      'output': OUTPUT, 'sha256': sha(safe(OUTPUT))}))

if __name__ == '__main__': main()

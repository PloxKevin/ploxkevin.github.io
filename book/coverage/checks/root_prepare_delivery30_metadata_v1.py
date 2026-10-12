"""Record actual content delivery and prepare its exact metadata publication."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, subprocess

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / 'reports/book/publication-repo'
CONTENT = 'ae9e78658094db31d456b9dec509cc7a92b7f386'
OUT = ROOT / 'reports/full-coverage/publication30-delivery-metadata-preparation-v1.json'
HISTORY = ROOT / 'reports/full-coverage/source-history/checkpoint30-before-content-delivery-metadata-v1'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def ref(n):
    return {'file': n, 'sha256': sha(ROOT / n)}


def read(n):
    return json.loads((ROOT / n).read_bytes())


def git(args):
    return subprocess.run(['git', *args], cwd=PUB, capture_output=True, check=True).stdout


assert not OUT.exists() and not HISTORY.exists()
assert git(['rev-parse', 'HEAD']).decode().strip() == CONTENT
assert not git(['status', '--porcelain', '-z', '--untracked-files=all'])
live = read('reports/full-coverage/live-checkpoint-30-attempt2.json')
pages = read('reports/full-coverage/pages-checkpoint-30-attempt2.json')
jobs = json.loads((ROOT / 'reports/full-coverage/pages30-content-jobs-observation-execution-v1.log').read_bytes())
assert live['status'] == 'passed_all31_asset_sha256' and live['commit'] == live['remote_main'] == CONTENT
assert len(live['assets']) == 31 and all(r['matches'] and r['http_status'] == 200 for r in live['assets'])
assert pages['status'] == 'passed' and pages['exit_code'] == 0 and pages['commit'] == CONTENT
assert len(jobs['jobs']) == 3 and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs['jobs'])
assert all(j['head_sha'] == CONTENT for j in jobs['jobs'])
native = read('reports/full-coverage/live30-content-confirmation-execution-v2.json')
assert native['status'] == 'passed' and native['actual_exit_code'] == 0
HISTORY.mkdir(parents=True)
originals = {}
for n in ['book/coverage/progress.json', 'reports/full-coverage/README.md']:
    target = HISTORY / n; target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / n, target); assert sha(target) == sha(ROOT / n)
    originals[n] = {'file': target.relative_to(ROOT).as_posix(), 'sha256': sha(target)}
progress = read('book/coverage/progress.json')
progress['last_published_commit'] = CONTENT
progress['last_published_content_commit'] = CONTENT
progress['publication_status'] = 'checkpoint_30_content_published_and_all31_live_verified'
progress['live_delivery_status'] = 'passed_all31_asset_hashes_and_successful_content_Pages_workflow'
progress['live_delivery_evidence'] = {
    'content_commit': CONTENT, 'content_live_check': ref('reports/full-coverage/live-checkpoint-30-attempt2.json'),
    'content_pages_check': ref('reports/full-coverage/pages-checkpoint-30-attempt2.json'),
    'actual_live_execution': ref('reports/full-coverage/live30-content-confirmation-execution-v2.json'),
    'actual_three_successful_jobs': ref('reports/full-coverage/pages30-content-jobs-observation-execution-v1.log'),
    'actual_content_push': ref('reports/full-coverage/publication30-content-push-v1.json'),
    'metadata_push_and_metadata_live_check_pending': True}
progress['working_next_checkpoint_preparation']['status'] = 'checkpoint30_published_original_full_coverage_work_continues'
(ROOT / 'book/coverage/progress.json').write_text(json.dumps(progress, indent=2) + '\n')
p = ROOT / 'reports/full-coverage/README.md'; text = p.read_text()
old = '''Checkpoint 30 is verified locally and prepared for GitHub publication;
delivery is still pending. Checkpoint 29's successful content and metadata
delivery, including the [fresh all-31-asset check](live-checkpoint-29-attempt1.json),
remains preserved. Full mathematical coverage work continues.'''
new = '''Checkpoint 30 is published at content commit `ae9e7865`. Its GitHub Pages
workflow completed successfully, and the [fresh live check](live-checkpoint-30-attempt2.json)
verified all 31 asset hashes. The [actual push](publication30-content-push-v1.json)
and [actual check](live30-content-confirmation-execution-v2.json) preserve their
commands, outputs and times. The first live attempt ran while Pages was still
building and remains recorded as unsuccessful. Checkpoint 29's successful
content and metadata delivery is retained. Full mathematical coverage work
continues; delivery does not establish completion of the remaining material.'''
assert text.count(old) == 1
p.write_text(text.replace(old, new))
files = {n for n in ['book/coverage/progress.json', 'reports/full-coverage/README.md',
    'book/coverage/checks/root_prepare_delivery30_metadata_v1.py',
    'reports/full-coverage/publication30-content-commit-v1.json',
    'reports/full-coverage/publication30-content-commit-v1.log',
    'reports/full-coverage/publication30-content-push-v1.json',
    'reports/full-coverage/publication30-content-push-v1.log',
    'reports/full-coverage/commit-publication30-execution-v1.json',
    'reports/full-coverage/commit-publication30-execution-v1.log',
    'reports/full-coverage/push-publication30-execution-v1.json',
    'reports/full-coverage/push-publication30-execution-v1.log',
    'reports/full-coverage/live-checkpoint-30-attempt1.json',
    'reports/full-coverage/live-checkpoint-30-attempt2.json',
    'reports/full-coverage/pages-checkpoint-30-attempt1.json',
    'reports/full-coverage/pages-checkpoint-30-attempt1.log',
    'reports/full-coverage/pages-checkpoint-30-attempt2.json',
    'reports/full-coverage/pages-checkpoint-30-attempt2.log',
    'reports/full-coverage/live30-content-confirmation-execution-v1.json',
    'reports/full-coverage/live30-content-confirmation-execution-v1.log',
    'reports/full-coverage/live30-content-confirmation-execution-v2.json',
    'reports/full-coverage/live30-content-confirmation-execution-v2.log',
    'reports/full-coverage/pages30-actions-observation-execution-v1.json',
    'reports/full-coverage/pages30-actions-observation-execution-v1.log',
    'reports/full-coverage/pages30-content-jobs-observation-execution-v1.json',
    'reports/full-coverage/pages30-content-jobs-observation-execution-v1.log',
    'book/coverage/checks/root_prepare_tmp_owner30_context_v1.py',
    'reports/full-coverage/source79-owner30-finalcss-context-preparation-execution-v1.json',
    'reports/full-coverage/source79-owner30-finalcss-context-preparation-execution-v1.log']}
for directory in [HISTORY.relative_to(ROOT).as_posix(),
    'book/coverage/checks/future30-core/stager30-source-only1-independent-modules-v1',
    'book/coverage/checks/future30-core/stager30-source-only2-independent-modules-v1',
    'book/coverage/checks/future30-core/tmp-owner30-context1-independent-modules-v1']:
    files.update(p.relative_to(ROOT).as_posix() for p in (ROOT / directory).rglob('*') if p.is_file())
expected = {n: sha(ROOT / n) for n in sorted(files)}
for n in expected:
    assert not Path(n).is_absolute() and '..' not in Path(n).parts and '.git' not in Path(n).parts and '.lake' not in Path(n).parts
    assert (ROOT / n).is_file() and not (ROOT / n).is_symlink()
    target = PUB / n; assert target.resolve().is_relative_to(PUB) and not target.is_symlink()
    target.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(ROOT / n, target)
    assert sha(target) == expected[n]
record = {'status': 'actual_checkpoint30_content_delivery_recorded_metadata_commit_and_push_pending',
          'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'content_commit': CONTENT,
          'exact_metadata_paths_sha256': expected, 'original_progress_and_document_preserved': originals,
          'actual_content_live_check': ref('reports/full-coverage/live-checkpoint-30-attempt2.json'),
          'coverage_complete': False, 'metadata_commit_push_or_live_success_claimed': False}
OUT.write_text(json.dumps(record, indent=2) + '\n')
shutil.copyfile(OUT, PUB / OUT.relative_to(ROOT))
print(json.dumps({'status': record['status'], 'metadata_files': len(expected) + 1, 'content_commit': CONTENT, 'coverage_complete': False}))

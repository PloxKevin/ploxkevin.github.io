"""Record actual content delivery and prepare its exact metadata publication."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, re, shutil, subprocess

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / 'reports/book/publication-repo'
CONTENT = json.loads((ROOT / 'reports/full-coverage/publication31-content-commit-v1.json').read_bytes())['commit']
OUT = ROOT / 'reports/full-coverage/publication31-delivery-metadata-preparation-v1.json'
HISTORY = ROOT / 'reports/full-coverage/source-history/checkpoint31-before-content-delivery-metadata-v1'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def ref(n):
    return {'file': n, 'sha256': sha(ROOT / n)}


def read(n):
    return json.loads((ROOT / n).read_bytes())


def git(args):
    return subprocess.run(['git', *args], cwd=PUB, capture_output=True, check=True).stdout


ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--live-attempt', type=int, required=True)
ap.add_argument('--code-peer', action='append', default=[])
args = ap.parse_args()
assert args.live_attempt > 0
live_name = f'reports/full-coverage/live-checkpoint-31-attempt{args.live_attempt}.json'
pages_name = f'reports/full-coverage/pages-checkpoint-31-attempt{args.live_attempt}.json'
assert not OUT.exists() and not HISTORY.exists()
assert git(['rev-parse', 'HEAD']).decode().strip() == CONTENT
assert not git(['status', '--porcelain', '-z', '--untracked-files=all'])
live = read(live_name)
pages = read(pages_name)
jobs = json.loads((ROOT / 'reports/full-coverage/pages31-content-jobs-observation-execution-v1.log').read_bytes())
assert live['status'] == 'passed_all31_asset_sha256' and live['commit'] == live['remote_main'] == CONTENT
assert len(live['assets']) == 31 and all(r['matches'] and r['http_status'] == 200 for r in live['assets'])
assert pages['status'] == 'passed' and pages['exit_code'] == 0 and pages['commit'] == CONTENT
assert len(jobs['jobs']) == 3 and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs['jobs'])
assert all(j['head_sha'] == CONTENT for j in jobs['jobs'])
native = read('reports/full-coverage/live31-content-confirmation-execution-v1.json')
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
    'content_commit': CONTENT, 'content_live_check': ref(live_name),
    'content_pages_check': ref(pages_name),
    'actual_live_execution': ref('reports/full-coverage/live31-content-confirmation-execution-v1.json'),
    'actual_three_successful_jobs': ref('reports/full-coverage/pages31-content-jobs-observation-execution-v1.log'),
    'actual_content_push': ref('reports/full-coverage/publication31-content-push-v1.json'),
    'metadata_push_and_metadata_live_check_pending': True}
progress['working_next_checkpoint_preparation']['status'] = 'checkpoint31_published_original_full_coverage_work_continues'
(ROOT / 'book/coverage/progress.json').write_text(json.dumps(progress, indent=2) + '\n')
p = ROOT / 'reports/full-coverage/README.md'; text = p.read_text()
old = 'Checkpoint 31 is verified locally; its GitHub delivery is pending.'
new = (f'Checkpoint 31 is published at content commit `{CONTENT[:8]}`. Its Pages jobs\n'
       f'completed successfully, and the [fresh live check]({Path(live_name).name})\n'
       'verified all 31 asset hashes. The [actual push](publication31-content-push-v1.json)\n'
       'preserves its command, output and time. The delivery metadata commit is pending;\n'
       'full mathematical coverage remains unfinished.')
assert text.count(old) == 1
p.write_text(text.replace(old, new))
files = set(['book/coverage/progress.json', 'reports/full-coverage/README.md',
    'book/coverage/checks/root_prepare_delivery31_metadata_v1.py',
    'reports/full-coverage/publication31-content-commit-v1.json', 'reports/full-coverage/publication31-content-commit-v1.log',
    'reports/full-coverage/publication31-content-push-v1.json', 'reports/full-coverage/publication31-content-push-v1.log',
    'reports/full-coverage/commit-publication31-execution-v1.json', 'reports/full-coverage/commit-publication31-execution-v1.log',
    'reports/full-coverage/push-publication31-execution-v1.json', 'reports/full-coverage/push-publication31-execution-v1.log',
    live_name, pages_name, str(Path(pages_name).with_suffix('.log')),
    'reports/full-coverage/live31-content-confirmation-execution-v1.json', 'reports/full-coverage/live31-content-confirmation-execution-v1.log',
    'reports/full-coverage/pages31-actions-observation-execution-v1.json', 'reports/full-coverage/pages31-actions-observation-execution-v1.log',
    'reports/full-coverage/pages31-content-jobs-observation-execution-v1.json', 'reports/full-coverage/pages31-content-jobs-observation-execution-v1.log'])
for directory in [HISTORY.relative_to(ROOT).as_posix(), *[Path(n).parent.as_posix() for n in args.code_peer]]:
    for p in (ROOT / directory).rglob('*'):
        if p.is_file(): files.add(p.relative_to(ROOT).as_posix())
for n in args.code_peer:
    peer = read(n)
    assert peer['status'].startswith('passed') and peer.get('errors', []) == []
for n in files:
    assert not any(part in {'.git','.lake','__pycache__','..'} or re.fullmatch(r'checkpoint-\d+',part) for part in Path(n).parts[:-1])
expected = {n: sha(ROOT / n) for n in sorted(files)}
for n in expected:
    assert not Path(n).is_absolute() and '..' not in Path(n).parts and '.git' not in Path(n).parts and '.lake' not in Path(n).parts
    assert (ROOT / n).is_file() and not (ROOT / n).is_symlink()
    target = PUB / n; assert target.resolve().is_relative_to(PUB) and not target.is_symlink()
    target.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(ROOT / n, target)
    assert sha(target) == expected[n]
record = {'status': 'actual_checkpoint31_content_delivery_recorded_metadata_commit_and_push_pending',
          'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'content_commit': CONTENT,
          'exact_metadata_paths_sha256': expected, 'original_progress_and_document_preserved': originals,
          'actual_content_live_check': ref(live_name),
          'coverage_complete': False, 'metadata_commit_push_or_live_success_claimed': False}
OUT.write_text(json.dumps(record, indent=2) + '\n')
shutil.copyfile(OUT, PUB / OUT.relative_to(ROOT))
print(json.dumps({'status': record['status'], 'metadata_files': len(expected) + 1, 'content_commit': CONTENT, 'coverage_complete': False}))

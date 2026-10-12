"""Stage exact real delivery metadata, commit it, or push its recorded commit."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, shutil, subprocess, time

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / 'reports/book/publication-repo'
CONTENT = json.loads((ROOT / 'reports/full-coverage/publication31-content-commit-v1.json').read_bytes())['commit']
COMMIT = 'reports/full-coverage/publication31-metadata-commit-v1.json'
PUSH = 'reports/full-coverage/publication31-metadata-push-v1.json'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def git(args, data=None):
    return subprocess.run(['git', *args], cwd=PUB, input=data, capture_output=True, check=True).stdout


def read(n):
    return json.loads((ROOT / n).read_bytes())


def execute(command, record_name):
    path = ROOT / record_name; log = path.with_suffix('.log')
    assert not path.exists() and not log.exists()
    started = datetime.now(timezone.utc).isoformat(); tick = time.monotonic()
    with log.open('xb') as out:
        result = subprocess.run(command, cwd=PUB, stdout=out, stderr=subprocess.STDOUT)
    record = {'status': 'passed' if result.returncode == 0 else 'failed', 'actual_exit_code': result.returncode,
              'actual_command': command, 'actual_workdir': str(PUB), 'started_at_utc': started,
              'finished_at_utc': datetime.now(timezone.utc).isoformat(), 'elapsed_seconds': time.monotonic() - tick,
              'raw_log': log.relative_to(ROOT).as_posix(), 'raw_log_sha256': sha(log),
              'content_commit': CONTENT, 'coverage_complete': False}
    return path, record


ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('mode', choices=['commit', 'push'])
args = ap.parse_args()
if args.mode == 'commit':
    assert git(['rev-parse', 'HEAD']).decode().strip() == CONTENT
    assert not git(['diff', '--cached', '--name-only', '-z'])
    preparation_name = 'reports/full-coverage/publication31-delivery-metadata-preparation-v1.json'
    preparation = read(preparation_name)
    assert preparation['status'] == 'actual_checkpoint31_content_delivery_recorded_metadata_commit_and_push_pending'
    expected = dict(preparation['exact_metadata_paths_sha256'])
    extras = [preparation_name, 'reports/full-coverage/prepare-delivery31-metadata-execution-v1.json',
              'reports/full-coverage/prepare-delivery31-metadata-execution-v1.log',
              'book/coverage/checks/root_commit_push_delivery31_metadata_v1.py']
    for n in extras:
        target = PUB / n; target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / n, target); expected[n] = sha(ROOT / n)
    assert all(sha(PUB / n) == sha(ROOT / n) == h for n, h in expected.items())
    for row in git(['status', '--porcelain', '-z', '--untracked-files=all']).decode().split('\0'):
        if row:
            assert row[:2] in {' M', '??'} and row[3:] in expected, row
    native = read('reports/full-coverage/prepare-delivery31-metadata-execution-v1.json')
    assert native['status'] == 'passed' and native['actual_exit_code'] == 0
    git(['--literal-pathspecs', 'add', '-f', '--pathspec-from-file=-', '--pathspec-file-nul'],
        b'\0'.join(n.encode() for n in sorted(expected)) + b'\0')
    names = {n.decode() for n in git(['diff', '--cached', '--name-only', '-z']).split(b'\0') if n}
    assert names and names <= set(expected) and not git(['diff', '--name-only', '-z'])
    for n in names:
        assert hashlib.sha256(git(['show', ':' + n])).hexdigest() == expected[n]
    path, record = execute(['git', 'commit', '--quiet', '-m', 'Record checkpoint 31 successful Pages and all 31 live asset checks'], COMMIT)
    record['actual_committed_paths_sha256'] = {n: expected[n] for n in names}
    if record['actual_exit_code'] == 0:
        record['commit'] = git(['rev-parse', 'HEAD']).decode().strip()
        assert git(['rev-parse', 'HEAD^']).decode().strip() == CONTENT
        assert not git(['status', '--porcelain', '-z', '--untracked-files=all'])
    with path.open('x') as out:
        out.write(json.dumps(record, indent=2) + '\n')
else:
    commit = read(COMMIT)
    assert commit['status'] == 'passed' and commit['actual_exit_code'] == 0
    assert git(['rev-parse', 'HEAD']).decode().strip() == commit['commit']
    assert not git(['status', '--porcelain', '-z', '--untracked-files=all'])
    assert git(['ls-remote', 'origin', 'refs/heads/main']).decode().split()[0] == CONTENT
    path, record = execute(['git', 'push', 'origin', 'main'], PUSH)
    record['commit'] = commit['commit']
    if record['actual_exit_code'] == 0:
        record['remote_main_after'] = git(['ls-remote', 'origin', 'refs/heads/main']).decode().split()[0]
        assert record['remote_main_after'] == commit['commit']
    record['metadata_Pages_or_metadata_live_success_claimed'] = False
    with path.open('x') as out:
        out.write(json.dumps(record, indent=2) + '\n')
print(json.dumps({'status': record['status'], 'actual_exit_code': record['actual_exit_code'],
                  'commit': record.get('commit'), 'coverage_complete': False}))
raise SystemExit(record['actual_exit_code'])

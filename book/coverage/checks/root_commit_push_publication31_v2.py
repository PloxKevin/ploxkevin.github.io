"""Commit the exact staged checkpoint31 list, or push that recorded commit."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, shutil, subprocess, time

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / 'reports/book/publication-repo'
BASELINE = '676db1f7d13ddbf65c2f0253d1fab79c44948a7e'
STAGED = 'reports/full-coverage/publication31-staged-byte-check-v1.json'
COMMIT_RECORD = 'reports/full-coverage/publication31-content-commit-v1.json'
PUSH_RECORD = 'reports/full-coverage/publication31-content-push-v1.json'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def git(args):
    return subprocess.run(['git', *args], cwd=PUB, capture_output=True, check=True).stdout


def read(n):
    return json.loads((ROOT / n).read_bytes())


def execute(command, record_name):
    record_path = ROOT / record_name; log = record_path.with_suffix('.log')
    assert not record_path.exists() and not log.exists()
    start = datetime.now(timezone.utc).isoformat(); tick = time.monotonic()
    with log.open('xb') as out:
        run = subprocess.run(command, cwd=PUB, stdout=out, stderr=subprocess.STDOUT)
    record = {'status': 'passed' if run.returncode == 0 else 'failed', 'actual_exit_code': run.returncode,
              'actual_command': command, 'actual_workdir': str(PUB), 'started_at_utc': start,
              'finished_at_utc': datetime.now(timezone.utc).isoformat(), 'elapsed_seconds': time.monotonic() - tick,
              'raw_log': log.relative_to(ROOT).as_posix(), 'raw_log_sha256': sha(log),
              'helper_sha256': sha(Path(__file__)), 'coverage_complete': False}
    command_path = record_path.with_name(record_path.stem + '-command.json')
    with command_path.open('x') as out:
        out.write(json.dumps(record, indent=2) + '\n')
    record['actual_command_receipt'] = {'file': command_path.relative_to(ROOT).as_posix(), 'sha256': sha(command_path)}
    return record_path, record


ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('mode', choices=['commit', 'push'])
args = ap.parse_args()
try:
    if args.mode == 'commit':
        assert git(['symbolic-ref', '--short', 'HEAD']).decode().strip() == 'main'
        assert git(['rev-parse', 'HEAD']).decode().strip() == BASELINE
        staged = read(STAGED)
        assert staged['status'] == 'passed_actual_checkpoint31_staged_blob_sha256_and_partial_ledger_check'
        expected = dict(staged['actual_staged_paths_sha256'])
        expected[STAGED] = sha(ROOT / STAGED)
        assert all(sha(PUB / n) == h for n, h in expected.items())
        for n in ['reports/full-coverage/stage-publication31-execution-v1.json',
                  'reports/full-coverage/stage-publication31-execution-v1.log',
                  'book/coverage/checks/root_commit_push_publication31_v2.py']:
            target = PUB / n; target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / n, target)
            assert sha(target) == sha(ROOT / n)
            expected[n] = sha(target)
        data = b'\0'.join(n.encode() for n in sorted(expected)) + b'\0'
        subprocess.run(['git', '--literal-pathspecs', 'add', '-f', '--pathspec-from-file=-', '--pathspec-file-nul'],
                       cwd=PUB, input=data, capture_output=True, check=True)
        names = {n.decode() for n in git(['diff', '--cached', '--name-only', '-z']).split(b'\0') if n}
        assert names == set(expected) and not git(['diff', '--name-only', '-z'])
        native = read('reports/full-coverage/stage-publication31-execution-v1.json')
        assert native['status'] == 'passed' and native['actual_exit_code'] == 0
        command = ['git', 'commit', '--quiet', '-m', 'Verify checkpoint 31 source corrections and six additional Lean proof files']
        path, record = execute(command, COMMIT_RECORD)
        record['baseline_publication_head'] = BASELINE
        record['staged_check'] = {'file': STAGED, 'sha256': sha(ROOT / STAGED)}
        record['actual_committed_paths_sha256'] = expected
        if record['actual_exit_code'] == 0:
            record['commit'] = git(['rev-parse', 'HEAD']).decode().strip()
            assert git(['rev-parse', 'HEAD^']).decode().strip() == BASELINE
            assert not git(['status', '--porcelain', '-z', '--untracked-files=all'])
        with path.open('x') as out:
            out.write(json.dumps(record, indent=2) + '\n')
        print(json.dumps({'status': record['status'], 'actual_exit_code': record['actual_exit_code'], 'commit': record.get('commit'), 'coverage_complete': False}))
        raise SystemExit(record['actual_exit_code'])
    else:
        commit = read(COMMIT_RECORD)
        assert commit['status'] == 'passed' and commit['actual_exit_code'] == 0
        assert git(['rev-parse', 'HEAD']).decode().strip() == commit['commit']
        assert git(['rev-parse', 'refs/heads/main']).decode().strip() == commit['commit']
        assert git(['symbolic-ref', '--short', 'HEAD']).decode().strip() == 'main'
        assert not git(['status', '--porcelain', '-z', '--untracked-files=all'])
        remote_before = git(['ls-remote', 'origin', 'refs/heads/main']).decode().split()[0]
        assert remote_before == BASELINE
        path, record = execute(['git', 'push', 'origin', 'main'], PUSH_RECORD)
        record['commit'] = commit['commit']; record['remote_main_before'] = remote_before
        if record['actual_exit_code'] == 0:
            record['remote_main_after'] = git(['ls-remote', 'origin', 'refs/heads/main']).decode().split()[0]
            assert record['remote_main_after'] == commit['commit']
        record['Pages_or_live_success_claimed'] = False
        with path.open('x') as out:
            out.write(json.dumps(record, indent=2) + '\n')
        print(json.dumps({'status': record['status'], 'actual_exit_code': record['actual_exit_code'], 'commit': record['commit'], 'remote_main_after': record.get('remote_main_after'), 'coverage_complete': False}))
        raise SystemExit(record['actual_exit_code'])
except Exception as error:
    if 'record' in globals() and 'path' in globals() and not path.exists():
        record['status'] = 'failed_post_command_association'
        record['association_error'] = type(error).__name__ + ': ' + str(error)
        record['scope'] = 'The immutable command receipt retains the true subprocess exit code and time; the later association failed.'
        with path.open('x') as out:
            out.write(json.dumps(record, indent=2) + '\n')
    raise

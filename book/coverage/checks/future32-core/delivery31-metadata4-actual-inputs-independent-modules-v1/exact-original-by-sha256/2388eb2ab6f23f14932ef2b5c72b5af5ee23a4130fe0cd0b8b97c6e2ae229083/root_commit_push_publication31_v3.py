"""Commit the exact staged checkpoint31 list, or push that recorded commit."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, shutil, subprocess, tempfile, time

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


def verify_committed_tree(expected, before, after):
    changed = {n.decode() for n in git(['diff-tree', '--no-commit-id', '--name-only', '-r', '-z', '--no-renames', before, after]).split(b'\0') if n}
    assert changed == set(expected), 'Committed path delta differs from exact staged names'
    objects = {}
    for row in git(['ls-tree', '-r', '-z', after]).split(b'\0'):
        if not row: continue
        header, name = row.split(b'\t', 1)
        if name.decode() in changed:
            mode, kind, oid = header.split()
            assert mode == b'100644' and kind == b'blob'
            objects[name.decode()] = oid.decode()
    assert set(objects) == changed
    unique = sorted(set(objects.values())); hashes = {}
    with tempfile.TemporaryFile() as requests:
        requests.write(('\n'.join(unique) + '\n').encode()); requests.seek(0)
        process = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=PUB, stdin=requests, stdout=subprocess.PIPE)
        try:
            for requested in unique:
                oid, kind, size = process.stdout.readline().split()
                assert oid.decode() == requested and kind == b'blob'
                remaining = int(size); digest = hashlib.sha256()
                while remaining:
                    chunk = process.stdout.read(min(1048576, remaining)); assert chunk
                    digest.update(chunk); remaining -= len(chunk)
                assert process.stdout.read(1) == b'\n'
                hashes[requested] = digest.hexdigest()
            assert process.stdout.read() == b'' and process.wait() == 0
        finally:
            if process.poll() is None: process.terminate(); process.wait()
    assert {n: hashes[oid] for n, oid in objects.items()} == expected
    return expected


def execute(command, record_name):
    record_path = ROOT / record_name; log = record_path.with_suffix('.log')
    command_path = record_path.with_name(record_path.stem + '-command.json')
    assert not record_path.exists() and not log.exists() and not command_path.exists()
    start = datetime.now(timezone.utc).isoformat(); tick = time.monotonic()
    with log.open('xb') as out:
        run = subprocess.run(command, cwd=PUB, stdout=out, stderr=subprocess.STDOUT)
    record = {'status': 'passed' if run.returncode == 0 else 'failed', 'actual_exit_code': run.returncode,
              'actual_command': command, 'actual_workdir': str(PUB), 'started_at_utc': start,
              'finished_at_utc': datetime.now(timezone.utc).isoformat(), 'elapsed_seconds': time.monotonic() - tick,
              'raw_log': log.relative_to(ROOT).as_posix(), 'raw_log_sha256': sha(log),
              'helper_sha256': sha(Path(__file__)), 'coverage_complete': False}
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
                  'book/coverage/checks/root_commit_push_publication31_v3.py']:
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
        record['expected_committed_paths_sha256'] = expected
        if record['actual_exit_code'] == 0:
            record['commit'] = git(['rev-parse', 'HEAD']).decode().strip()
            assert git(['rev-parse', 'HEAD^']).decode().strip() == BASELINE
            record['actual_committed_paths_sha256'] = verify_committed_tree(expected, BASELINE, record['commit'])
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

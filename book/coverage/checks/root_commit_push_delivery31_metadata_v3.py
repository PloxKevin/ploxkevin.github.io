"""Stage exact real delivery metadata, commit it, or push its recorded commit."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, shutil, subprocess, tempfile, time

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
    path = ROOT / record_name; log = path.with_suffix('.log')
    command_path = path.with_name(path.stem + '-command.json')
    assert not path.exists() and not log.exists() and not command_path.exists()
    started = datetime.now(timezone.utc).isoformat(); tick = time.monotonic()
    with log.open('xb') as out:
        result = subprocess.run(command, cwd=PUB, stdout=out, stderr=subprocess.STDOUT)
    record = {'status': 'passed' if result.returncode == 0 else 'failed', 'actual_exit_code': result.returncode,
              'actual_command': command, 'actual_workdir': str(PUB), 'started_at_utc': started,
              'finished_at_utc': datetime.now(timezone.utc).isoformat(), 'elapsed_seconds': time.monotonic() - tick,
              'raw_log': log.relative_to(ROOT).as_posix(), 'raw_log_sha256': sha(log),
              'content_commit': CONTENT, 'coverage_complete': False}
    with command_path.open('x') as out:
        out.write(json.dumps(record, indent=2) + '\n')
    record['actual_command_receipt'] = {'file': command_path.relative_to(ROOT).as_posix(), 'sha256': sha(command_path)}
    return path, record


ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('mode', choices=['commit', 'push'])
args = ap.parse_args()
try:
    if args.mode == 'commit':
        assert git(['symbolic-ref', '--short', 'HEAD']).decode().strip() == 'main'
        assert git(['rev-parse', 'HEAD']).decode().strip() == CONTENT
        assert not git(['diff', '--cached', '--name-only', '-z'])
        preparation_name = 'reports/full-coverage/publication31-delivery-metadata-preparation-v1.json'
        preparation = read(preparation_name)
        assert preparation['status'] == 'actual_checkpoint31_content_delivery_recorded_metadata_commit_and_push_pending'
        expected = dict(preparation['exact_metadata_paths_sha256'])
        extras = [preparation_name, 'reports/full-coverage/prepare-delivery31-metadata-execution-v1.json',
                  'reports/full-coverage/prepare-delivery31-metadata-execution-v1.log',
                  'book/coverage/checks/root_commit_push_delivery31_metadata_v3.py']
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
        record['expected_committed_paths_sha256'] = {n: expected[n] for n in names}
        if record['actual_exit_code'] == 0:
            record['commit'] = git(['rev-parse', 'HEAD']).decode().strip()
            assert git(['rev-parse', 'HEAD^']).decode().strip() == CONTENT
            record['actual_committed_paths_sha256'] = verify_committed_tree({n: expected[n] for n in names}, CONTENT, record['commit'])
            assert not git(['status', '--porcelain', '-z', '--untracked-files=all'])
        with path.open('x') as out:
            out.write(json.dumps(record, indent=2) + '\n')
    else:
        commit = read(COMMIT)
        assert commit['status'] == 'passed' and commit['actual_exit_code'] == 0
        assert git(['rev-parse', 'HEAD']).decode().strip() == commit['commit']
        assert git(['rev-parse', 'refs/heads/main']).decode().strip() == commit['commit']
        assert git(['symbolic-ref', '--short', 'HEAD']).decode().strip() == 'main'
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
except Exception as error:
    if 'record' in globals() and 'path' in globals() and not path.exists():
        record['status'] = 'failed_post_command_association'
        record['association_error'] = type(error).__name__ + ': ' + str(error)
        record['scope'] = 'The immutable command receipt retains the true subprocess exit code and time; the later association failed.'
        with path.open('x') as out:
            out.write(json.dumps(record, indent=2) + '\n')
    raise

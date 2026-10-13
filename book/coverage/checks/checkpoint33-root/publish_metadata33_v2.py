"""Commit or push the explicit checkpoint33 content-delivery metadata plan."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
PUB = ROOT / 'reports/book/publication-repo'
CONTENT = json.loads((ROOT / 'reports/full-coverage/publication33-commit-v1.json').read_bytes())['commit']
PLAN = 'reports/full-coverage/publication33-delivery-metadata-plan-v2.json'
COMMIT = 'reports/full-coverage/publication33-metadata-commit-v1.json'
PUSH = 'reports/full-coverage/publication33-metadata-push-v1.json'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(n):
    return json.loads((ROOT / n).read_bytes())


def git(args, data=None):
    return subprocess.run(['git', *args], cwd=PUB, capture_output=True, input=data, check=True).stdout


def write(n, d):
    assert not (ROOT / n).exists()
    with (ROOT / n).open('x') as f:
        f.write(json.dumps(d, indent=2) + '\n')


def execute(command, n):
    log = n.replace('.json', '.log')
    original = n.replace('.json', '-command.json')
    assert not any((ROOT / p).exists() for p in [n, log, original])
    start = datetime.now(timezone.utc).isoformat()
    tick = time.monotonic()
    with (ROOT / log).open('xb') as f:
        r = subprocess.run(command, cwd=PUB, stdout=f, stderr=subprocess.STDOUT)
    d = dict(status='passed' if r.returncode == 0 else 'failed', actual_exit_code=r.returncode,
             actual_command=command, actual_workdir=str(PUB), started_at_utc=start,
             finished_at_utc=datetime.now(timezone.utc).isoformat(), elapsed_seconds=time.monotonic()-tick,
             raw_log=log, raw_log_sha256=sha(ROOT / log), coverage_complete=False)
    write(original, d)
    d['actual_command_receipt'] = dict(file=original, sha256=sha(ROOT / original))
    return d


ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('mode', choices=['commit', 'push'])
args = ap.parse_args()
assert git(['symbolic-ref', '--short', 'HEAD']).decode().strip() == 'main'
if args.mode == 'push':
    assert not git(['status', '--porcelain', '-z', '--untracked-files=all'])
if args.mode == 'commit':
    assert git(['rev-parse', 'HEAD']).decode().strip() == CONTENT
    assert git(['ls-remote', 'origin', 'refs/heads/main']).decode().split()[0] == CONTENT
    delivery = read('reports/full-coverage/publication33-content-delivery-v1.json')
    assert delivery['status'] == 'passed_actual_checkpoint33_content_push_Pages_and_all31_live_hashes'
    assert delivery['content_commit'] == CONTENT and delivery['coverage_complete'] is False
    plan = read(PLAN)
    assert plan['status'] == 'exact_verified_content33_delivery_metadata_plan' and plan['content_commit'] == CONTENT
    expected = {**plan['paths_sha256'], PLAN: sha(ROOT / PLAN)}
    assert not git(['diff', '--cached', '--name-only', '-z'])
    # Resume only the exact metadata copies left by the preserved v1 preflight.
    for row in git(['status', '--porcelain', '-z', '--untracked-files=all']).decode().split('\0'):
        if row:
            assert row[:2] in {' M', '??'} and row[3:] in expected
            assert sha(PUB / row[3:]) == expected[row[3:]]
    # Validate every completed Root record before any further copy.
    for n, h in expected.items():
        assert (ROOT / n).is_file() and not (ROOT / n).is_symlink() and sha(ROOT / n) == h
    for n, h in expected.items():
        assert not Path(n).is_absolute() and not {'..', '.git', '.lake', '__pycache__'}.intersection(Path(n).parts)
        assert n.startswith(('book/coverage/', 'reports/full-coverage/', 'README.md')) and not n.endswith('.lean')
        source, target = ROOT / n, PUB / n
        assert source.is_file() and not source.is_symlink() and sha(source) == h
        assert target.resolve().is_relative_to(PUB) and not target.is_symlink()
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    for row in git(['status', '--porcelain', '-z', '--untracked-files=all']).decode().split('\0'):
        if row:
            assert row[:2] in {' M', '??'} and row[3:] in expected
    git(['--literal-pathspecs', 'add', '-f', '--pathspec-from-file=-', '--pathspec-file-nul'], b'\0'.join(n.encode() for n in sorted(expected)) + b'\0')
    changed = {n.decode() for n in git(['diff', '--cached', '--name-only', '-z']).split(b'\0') if n}
    assert changed and changed <= set(expected) and not git(['diff', '--name-only', '-z'])
    for n in changed:
        assert hashlib.sha256(git(['show', ':' + n])).hexdigest() == expected[n]
    record = execute(['git', 'commit', '--quiet', '-m', 'Record checkpoint 33 successful Pages delivery and continuation notes'], COMMIT)
    if record['actual_exit_code'] == 0:
        commit = git(['rev-parse', 'HEAD']).decode().strip()
        assert git(['rev-parse', 'HEAD^']).decode().strip() == CONTENT
        actual = {n.decode() for n in git(['diff-tree', '--no-commit-id', '--name-only', '-r', '-z', '--no-renames', CONTENT, commit]).split(b'\0') if n}
        assert actual == changed
        assert all(hashlib.sha256(git(['show', commit + ':' + n])).hexdigest() == expected[n] for n in changed)
        record.update(commit=commit, parent=CONTENT, actual_committed_paths_sha256={n: expected[n] for n in sorted(changed)})
    write(COMMIT, record)
else:
    previous = read(COMMIT)
    assert previous['status'] == 'passed' and previous['actual_exit_code'] == 0
    assert git(['rev-parse', 'HEAD']).decode().strip() == previous['commit']
    assert git(['ls-remote', 'origin', 'refs/heads/main']).decode().split()[0] == CONTENT
    record = execute(['git', 'push', 'origin', 'main'], PUSH)
    if record['actual_exit_code'] == 0:
        remote = git(['ls-remote', 'origin', 'refs/heads/main']).decode().split()[0]
        assert remote == previous['commit']
        record.update(commit=previous['commit'], remote_main=remote)
    record['metadata_Pages_or_live_success_claimed'] = False
    write(PUSH, record)
print(json.dumps(dict(status=record['status'], commit=record.get('commit'), actual_exit_code=record['actual_exit_code'])))
raise SystemExit(record['actual_exit_code'])

"""Publish only an explicitly verified source snapshot and bounded new evidence."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / 'reports/book/publication-repo'
BASELINE = 'a5fcd43a5bba21f9ebe43a3623c3ef0e054ae387'
PREP = 'reports/full-coverage/publication32-recovery-preparation-v1.json'
COMMIT = 'reports/full-coverage/publication32-recovery-commit-v1.json'
PUSH = 'reports/full-coverage/publication32-recovery-push-v1.json'


def safe(root, n):
    assert isinstance(n, str) and n and Path(n).as_posix() == n
    assert not Path(n).is_absolute() and not {'..', '.git', '.lake', '__pycache__'}.intersection(Path(n).parts)
    p = root / n
    assert p.resolve().is_relative_to(root) and not p.is_symlink()
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(root))
    return p


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(n):
    return json.loads(safe(ROOT, n).read_bytes())


def git(args, data=None):
    return subprocess.run(['git', *args], cwd=PUB, input=data, capture_output=True, check=True).stdout


def new(n, d):
    p = safe(ROOT, n)
    assert not p.exists()
    with p.open('x') as f:
        f.write(json.dumps(d, indent=2) + '\n')


def execute(command, association_name):
    command_name = association_name.replace('.json', '-command.json')
    log = association_name.replace('.json', '.log')
    assert not (ROOT / command_name).exists() and not (ROOT / association_name).exists() and not (ROOT / log).exists()
    started = datetime.now(timezone.utc).isoformat()
    tick = time.monotonic()
    with (ROOT / log).open('xb') as f:
        r = subprocess.run(command, cwd=PUB, stdout=f, stderr=subprocess.STDOUT)
    record = dict(status='passed' if r.returncode == 0 else 'failed', actual_exit_code=r.returncode,
                  actual_command=command, actual_workdir=str(PUB), started_at_utc=started,
                  finished_at_utc=datetime.now(timezone.utc).isoformat(), elapsed_seconds=time.monotonic()-tick,
                  raw_log=log, raw_log_sha256=sha(ROOT / log), coverage_complete=False)
    # Preserve the real subprocess outcome before any subsequent association
    # or network check, including when a later observation fails.
    new(command_name, record)
    record['actual_command_receipt'] = dict(file=command_name, sha256=sha(ROOT / command_name))
    return record


ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('mode', choices=['prepare', 'commit', 'push'])
args = ap.parse_args()
assert git(['symbolic-ref', '--short', 'HEAD']).decode().strip() == 'main'
if args.mode == 'prepare':
    assert git(['rev-parse', 'HEAD']).decode().strip() == BASELINE
    assert not git(['status', '--porcelain', '-z', '--untracked-files=all'])
    assert not safe(ROOT, PREP).exists()
    manifest_name = 'reports/full-coverage/checkpoint-32-manifest.json'
    manifest = read(manifest_name)
    assert manifest['status'] == 'formal_verification_passed_partial_coverage' and manifest['source_only_snapshot'] is True
    assert manifest['old_snapshot_or_lake_tree_copied'] is False
    audit_ref = manifest['successful_verification']
    audit_path = safe(ROOT, audit_ref['report'])
    assert sha(audit_path) == audit_ref['report_sha256']
    audit = json.loads(audit_path.read_bytes())
    assert audit['status'] == 'passed' and audit['proof_file_count'] == 1254 and audit['theorem_count'] == 11267
    assert all(c['exit_code'] == 0 for c in audit['checks'])
    assert all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in audit['axiom_dependencies'].values())
    planned = {n: (safe(ROOT, manifest['snapshot'] + '/' + n), h) for n, h in manifest['frozen_inputs_sha256'].items()}
    def add(n, expected=None):
        assert not any(re.fullmatch(r'checkpoint-\d+', p) for p in Path(n).parts[:-1])
        p = safe(ROOT, n)
        assert p.is_file() and p.stat().st_size < 100_000_000
        h = sha(p)
        assert expected is None or expected == h
        if n in planned:
            # Frozen Applied omits only three unused metadata entries.
            assert h == planned[n][1] or n == 'book/coverage/applied.json'
        else:
            planned[n] = (p, h)
    for n in [manifest_name, 'README.md', 'book/README.md', 'verification/lean/README.md', 'reports/full-coverage/README.md', 'book/coverage/progress.json', 'book/validate28_v1.py', 'book/coverage/checks/recovery32_prepare_runtime.py', 'book/coverage/checks/recovery_finish_delivery31.py', 'book/coverage/checks/recovery32_finalize.py', 'book/coverage/checks/recovery32_install.py', 'book/coverage/checks/recovery32_publish.py', 'reports/full-coverage/checkpoint-32-selection.json', 'reports/full-coverage/checkpoint32-runtime-preparation-recovery-v1.json', 'reports/full-coverage/recovery32-reviewed-six-additions-plan-v1.json', 'reports/full-coverage/owner32-recovery-integration-v1.json', 'reports/full-coverage/ledger32-working-recovery-v1.json', 'reports/full-coverage/ledger32-frozen-source-only-recovery-v1.json', 'reports/full-coverage/integration32-recovery-v3.json', 'reports/full-coverage/publication31-finish-recovery-v1.json']:
        add(n)
    for directory in ['book/coverage/checks/recovery32', 'book/coverage/checks/recovery32-core', 'book/coverage/checks/recovery32-review', 'reports/full-coverage/lean-checkpoint-32-source81-recovery-v1', 'reports/full-coverage/source-history/checkpoint31-before-recovery-closure-v1', 'reports/full-coverage/source-history/owner31-before-recovery32-v1', 'reports/full-coverage/source-history/documentation-before-recovery32-v1']:
        for p in sorted((ROOT / directory).rglob('*')):
            if p.is_file() and not p.is_symlink():
                add(p.relative_to(ROOT).as_posix())
    for pattern in ['*32*recovery*execution*.json', '*32*recovery*execution*.log', '*runtime32*execution*.json', '*runtime32*execution*.log', '*delivery31*recovery*.json', '*delivery31*recovery*.log', '*delivery31-metadata-execution-v1.*', 'publication31-metadata-*', '*live31-metadata*', 'pages31-metadata-jobs-*', 'live-checkpoint-31-attempt[34].json', 'pages-checkpoint-31-attempt[34].*']:
        for p in (ROOT / 'reports/full-coverage').glob(pattern):
            if p.is_file():
                add(p.relative_to(ROOT).as_posix())
    for p in (ROOT / 'book/coverage/checks').glob('CompleteCoreFilippovPolygonal32*'):
        if p.is_file():
            add(p.relative_to(ROOT).as_posix())
    # Peer closures explicitly enumerate their required original records;
    # historical directories and runtime/build trees are never copied.
    for row in read('reports/full-coverage/recovery32-reviewed-six-additions-plan-v1.json')['sources']:
        for r in row['independent_source_reviews']:
            add(r['file'], r['sha256'])
            for n, h in read(r['file']).get('required_evidence_artifacts_sha256', {}).items():
                add(n, h)
    assert audit['source_sha256'] == {n: h for n, (_, h) in planned.items() if n.startswith('SafeLearning/')}
    assert audit['proof_sha256'] == {n: h for n, (_, h) in planned.items() if n.startswith('verification/lean/SafeLearning/') and n.endswith('.lean')}
    for n, (p, h) in planned.items():
        assert sha(p) == h
        safe(PUB, n)
    copied = []
    for n, (p, h) in sorted(planned.items()):
        target = safe(PUB, n)
        if target.is_file() and sha(target) == h:
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(p, target)
        assert sha(target) == h
        copied.append(n)
    record = dict(status='passed_exact_checkpoint32_publication_preparation', baseline=BASELINE,
                  prepared_at_utc=datetime.now(timezone.utc).isoformat(),
                  paths_sha256={n: h for n, (_, h) in planned.items()}, copied_paths=copied,
                  source_only=True, coverage_complete=False, commit_or_delivery_claimed=False)
    new(PREP, record)
    shutil.copyfile(ROOT / PREP, PUB / PREP)
    print(json.dumps(dict(status=record['status'], copied=len(copied), planned=len(planned))))
elif args.mode == 'commit':
    assert git(['rev-parse', 'HEAD']).decode().strip() == BASELINE
    assert not git(['diff', '--cached', '--name-only', '-z'])
    preparation = read(PREP)
    assert preparation['status'] == 'passed_exact_checkpoint32_publication_preparation'
    expected = dict(preparation['paths_sha256'])
    expected[PREP] = sha(ROOT / PREP)
    for n in ['reports/full-coverage/prepare-publication32-recovery-execution-v1.json', 'reports/full-coverage/prepare-publication32-recovery-execution-v1.log']:
        p = safe(ROOT, n)
        assert p.is_file()
        target = safe(PUB, n)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(p, target)
        expected[n] = sha(p)
    for n, h in expected.items():
        assert sha(safe(PUB, n)) == h
    for row in git(['status', '--porcelain', '-z', '--untracked-files=all']).decode().split('\0'):
        if row:
            assert row[:2] in {' M', '??'} and row[3:] in expected, row
    git(['--literal-pathspecs', 'add', '-f', '--pathspec-from-file=-', '--pathspec-file-nul'], b'\0'.join(n.encode() for n in sorted(expected)) + b'\0')
    changed = {n.decode() for n in git(['diff', '--cached', '--name-only', '-z']).split(b'\0') if n}
    assert changed and changed <= set(expected) and not git(['diff', '--name-only', '-z'])
    for n in changed:
        assert hashlib.sha256(git(['show', ':' + n])).hexdigest() == expected[n]
    record = execute(['git', 'commit', '--quiet', '-m', 'Verify checkpoint 32: 83 additional Lean proofs and six material mappings'], COMMIT)
    if record['actual_exit_code']:
        new(COMMIT, record)
        raise SystemExit(record['actual_exit_code'])
    commit = git(['rev-parse', 'HEAD']).decode().strip()
    assert git(['rev-parse', 'HEAD^']).decode().strip() == BASELINE
    actual = {n.decode() for n in git(['diff-tree', '--no-commit-id', '--name-only', '-r', '-z', '--no-renames', BASELINE, commit]).split(b'\0') if n}
    assert actual == changed
    for n in actual:
        assert hashlib.sha256(git(['show', commit + ':' + n])).hexdigest() == expected[n]
    assert not git(['status', '--porcelain', '-z', '--untracked-files=all'])
    record.update(commit=commit, parent=BASELINE, actual_committed_paths_sha256={n: expected[n] for n in sorted(actual)})
    new(COMMIT, record)
    print(json.dumps(dict(status='passed', commit=commit, paths=len(actual))))
else:
    commit = read(COMMIT)['commit']
    assert git(['rev-parse', 'HEAD']).decode().strip() == commit
    assert not git(['status', '--porcelain', '-z', '--untracked-files=all'])
    assert git(['ls-remote', 'origin', 'refs/heads/main']).decode().split()[0] == BASELINE
    record = execute(['git', 'push', 'origin', 'main'], PUSH)
    head = git(['ls-remote', 'origin', 'refs/heads/main']).decode().split()[0]
    record.update(status='passed' if record['actual_exit_code'] == 0 and head == commit else 'failed',
                  commit=commit, remote_main=head, Pages_or_live_success_claimed=False)
    new(PUSH, record)
    print(json.dumps(record))
    raise SystemExit(0 if record['status'] == 'passed' else 1)

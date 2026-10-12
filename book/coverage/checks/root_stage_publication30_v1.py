"""Validate exact prepared checkpoint30 bytes and stage only its explicit list."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, re, shutil, subprocess, tempfile

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / 'reports/book/publication-repo'
RESULT = 'reports/full-coverage/publication30-staged-byte-check-v1.json'
BASELINE = '01b95073d2f78d066ef88c1aa3fd20af1d631e22'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def safe(root, n):
    assert type(n) is str and n and Path(n).as_posix() == n and not Path(n).is_absolute()
    assert not any(p in {'..', '.git', '.lake', '__pycache__'} for p in Path(n).parts)
    assert not any(re.fullmatch(r'checkpoint-\d+', p) for p in Path(n).parts[:-1])
    p = root / n
    assert p.resolve().is_relative_to(root) and not p.is_symlink()
    assert all(not a.is_symlink() for a in p.parents if a.is_relative_to(root))
    return p


def git(args, data=None):
    return subprocess.run(['git', *args], cwd=PUB, input=data, capture_output=True, check=True).stdout


def read(n):
    return json.loads(safe(ROOT, n).read_bytes())


assert git(['rev-parse', 'HEAD']).decode().strip() == BASELINE
assert not git(['diff', '--cached', '--name-only', '-z'])
assert not safe(ROOT, RESULT).exists() and not safe(PUB, RESULT).exists()
prepared_name = 'reports/full-coverage/publication30-prepared-exact-files-v1.json'
prepared = read(prepared_name)
assert prepared['status'] == 'exact_checkpoint30_publication_inputs_prepared_awaiting_staging_and_delivery'
expected = dict(prepared['expected_publication_paths_sha256'])
assert expected == {n: sha(safe(PUB, n)) for n in expected}
native_name = 'reports/full-coverage/prepare-publication30-source-only-execution-v1.json'
native = read(native_name)
assert native['status'] == 'passed' and native['actual_exit_code'] == 0
assert native['actual_command'][1] == 'book/coverage/prepare_publication30_source_only_v3.py'
assert native['helper_sha256_before'] == native['helper_sha256_after'] == {'book/coverage/prepare_publication30_source_only_v3.py': 'f1b8f6ab8c8cceaa0323de4097c2292ce78b1eecfa3ce0297f5cae4f8237e3bb'}
ledger_name = 'reports/full-coverage/publication-checks/ledger-checkpoint-30-v1.json'
ledger = read(ledger_name)
assert ledger['integrity_status'] == 'passed' and ledger['errors'] == [] and ledger['mathematical_coverage_complete'] is False
assert ledger['counts']['material_review_statuses'] == {'reviewed': 4770, 'pending': 8004}
for r in ledger['domains']:
    assert r['ledger_sha256'] == expected['book/coverage/' + r['domain'] + '.json']
extras = [prepared_name, native_name, native['log'], ledger_name,
          'reports/full-coverage/publication30-ledger-execution-v1.json',
          'reports/full-coverage/publication30-ledger-execution-v1.log',
          'reports/full-coverage/prepare-publication30-supplements-execution-v2.json',
          'reports/full-coverage/prepare-publication30-supplements-execution-v2.log',
          'book/coverage/checks/root_stage_publication30_v1.py']
for n in extras:
    source = safe(ROOT, n); target = safe(PUB, n)
    h = sha(source)
    assert n not in expected or expected[n] == h
    target.parent.mkdir(parents=True, exist_ok=True)
    if not target.is_file() or sha(target) != h:
        shutil.copyfile(source, target)
    assert sha(target) == h
    expected[n] = h
manifest = read('reports/full-coverage/checkpoint-30-manifest.json')
assets = {n: h for n, h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets) == 31 and all(expected[n] == h for n, h in assets.items())
proofs = {p.relative_to(PUB).as_posix(): sha(p) for p in (PUB / 'verification/lean/SafeLearning').glob('*.lean') if p.name != 'Smoke.lean'}
assert proofs == {n: r['sha256'] for n, r in manifest['proof_files'].items()} and len(proofs) == 1242
assert all(safe(PUB, n).stat().st_size < 100000000 for n in expected)
rows = git(['status', '--porcelain', '-z', '--untracked-files=all']).decode().split('\0')
for row in rows:
    if row:
        assert row[:2] in {' M', '??'} and row[3:] in expected, row
exclusions = [l[4:] for l in safe(PUB, '_config.yml').read_text().splitlines() if l.startswith('  - ')]
assert exclusions == sorted(set(exclusions))
website_bytes = 0
for directory, subdirs, files in os.walk(PUB):
    rel = Path(directory).relative_to(PUB).as_posix()
    subdirs[:] = [n for n in subdirs if n != '.git' and (rel + '/' + n if rel != '.' else n) not in exclusions]
    for n in files:
        p = Path(directory) / n; name = p.relative_to(PUB).as_posix()
        if any(name == e or name.startswith(e + '/') for e in exclusions):
            continue
        assert not p.is_symlink()
        website_bytes += p.stat().st_size
assert website_bytes < 850000000
git(['--literal-pathspecs', 'add', '-f', '--pathspec-from-file=-', '--pathspec-file-nul'],
    b'\0'.join(n.encode() for n in sorted(expected)) + b'\0')
staged = {n.decode() for n in git(['diff', '--cached', '--name-only', '-z']).split(b'\0') if n}
assert staged and staged <= set(expected) and not git(['diff', '--name-only', '-z'])
objects = {}
for row in git(['ls-files', '--stage', '-z']).split(b'\0'):
    if not row:
        continue
    header, name = row.split(b'\t', 1); mode, oid, stage = header.split()
    assert stage == b'0'
    if name.decode() in staged:
        assert mode == b'100644'
        objects[name.decode()] = oid.decode()
assert set(objects) == staged
# Read actual staged blob bytes in one process, then SHA256 each exact payload.
ordered = sorted(staged)
with tempfile.TemporaryFile() as requests:
    requests.write(('\n'.join(objects[n] for n in ordered) + '\n').encode())
    requests.seek(0)
    process = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=PUB, stdin=requests, stdout=subprocess.PIPE)
    try:
        for n in ordered:
            oid, kind, size = process.stdout.readline().split()
            assert oid.decode() == objects[n] and kind == b'blob'
            remaining = int(size); digest = hashlib.sha256()
            while remaining:
                chunk = process.stdout.read(min(1048576, remaining))
                assert chunk
                digest.update(chunk); remaining -= len(chunk)
            assert digest.hexdigest() == expected[n]
            assert process.stdout.read(1) == b'\n'
        assert process.stdout.read() == b'' and process.wait() == 0
    finally:
        if process.poll() is None:
            process.terminate(); process.wait()
assert git(['rev-parse', 'HEAD']).decode().strip() == BASELINE
report = {'status': 'passed_actual_checkpoint30_staged_blob_sha256_and_partial_ledger_check',
    'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'baseline_publication_head': BASELINE,
    'actual_staged_paths_sha256': {n: expected[n] for n in ordered},
    'staged_file_count': len(staged), 'verified_proof_count': 1242, 'verified_asset_count': 31,
    'included_website_bytes': website_bytes, 'website_budget_bytes': 850000000,
    'actual_publication_ledger': {'file': ledger_name, 'sha256': sha(safe(ROOT, ledger_name))},
    'coverage_complete': False, 'commit_push_Pages_or_live_success_claimed': False}
safe(ROOT, RESULT).write_text(json.dumps(report, indent=2) + '\n')
shutil.copyfile(safe(ROOT, RESULT), safe(PUB, RESULT))
git(['--literal-pathspecs', 'add', '-f', '--', RESULT])
print(json.dumps({'status': report['status'], 'staged_files': len(staged) + 1,
                  'included_website_bytes': website_bytes, 'coverage_complete': False}))

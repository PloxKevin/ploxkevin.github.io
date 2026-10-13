"""Plan, then atomically stage exact checkpoint35 bytes without Git mutations.

--plan --docs-receipt reports/full-coverage/checkpoint35-documentation-v1.json
--apply --plan-sha256 SHA256
An interrupted apply accepts only each destination's recorded before/after bytes.
New native receipts produced by this helper are intentionally outside its plan.
"""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile

SELF = Path(__file__).resolve()
ROOT = SELF.parents[4]
PUB = ROOT / 'reports/book/publication-repo'
BASELINE = '04919a9dbbfce180c18327d74edeb67343030f5a'
SCHEMA = 'checkpoint35.publication-stage.v1'
PLAN = 'reports/full-coverage/publication35-copy-plan-v1.json'
MANIFEST = 'reports/full-coverage/checkpoint-35-manifest.json'
SELECTION = 'reports/full-coverage/checkpoint-35-selection.json'
FINAL = 'reports/full-coverage/checkpoint35-finalization-v1.json'
EXPORT = 'reports/full-coverage/lean-checkpoint-35-source90-v1'
DOCS = {'README.md', 'verification/lean/README.md', 'book/coverage/progress.json',
        'book/coverage/CONTINUATION.md', 'reports/full-coverage/README.md'}
EVIDENCE = ['book/coverage/checks/checkpoint35-' + n for n in ['root', 'review', 'ledgers', 'proofs']]
HISTORIES = ['reports/full-coverage/source-history/' + n + '-before-checkpoint35-v1'
             for n in ['verification', 'owners34', 'documentation34']]
HISTORIES += ['reports/full-coverage/source-history/checkpoint35-failed-helper-inputs-v1']


def safe(root, name):
    p = Path(name)
    assert isinstance(name, str) and name and len(name) <= 4096
    assert not p.is_absolute() and p.as_posix() == name
    assert not {'..', '.git', '.lake', '__pycache__', 'source-objects'}.intersection(p.parts), name
    assert not any(c in name for c in '\0\n\r')
    p = root / p
    assert p.resolve().is_relative_to(root) and not p.is_symlink(), name
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(root)), name
    return p


def destination(name):
    assert not any(re.fullmatch(r'checkpoint-\d+', part) or part.startswith(('runtime-checkpoint-', 'isolated-runtime', 'archive'))
                   for part in Path(name).parts), name
    assert not Path(name).name.endswith(('.olean', '.ilean', '.pyc', '.o', '.trace', '.lock')), name
    return safe(PUB, name)


def sha(p):
    assert p.is_file(), str(p)
    with p.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def ref(name):
    return {'file': name, 'sha256': sha(safe(ROOT, name))}


def exact(row):
    p = safe(ROOT, row['file'])
    assert sha(p) == row['sha256'], row['file']
    if 'bytes' in row:
        assert p.stat().st_size == row['bytes'], row['file']
    return p


def read(name):
    return json.loads(safe(ROOT, name).read_bytes())


def fsync_dir(p):
    fd = os.open(p, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def json_new(p, value):
    p.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix='.' + p.name + '-', dir=p.parent)
    try:
        with os.fdopen(fd, 'wb') as output:
            output.write((json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode())
            output.flush()
            os.fsync(output.fileno())
        os.link(temporary, p)
        fsync_dir(p.parent)
    finally:
        os.unlink(temporary)


def copy_exact(source, target, fingerprint, *, temporary=None):
    target.parent.mkdir(parents=True, exist_ok=True)
    if temporary is None:
        fd, temporary = tempfile.mkstemp(prefix='.' + target.name + '-', dir=target.parent)
    else:
        fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    try:
        with source.open('rb') as original, os.fdopen(fd, 'wb') as output:
            shutil.copyfileobj(original, output, 1024 * 1024)
            output.flush()
            os.fsync(output.fileno())
        assert sha(Path(temporary)) == fingerprint, str(source)
        os.replace(temporary, target)
        fsync_dir(target.parent)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def git(args, data=None):
    process = subprocess.run(['git', *args], cwd=PUB, input=data, capture_output=True)
    assert process.returncode == 0, 'Read-only Git command failed: ' + str(args)
    return process.stdout


def head():
    assert git(['symbolic-ref', '--short', 'HEAD']).decode().strip() == 'main'
    value = git(['rev-parse', 'HEAD']).decode().strip()
    assert value == BASELINE, 'Publication baseline HEAD changed'
    return value


def dirty():
    raw = git(['status', '--porcelain', '-z', '--untracked-files=all'])
    result = {}
    for row in raw.split(b'\0'):
        if not row:
            continue
        assert len(row) > 3 and row[2:3] == b' '
        state, name = row[:2].decode(), row[3:].decode()
        assert state in {' M', '??'}, 'Unexpected index/deletion/rename change: ' + name
        result[name] = state
    return result


def files_bounded(name, depth=0, budget=None):
    """Walk only explicit evidence/history roots, never the whole reports tree."""
    budget = [0] if budget is None else budget
    p = safe(ROOT, name)
    assert p.is_dir(), name
    result = []
    for child in sorted(p.iterdir()):
        if child.name == '__pycache__' or child.name.startswith('.') or child.suffix in {'.pyc', '.lock'}:
            continue
        n = child.relative_to(ROOT).as_posix()
        safe(ROOT, n)
        if child.is_dir():
            assert depth > 0, 'Unexpected evidence subdirectory: ' + n
            result.extend(files_bounded(n, depth - 1, budget))
        else:
            assert child.is_file(), n
            budget[0] += 1
            assert budget[0] <= 5000, 'Explicit evidence root exceeds bounded file count'
            result.append(n)
    return result


def new35_reports():
    selected = {}
    for p in sorted((ROOT / 'reports/full-coverage').iterdir()):
        if not p.is_file() or '35' not in p.name or p.suffix not in {'.json', '.log'}:
            continue
        if p.name.startswith('publication35-'):
            continue  # This helper's plan/stage/metadata are separately hash-bound.
        selected[p.relative_to(ROOT).as_posix()] = p
    incomplete = set()
    for name in selected:
        if name.endswith('.started.json'):
            final = name.removesuffix('.started.json') + '.json'
            if not safe(ROOT, final).exists():
                incomplete.update({name, final, final.removesuffix('.json') + '.log'})
    # Legacy recorder logs are bound by their completed final receipt as well.
    for name in selected:
        if name.endswith('.log'):
            final = name.removesuffix('.log') + '.json'
            if not safe(ROOT, final).exists():
                incomplete.add(name)
    return sorted(set(selected) - incomplete), sorted(incomplete)


def validate_native(name):
    d = read(name)
    if not isinstance(d, dict) or not isinstance(d.get('actual_command'), list) or not isinstance(d.get('log'), str):
        return
    assert d['status'] in {'passed', 'failed', 'interrupted', 'spawn_failed', 'recorder_failed'}, name
    assert d['status'] != 'passed' or d['actual_exit_code'] == 0, name
    assert sha(safe(ROOT, d['log'])) == d['log_sha256'], name
    if d.get('started_receipt'):
        assert read(d['started_receipt'])['status'] == 'started'
        assert sha(safe(ROOT, d['started_receipt'])) == d['started_receipt_sha256'], name


def build_plan(plan_name, docs_name):
    head()
    assert not dirty(), 'Publication checkout must be clean before planning'
    final, manifest, selection, docs = read(FINAL), read(MANIFEST), read(SELECTION), read(docs_name)
    assert final['status'] == 'passed_checkpoint35_actual_audit_export_and_source_only_freeze'
    assert final['manifest'] == ref(MANIFEST) and final['selection'] == ref(SELECTION)
    assert manifest['status'] == 'formal_verification_passed_partial_coverage'
    assert manifest['source_only_snapshot'] is True and manifest['old_snapshot_or_lake_tree_copied'] is False
    assert manifest['snapshot'] == 'reports/full-coverage/checkpoint-35'
    assert manifest['coverage_complete'] is False and len(selection['proof_files']) == 1267
    assert manifest['selection_sha256'] == sha(safe(ROOT, SELECTION))
    assert final['proof_files'] == 1267 and final['public_theorems'] == 11472
    assert docs['status'].startswith('passed') and docs['coverage_complete'] is False
    assert docs['finalization'] == ref(FINAL) and set(docs['document_sha256']) == DOCS
    for n, h in docs['document_sha256'].items():
        assert sha(safe(ROOT, n)) == h, n
    baseline = json.loads(exact(selection['baseline_selection']).read_bytes())
    assert len(baseline['proof_files']) == 1264
    assert set(p.relative_to(PUB).as_posix() for p in (PUB / 'verification/lean/SafeLearning').glob('*.lean')) == set(baseline['proof_files'])
    for n, r in baseline['proof_files'].items():
        assert sha(destination(n)) == r['sha256'] == selection['proof_files'][n]['sha256'], n
    planned = {}

    def add(source_name, target_name=None, expected=None):
        target_name = source_name if target_name is None else target_name
        source, target = safe(ROOT, source_name), destination(target_name)
        fingerprint = sha(source)
        assert expected is None or expected == fingerprint, source_name
        row = dict(source=source_name, destination=target_name, sha256=fingerprint, bytes=source.stat().st_size,
                   destination_sha256_before=sha(target) if target.exists() else None)
        if target_name in planned:
            assert planned[target_name] == row, target_name
        planned[target_name] = row

    frozen = manifest['frozen_inputs_sha256']
    for n, h in sorted(frozen.items()):
        add(manifest['snapshot'] + '/' + n, n, h)
    assert 'verification/lean/SafeLearning.lean' in frozen
    assert {n: frozen[n] for n in selection['proof_files']} == {n: r['sha256'] for n, r in selection['proof_files'].items()}
    site = {n: h for n, h in frozen.items() if n.startswith('SafeLearning/')}
    assert len(site) == 31
    for n, h in site.items():
        assert sha(destination(n)) == sha(safe(ROOT, n)) == h, n
    for n, h in docs['document_sha256'].items():
        add(n, expected=h)
    for row in docs['preserved_original_documents'].values():
        exact(row)
        add(row['file'], expected=row['sha256'])
    exact(docs['remaining_exercises'])
    add(docs['remaining_exercises']['file'], expected=docs['remaining_exercises']['sha256'])
    add(docs_name)
    add('.ignore')
    for row in [final['manifest'], final['selection'], final['audit'], final['native_execution'],
                final['owner_integration'], final['working_ledger'], final['frozen_ledger']]:
        exact(row)
        add(row['file'], expected=row['sha256'])
    for n in files_bounded(EXPORT):
        add(n)
    for folder in EVIDENCE:
        for n in files_bounded(folder, 2 if folder.endswith('-proofs') else 0):
            add(n)
    for folder in HISTORIES:
        for n in files_bounded(folder, 4):
            add(n)
    reports, incomplete = new35_reports()
    for n in reports:
        if n == plan_name:
            continue
        if n.endswith('.json') and not n.endswith('.started.json'):
            validate_native(n)
        add(n)
    assert len(planned) <= 6000
    plan_target = destination(plan_name)
    return dict(schema=SCHEMA, status='ready_exact_checkpoint35_publication_stage', expected_head=BASELINE,
        publication_checkout=PUB.relative_to(ROOT).as_posix(), recorder=ref(SELF.relative_to(ROOT).as_posix()),
        manifest=ref(MANIFEST), documentation=ref(docs_name), proof_files=1267, public_theorems=11472,
        selected_proof_sha256={n: r['sha256'] for n, r in selection['proof_files'].items()}, unchanged_site_sha256=site,
        files=[planned[n] for n in sorted(planned)], incomplete_native_attempts_excluded=incomplete,
        self_publication_destination=plan_name, self_destination_sha256_before=sha(plan_target) if plan_target.exists() else None,
        self_hash_binding='Apply copies the plan using the explicit --plan-sha256 argument; the apply receipt records its exact mapping.',
        git_index_mutated=False, coverage_complete=False,
        scope='Only frozen selected normal sources, explicit checkpoint35 evidence and completed receipts. No earlier snapshot, cache, archive, object-store or runtime tree is copied.')


def plan_rows(plan, name, fingerprint):
    assert plan['schema'] == SCHEMA and plan['status'] == 'ready_exact_checkpoint35_publication_stage'
    assert plan['expected_head'] == BASELINE and plan['publication_checkout'] == PUB.relative_to(ROOT).as_posix()
    assert plan['recorder'] == ref(SELF.relative_to(ROOT).as_posix()), 'Publication helper bytes changed'
    assert plan['self_publication_destination'] == name
    rows = [*plan['files'], dict(source=name, destination=name, sha256=fingerprint,
        bytes=safe(ROOT, name).stat().st_size, destination_sha256_before=plan['self_destination_sha256_before'])]
    assert len(rows) <= 6001 and len({r['destination'] for r in rows}) == len(rows)
    for r in rows:
        assert re.fullmatch('[0-9a-f]{64}', r['sha256'])
        exact({'file': r['source'], 'sha256': r['sha256'], 'bytes': r['bytes']})
        destination(r['destination'])
    return rows


def scratch(row, plan_sha256):
    token = hashlib.sha256((plan_sha256 + '\0' + row['destination']).encode()).hexdigest()[:24]
    return destination(row['destination']).parent / ('.checkpoint35-' + token + '.tmp')


def apply(plan, name, fingerprint):
    rows = plan_rows(plan, name, fingerprint)
    changed = {r['destination'] for r in rows if r['destination_sha256_before'] != r['sha256']}
    start_name = str(Path(name).with_name(Path(name).stem + '-stage.started.json'))
    out_name = str(Path(name).with_name(Path(name).stem + '-applied.json'))
    start, out = safe(ROOT, start_name), safe(ROOT, out_name)
    head()
    reused = out.exists()
    if start.exists():
        initial = read(start_name)
        assert initial['plan'] == {'file': name, 'sha256': fingerprint} and initial['expected_head'] == BASELINE
        # A hard kill may leave a partial copy. Only this plan's exact scratch
        # names are authorized for cleanup by the durable matching start marker.
        for r in rows:
            temporary = scratch(r, fingerprint)
            safe(PUB, temporary.relative_to(PUB).as_posix())
            if temporary.exists():
                assert temporary.is_file()
                temporary.unlink()
                fsync_dir(temporary.parent)
    status = dirty()
    assert set(status) <= changed, 'Unexpected dirty publication paths: ' + str(sorted(set(status) - changed))
    if not start.exists():
        assert not reused and not status, 'Initial stage requires a clean checkout'
        for r in rows:
            p = destination(r['destination'])
            assert (sha(p) if p.exists() else None) == r['destination_sha256_before'], r['destination']
        initial = dict(status='started_exact_checkpoint35_publication_stage', plan={'file': name, 'sha256': fingerprint},
            expected_head=BASELINE, started_at_utc=datetime.now(timezone.utc).isoformat())
        json_new(start, initial)
    for r in rows:
        p = destination(r['destination'])
        current = sha(p) if p.exists() else None
        assert current in {r['destination_sha256_before'], r['sha256']}, 'Unexpected destination bytes: ' + r['destination']
        if reused:
            assert current == r['sha256'], 'Completed stage destination differs: ' + r['destination']
    # Reject any corrupt destination before continuing an interrupted stage.
    for r in rows:
        p = destination(r['destination'])
        current = sha(p) if p.exists() else None
        assert current in {r['destination_sha256_before'], r['sha256']}, r['destination']
        if not reused and current != r['sha256']:
            copy_exact(safe(ROOT, r['source']), p, r['sha256'], temporary=scratch(r, fingerprint))
    for r in rows:
        assert sha(destination(r['destination'])) == r['sha256']
        exact({'file': r['source'], 'sha256': r['sha256'], 'bytes': r['bytes']})
    assert set(p.relative_to(PUB).as_posix() for p in (PUB / 'verification/lean/SafeLearning').glob('*.lean')) == set(plan['selected_proof_sha256'])
    assert all(sha(destination(n)) == h for n, h in plan['unchanged_site_sha256'].items())
    head()
    assert set(dirty()) <= changed
    if reused:
        saved = read(out_name)
        assert saved['plan'] == {'file': name, 'sha256': fingerprint} and saved['files'] == rows
        assert saved['stage_started'] == ref(start_name) and saved['status'] == 'passed_exact_checkpoint35_bytes_staged_git_pending'
    else:
        # List ignored raw logs so Root can explicitly add their exact paths.
        process = subprocess.run(['git', 'check-ignore', '--stdin', '-z'], cwd=PUB,
            input=b''.join(r['destination'].encode() + b'\0' for r in rows), capture_output=True)
        assert process.returncode in {0, 1}, 'Read-only ignored-path inspection failed'
        ignored = [n.decode() for n in process.stdout.split(b'\0') if n]
        saved = dict(status='passed_exact_checkpoint35_bytes_staged_git_pending', plan={'file': name, 'sha256': fingerprint},
            stage_started=ref(start_name), expected_head=BASELINE, files=rows,
            ignored_paths_requiring_git_add_force=ignored, proof_files=1267, public_theorems=11472,
            unchanged_site_assets=31, git_index_mutated=False, commit_or_push_claimed=False, coverage_complete=False)
        json_new(out, saved)
    return out_name, reused


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--plan', action='store_true')
    mode.add_argument('--apply', action='store_true')
    parser.add_argument('--plan-file', default=PLAN)
    parser.add_argument('--plan-sha256')
    parser.add_argument('--docs-receipt')
    args = parser.parse_args()
    lock = safe(ROOT, 'reports/full-coverage/publication35-stage.lock')
    lock.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(lock, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        p = safe(ROOT, args.plan_file)
        if args.plan:
            assert args.docs_receipt and not args.plan_sha256
            if p.exists():
                value = read(args.plan_file)
                assert value['documentation'] == ref(args.docs_receipt)
                plan_rows(value, args.plan_file, sha(p))
                reused = True
            else:
                value = build_plan(args.plan_file, args.docs_receipt)
                json_new(p, value)
                reused = False
            print(json.dumps(dict(status=value['status'], plan=ref(args.plan_file), files=len(value['files']), reused=reused)))
        else:
            assert args.plan_sha256 and re.fullmatch('[0-9a-f]{64}', args.plan_sha256)
            assert sha(p) == args.plan_sha256
            name, reused = apply(read(args.plan_file), args.plan_file, args.plan_sha256)
            print(json.dumps(dict(status='passed_exact_checkpoint35_bytes_staged_git_pending', record=ref(name), reused=reused)))
    except (AssertionError, OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps(dict(status='refused_publication35_stage', error=str(error), checkout_commit_or_push_claimed=False)))
        return 1
    finally:
        os.close(fd)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

"""Publish verified checkpoint33 source files and explicit bounded evidence.

Prepared from recovery32_publish.py; no executed helper is changed. Runtime
and snapshot directories are forbidden publication destinations. An exact
delivery plan provides finalized docs, QA gates and artifact references.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
PUB = ROOT / 'reports/book/publication-repo'
BASELINE = 'c85ef5d82103a0033a3f2c291af452be835f34d6'
PREP = 'reports/full-coverage/publication33-preparation-v1.json'
COMMIT = 'reports/full-coverage/publication33-commit-v1.json'
PUSH = 'reports/full-coverage/publication33-push-v1.json'
MANIFEST = 'reports/full-coverage/checkpoint-33-manifest.json'
SELECTION = 'reports/full-coverage/checkpoint-33-selection.json'
FROZEN_LEDGER = 'reports/full-coverage/ledger33-frozen-source-only-v1.json'
READINESS = 'book/coverage/checks/checkpoint33-proofs/actual-reviewed33-seven-canonical-paired-readiness-v1.json'
READINESS_SHA = 'c4a570116a807043fec19351b5b082b862c7b37d6ede0583d9c75d79e6b0f8c6'
DOCUMENTS = {'_config.yml', 'README.md', 'book/README.md', 'verification/lean/README.md',
             'reports/full-coverage/README.md', 'book/coverage/progress.json',
             'book/coverage/CONTINUATION.md', 'book/coverage/remaining-exercises33.json'}
REQUIRED_QA = {'reports/full-coverage/integration33-source88-v1.json',
               'reports/full-coverage/browser33-source88-changed-regions-v1.json',
               'reports/full-coverage/browser33-source88-learning-v1.json'}
EXCLUDED_DUPLICATES = {'book/coverage/checks/checkpoint33-ledgers/isolated-ledger-audit-v2.json'}


def safe(root, n):
    assert isinstance(n, str) and n and Path(n).as_posix() == n
    assert not Path(n).is_absolute() and not {'..', '.git', '.lake', '__pycache__'}.intersection(Path(n).parts)
    assert not any(c in n for c in '\0\n\r')
    p = root / n
    assert p.resolve().is_relative_to(root) and not p.is_symlink()
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(root))
    return p


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(n, expected=None):
    p = safe(ROOT, n)
    if expected is not None:
        assert sha(p) == expected, n
    return json.loads(p.read_bytes())


def forbidden_destination(n):
    name = Path(n).name
    return (name.endswith(('.olean', '.ilean', '.pyc', '.o', '.trace')) or '.olean.' in name
            or any(re.fullmatch(r'checkpoint-\d+', part) or part.startswith('runtime-checkpoint-')
                   or part.startswith('isolated-runtime') for part in Path(n).parts))


def exact(r):
    p = safe(ROOT, r['file'])
    assert p.is_file() and sha(p) == r['sha256'], r['file']
    if 'bytes' in r:
        assert p.stat().st_size == r['bytes']
    return p


def passed_quality(report):
    rows = report if isinstance(report, list) else [report]
    assert rows and all(isinstance(row, dict) for row in rows)
    for row in rows:
        assert (row['status'] in {'passed', 'PASS'} or row['status'].startswith('passed_')) and row.get('errors', []) == []
        for key in ['actual_exit_code', 'exit_code']:
            if key in row:
                assert type(row[key]) is int and row[key] == 0


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
ap.add_argument('--manifest-sha256')
ap.add_argument('--selection-sha256')
ap.add_argument('--frozen-ledger-sha256')
ap.add_argument('--evidence-plan')
ap.add_argument('--evidence-plan-sha256')
ap.add_argument('--preparation-sha256')
ap.add_argument('--prepare-execution-sha256')
ap.add_argument('--prepare-log-sha256')
ap.add_argument('--commit-receipt-sha256')
args = ap.parse_args()
for key, value in vars(args).items():
    if key.endswith('_sha256') and value is not None:
        assert re.fullmatch('[0-9a-f]{64}', value), key
assert git(['symbolic-ref', '--short', 'HEAD']).decode().strip() == 'main'
if args.mode == 'prepare':
    assert git(['rev-parse', 'HEAD']).decode().strip() == BASELINE
    assert not git(['status', '--porcelain', '-z', '--untracked-files=all'])
    assert not safe(ROOT, PREP).exists()
    assert all([args.manifest_sha256, args.selection_sha256, args.frozen_ledger_sha256,
                args.evidence_plan, args.evidence_plan_sha256])
    manifest_name = MANIFEST
    manifest = read(manifest_name, args.manifest_sha256)
    assert manifest['status'] == 'formal_verification_passed_partial_coverage' and manifest['source_only_snapshot'] is True
    assert manifest['old_snapshot_or_lake_tree_copied'] is False
    assert manifest['snapshot'] == 'reports/full-coverage/checkpoint-33'
    audit_ref = manifest['successful_verification']
    audit_path = safe(ROOT, audit_ref['report'])
    assert sha(audit_path) == audit_ref['report_sha256']
    audit = json.loads(audit_path.read_bytes())
    assert audit['status'] == 'passed' and audit['proof_file_count'] == 1261 and audit['theorem_count'] == 11345
    assert all(c['exit_code'] == 0 for c in audit['checks'])
    assert all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in audit['axiom_dependencies'].values())
    assert audit_ref['fresh_kernel_replays'] == 7 and audit_ref['exact_reused_kernel_checks'] == 1254
    assert audit_ref['snapshot_execution_claimed'] is False
    selection = read(SELECTION, args.selection_sha256)
    assert manifest['selection_sha256'] == args.selection_sha256
    assert audit['proof_sha256'] == {n: r['sha256'] for n, r in selection['proof_files'].items()}
    frozen = read(FROZEN_LEDGER, args.frozen_ledger_sha256)
    assert frozen['integrity_status'] == 'passed' and frozen['errors'] == []
    assert frozen['mathematical_coverage_complete'] is False
    assert frozen['counts']['material_review_statuses'] == {'reviewed': 4851, 'pending': 7923}
    evidence = read(args.evidence_plan, args.evidence_plan_sha256)
    assert evidence['status'] == 'passed_checkpoint33_delivery_inputs_ready_for_publication'
    assert evidence['checkpoint'] == 33 and evidence['source_revision'] == 88 and evidence['coverage_complete'] is False
    assert DOCUMENTS <= {r['file'] for r in evidence['documents']}
    assert REQUIRED_QA <= {r['file'] for r in evidence['quality_checks']}
    for r in evidence['documents']:
        exact(r)
    for r in evidence['quality_checks']:
        passed_quality(json.loads(exact(r).read_bytes()))
    visual_review = json.loads(exact(evidence['visual_review']).read_bytes())
    passed_quality(visual_review)
    assert visual_review['region_view_image_count'] == 18
    assert visual_review['additional_scroll_view_image_count'] == 1
    assert visual_review['application_lab_view_image_count'] == 4
    assert visual_review['source_bytes_preserved'] is True
    assert visual_review['source_sha256_before'] == visual_review['source_sha256_after']
    assert all(audit['source_sha256'][n] == h for n, h in visual_review['source_sha256_after'].items())
    planned = {n: (safe(ROOT, manifest['snapshot'] + '/' + n), h) for n, h in manifest['frozen_inputs_sha256'].items()}
    def add(n, expected=None):
        assert not forbidden_destination(n), n
        p = safe(ROOT, n)
        assert p.is_file() and p.stat().st_size < 100_000_000
        h = sha(p)
        assert expected is None or expected == h
        if n in planned:
            # Frozen Applied omits only three unused metadata entries.
            assert h == planned[n][1] or n == 'book/coverage/applied.json'
        else:
            planned[n] = (p, h)
    for n in [manifest_name, SELECTION, FROZEN_LEDGER, args.evidence_plan, 'book/validate28_v1.py',
              'reports/full-coverage/checkpoint33-runtime-source88-preparation-v1.json',
              'reports/full-coverage/checkpoint33-additions-plan-v1.json',
              'reports/full-coverage/checkpoint33-source-corrections82-88-v1.json',
              'reports/full-coverage/owner33-integration-v1.json',
              'reports/full-coverage/ledger33-working-v1.json',
              'reports/full-coverage/verify-runtime33-execution-v1.json']:
        add(n)
    for r in [*evidence['documents'], *evidence['quality_checks'], evidence['visual_review'], *evidence['files']]:
        exact(r)
        add(r['file'], r['sha256'])
    config = safe(ROOT, '_config.yml').read_text()
    assert '  - book/coverage/checks\n' in config
    for ordinal in range(82, 89):
        for phase in ['before', 'after']:
            assert '  - book/coverage/inventory-' + phase + '-correction' + str(ordinal) + '.json\n' in config
    retained_duplicate_refs = {}
    for directory in ['book/coverage/checks/checkpoint33-proofs', 'book/coverage/checks/checkpoint33-root',
                      'book/coverage/checks/checkpoint33-review', 'book/coverage/checks/checkpoint33-ledgers',
                      'reports/full-coverage/lean-checkpoint-33-source88-v1']:
        for p in sorted((ROOT / directory).rglob('*')):
            n = p.relative_to(ROOT).as_posix()
            if not p.is_file() or p.is_symlink() or '__pycache__' in p.parts:
                continue
            if n in EXCLUDED_DUPLICATES or forbidden_destination(n):
                retained_duplicate_refs[n] = sha(p)
                continue
            add(n)
    # Include immutable candidate and original owner bytes exactly as reviewed.
    # Never recursively copy the isolated candidate-validation tree.
    integration = read('reports/full-coverage/owner33-integration-v1.json')
    assert integration['applied'] is True and integration['coverage_complete'] is False
    assert {r['destination'] for r in integration['exact_replacements']} == {'book/coverage/'+d+'.json' for d in ['foundations', 'applied', 'modules', 'core']}
    for replacement in integration['exact_replacements']:
        for key in ['candidate', 'preserved_original', 'exact_inverse', 'independent_mapping_peer']:
            r = replacement[key]
            exact(r)
            add(r['file'], r['sha256'])
        frozen_owner = planned[replacement['destination']][0]
        candidate = exact(replacement['candidate'])
        if replacement['destination'] != 'book/coverage/applied.json':
            assert sha(frozen_owner) == sha(candidate)
        else:
            owner = json.loads(candidate.read_bytes())
            unused = {'verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean',
                      'verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean',
                      'verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean'}
            assert unused <= set(owner['proof_files'])
            owner['proof_files'] = {n: r for n, r in owner['proof_files'].items() if n not in unused}
            if 'proof_sha256' in owner:
                owner['proof_sha256'] = {n: h for n, h in owner['proof_sha256'].items() if n not in unused}
            assert json.loads(frozen_owner.read_bytes()) == owner
    # Full mathematical peers enumerate the required original evidence by hash.
    # No broad future32 directory or prior snapshot is selected.
    readiness = read(READINESS, READINESS_SHA)
    assert readiness['source_count'] == 7 and readiness['public_theorem_count'] == 78
    for row in readiness['sources']:
        narrow = row['independent_narrow_wording_and_parser_peer']
        exact(narrow)
        add(narrow['file'], narrow['sha256'])
        for r in row['independent_source_peers']:
            add(r['file'], r['sha256'])
            for n, h in read(r['file']).get('required_evidence_artifacts_sha256', {}).items():
                add(n, h)
    application = read('reports/full-coverage/checkpoint33-source-corrections82-88-v1.json')
    assert [r['correction_id'] for r in application['applications']] == list(range(82, 89))
    for row in application['applications']:
        for key in ['historical_source', 'inventory_before', 'inventory_after', 'source_proposal',
                    'independent_semantic_review', 'cumulative_independent_review', 'actual_fresh_parser']:
            r = row[key]
            exact(r)
            add(r['file'], r['sha256'])
        native = json.loads(exact(row['actual_fresh_parser']).read_bytes())
        codes = [native[k] for k in ['actual_exit_code', 'exit_code'] if k in native]
        assert codes and all(type(code) is int and code == 0 for code in codes)
        raw = native.get('raw_log', native.get('log'))
        if isinstance(raw, dict):
            exact(raw)
            add(raw['file'], raw['sha256'])
        else:
            assert isinstance(raw, str)
            add(raw, native.get('raw_log_sha256', native.get('log_sha256')))
    assert audit['source_sha256'] == {n: h for n, (_, h) in planned.items() if n.startswith('SafeLearning/')}
    assert audit['proof_sha256'] == {n: h for n, (_, h) in planned.items() if n.startswith('verification/lean/SafeLearning/') and n.endswith('.lean')}
    assert all(planned[n][1] == h for n, h in audit['project_sha256'].items())
    for n, (p, h) in planned.items():
        assert not forbidden_destination(n), n
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
    record = dict(status='passed_exact_checkpoint33_publication_preparation', baseline=BASELINE,
                  prepared_at_utc=datetime.now(timezone.utc).isoformat(),
                  paths_sha256={n: h for n, (_, h) in planned.items()}, copied_paths=copied,
                  manifest=dict(file=MANIFEST, sha256=args.manifest_sha256),
                  evidence_plan=dict(file=args.evidence_plan, sha256=args.evidence_plan_sha256),
                  retained_exact_refs_for_duplicate_artifacts=retained_duplicate_refs,
                  runtime_or_snapshot_directory_copied=False,
                  source_only=True, coverage_complete=False, commit_or_delivery_claimed=False)
    new(PREP, record)
    shutil.copyfile(ROOT / PREP, PUB / PREP)
    print(json.dumps(dict(status=record['status'], copied=len(copied), planned=len(planned))))
elif args.mode == 'commit':
    assert all([args.preparation_sha256, args.prepare_execution_sha256, args.prepare_log_sha256])
    assert git(['rev-parse', 'HEAD']).decode().strip() == BASELINE
    assert not git(['diff', '--cached', '--name-only', '-z'])
    preparation = read(PREP, args.preparation_sha256)
    assert preparation['status'] == 'passed_exact_checkpoint33_publication_preparation'
    expected = dict(preparation['paths_sha256'])
    expected[PREP] = sha(ROOT / PREP)
    for n, h in [('reports/full-coverage/prepare-publication33-execution-v1.json', args.prepare_execution_sha256),
                 ('reports/full-coverage/prepare-publication33-execution-v1.log', args.prepare_log_sha256)]:
        p = safe(ROOT, n)
        assert p.is_file() and sha(p) == h
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
    record = execute(['git', 'commit', '--quiet', '-m', 'Verify checkpoint 33: 78 additional Lean proofs and ten material mappings'], COMMIT)
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
    assert args.commit_receipt_sha256
    association = read(COMMIT, args.commit_receipt_sha256)
    actual = json.loads(exact(association['actual_command_receipt']).read_bytes())
    assert association['actual_exit_code'] == actual['actual_exit_code'] == 0
    commit = association['commit']
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

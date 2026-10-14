"""Snapshot and stage exactly the Source91 piece01 candidate proof runtime.

This is a source-only operation. A native aggregate audit and independent
source correspondence approval run separately; preparation promotes no owner
or coverage status. Existing bytes and receipts are never overwritten.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile

ROOT = Path(__file__).resolve().parents[3]
PIECE = 'book/coverage/source91-piece01'
SELF = PIECE + '/prepare_runtime.py'
PRIOR = 'reports/solution-review/runtime-source91-selected35-v1'
AUDIT = PRIOR + '/reports/lean-verification/verification.json'
AUDIT_SHA256 = 'c12c9e237cf3d882baf843d38d6c3ca56cda925ee852298ab5a364c357800f50'
PRIOR_PREPARATION = 'reports/solution-review/source91-runtime-preparation-v1.json'
PRIOR_PREPARATION_SHA256 = '9e952d0cd79de8e988ad423af659df7d902550911155b7abe844329d97a38f44'
RUNTIME = 'reports/full-coverage/runtime-source91-piece01-v1'
PLAN = PIECE + '/runtime-plan-v1.json'
REPORT = PIECE + '/runtime-preparation-v1.json'
CLAIMS = PIECE + '/claims-v2.json'
CLAIMS_SHA256 = '3c36aaf6fa44e454492a2d63bbac11a3e1fac31d89b1fa13091975c3b7e84b87'
OBJECTS = 'reports/full-coverage/source-objects'
AGGREGATE = 'verification/lean/SafeLearning.lean'
SUPPORT = 'book/coverage/lean_names.py'
PROJECT = {'verification/lean/lean-toolchain', 'verification/lean/lakefile.toml',
           'verification/lean/lake-manifest.json', 'verification/lean/verify.py'}
ADDITIONS = ('CompleteModulesLandscapeARLawLimit',
             'CompleteModulesLandscapeStationaryCharacterization',
             'CompleteModulesLandscapeARPathFluctuation',
             'CompleteModulesLandscapeSource91ARPartI')
PROOF_NAME = re.compile(r'verification/lean/SafeLearning/[A-Za-z_][A-Za-z0-9_]*\.lean\Z')


def path(name):
    p = Path(name)
    assert isinstance(name, str) and name and not p.is_absolute() and p.as_posix() == name
    assert not {'..', '.git', '.lake', '__pycache__'}.intersection(p.parts)
    p = ROOT / p
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink(), name
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(ROOT)), name
    return p


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def ref(name):
    raw = path(name).read_bytes()
    return {'file': name, 'sha256': sha(raw), 'bytes': len(raw)}


def read(name):
    return json.loads(path(name).read_bytes())


def exact(row):
    raw = path(row['file']).read_bytes()
    assert sha(raw) == row['sha256'], 'Bound source differs: ' + row['file']
    if 'bytes' in row:
        assert len(raw) == row['bytes'], row['file']
    return raw


def encode(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()


def fsync_directory(directory):
    descriptor = os.open(directory, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def put(name, raw, *, readonly=False):
    """Install an immutable complete file without replacing a competing file."""
    target = path(name)
    if target.exists():
        assert target.read_bytes() == raw, 'Existing artifact differs: ' + name
        if readonly:
            assert not target.stat().st_mode & 0o222, 'Writable source object: ' + name
        return
    target.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix='.' + target.name + '-', dir=target.parent)
    try:
        with os.fdopen(descriptor, 'wb') as stream:
            stream.write(raw)
            stream.flush()
            if readonly:
                os.fchmod(stream.fileno(), 0o444)
            os.fsync(stream.fileno())
        try:
            os.link(temporary, target)
        except FileExistsError:
            assert path(name).read_bytes() == raw, 'Concurrent artifact differs: ' + name
        if readonly:
            assert not target.stat().st_mode & 0o222, 'Writable source object: ' + name
        fsync_directory(target.parent)
    finally:
        os.unlink(temporary)


def aggregate(proofs):
    return ('\n'.join('import SafeLearning.' + Path(n).stem for n in sorted(proofs)) + '\n').encode()


def protect(inputs):
    for name, fingerprint in inputs.items():
        assert ref(name)['sha256'] == fingerprint, 'Input edited: ' + name


def cache_links():
    result = {}
    project = path(PRIOR + '/verification/lean')
    for part in ('packages', 'build'):
        source = project / '.lake' / part
        original = ROOT / 'verification/lean/.lake' / part
        assert source.is_symlink() and source.is_dir() and original.is_dir()
        assert source.resolve() == original.resolve()
        result[part] = {'source': PRIOR + '/verification/lean/.lake/' + part,
                        'resolved_target': str(original.resolve())}
    return result


def model(plan_name, claims_name=CLAIMS, claims_sha256=CLAIMS_SHA256):
    """Read only explicit baseline/addition paths; never scan the working proofs."""
    assert ref(AUDIT)['sha256'] == AUDIT_SHA256
    assert ref(PRIOR_PREPARATION)['sha256'] == PRIOR_PREPARATION_SHA256
    audit, preparation = read(AUDIT), read(PRIOR_PREPARATION)
    assert audit['status'] == 'passed' and audit['proof_file_count'] == 1267 and audit['theorem_count'] == 11472
    baseline = audit['proof_sha256']
    assert len(baseline) == 1267 and all(PROOF_NAME.fullmatch(n) for n in baseline)
    assert set(audit['project_sha256']) == PROJECT | {AGGREGATE}
    assert preparation['runtime'] == PRIOR and preparation['proof_files'] == 1267
    assets = audit['source_sha256']
    assert len(assets) == 31 and assets == preparation['all31_site_source91_sha256']
    assert all(Path(n).parent == Path('SafeLearning') and Path(n).suffix in {'.html', '.js', '.css'} for n in assets)
    proof_directory = path(PRIOR + '/verification/lean/SafeLearning')
    assert {p.name for p in proof_directory.iterdir()} == {Path(n).name for n in baseline}
    assert all(p.is_file() and not p.is_symlink() for p in proof_directory.iterdir())
    site_directory = path(PRIOR + '/SafeLearning')
    assert {p.name for p in site_directory.iterdir()} == {Path(n).name for n in assets}
    assert all(p.is_file() and not p.is_symlink() for p in site_directory.iterdir())
    support_rows = [r for r in preparation['source_objects'] if r['runtime_file'] == PRIOR + '/' + SUPPORT]
    assert len(support_rows) == 1
    pinned = {**baseline, **audit['project_sha256'], **assets, SUPPORT: support_rows[0]['sha256']}
    inputs = {SELF: ref(SELF)['sha256'], AUDIT: AUDIT_SHA256,
              PRIOR_PREPARATION: PRIOR_PREPARATION_SHA256}
    files = []

    def add(target, source_name, kind, fingerprint=None, raw=None):
        source = ref(source_name) if source_name else None
        content = exact(source) if source else raw
        fingerprint = fingerprint or sha(content)
        assert sha(content) == fingerprint, 'Baseline source differs: ' + str(source_name)
        if source:
            inputs[source_name] = fingerprint
        files.append({'target': target, 'sha256': fingerprint, 'bytes': len(content), 'kind': kind,
                      'source': source, 'object': OBJECTS + '/' + fingerprint[:2] + '/' + fingerprint})

    for name, fingerprint in sorted(pinned.items()):
        if name == AGGREGATE:
            old = ref(PRIOR + '/' + name)
            assert old['sha256'] == fingerprint
            lines = exact(old).decode().splitlines()
            assert len(lines) == 1267 and set(lines) == {line for line in aggregate(baseline).decode().splitlines()}
            inputs[old['file']] = fingerprint
            continue
        kind = 'baseline_proof' if name in baseline else 'site' if name in assets else 'support' if name == SUPPORT else 'project'
        add(name, PRIOR + '/' + name, kind, fingerprint)
    selected = set(baseline)
    for module in ADDITIONS:
        name = 'verification/lean/SafeLearning/' + module + '.lean'
        assert name not in selected
        add(name, name, 'candidate_proof')
        selected.add(name)
    assert len(selected) == 1271
    assert ref(claims_name)['sha256'] == claims_sha256, 'Claim packet differs'
    packet = read(claims_name)
    assert len(packet['candidate_additions']) == 4 and set(packet['candidate_additions']) == set(ADDITIONS)
    assert packet['reader_source']['sha256'] == assets[packet['reader_source']['file']]
    exact(packet['inventory'])
    inputs[packet['inventory']['file']] = packet['inventory']['sha256']
    inputs[claims_name] = claims_sha256
    selected_hashes = {r['target']: r['sha256'] for r in files if r['kind'] in {'baseline_proof', 'candidate_proof'}}
    packet_sources = packet['proof_sources']
    assert len({r['file'] for r in packet_sources}) == len(packet_sources)
    assert {'verification/lean/SafeLearning/' + m + '.lean' for m in ADDITIONS} <= {r['file'] for r in packet_sources}
    for source in packet_sources:
        assert selected_hashes[source['file']] == source['sha256'], 'Packet selects a different proof source'
        exact(source)
        inputs[source['file']] = source['sha256']
    namespace = {}
    exec(compile(exact({'file': PRIOR + '/' + SUPPORT, 'sha256': pinned[SUPPORT]}), SUPPORT, 'exec'), namespace)
    theorem_counts = {}
    for row in files:
        if row['kind'] == 'candidate_proof':
            declarations = namespace['declarations'](exact(row['source']).decode())
            theorem_counts[Path(row['target']).stem] = sum(d['kind'] in {'theorem', 'lemma'} for d in declarations)
    assert theorem_counts[ADDITIONS[-1]] == 11 and sum(theorem_counts.values()) == 36
    add(AGGREGATE, None, 'aggregate', raw=aggregate(selected))
    for name, fingerprint in assets.items():
        inputs[name] = fingerprint
    protect(inputs)
    return {'schema': 'source91.piece01.source-only-runtime.v1',
            'status': 'immutable_source_selection_native_audit_and_correspondence_pending',
            'helper': ref(SELF), 'plan_file': plan_name, 'runtime': RUNTIME,
            'baseline_passing_audit': ref(AUDIT), 'baseline_runtime_preparation': ref(PRIOR_PREPARATION),
            'candidate_claim_packet': ref(claims_name),
            'baseline_proof_count': 1267, 'candidate_additions': list(ADDITIONS), 'proof_count': 1271,
            'candidate_source_public_theorem_counts': theorem_counts,
            'expected_public_theorems_pending_actual_native_audit': 11508,
            'files': sorted(files, key=lambda r: r['target']), 'protected_inputs': inputs,
            'site_source91_sha256': assets, 'runtime_only_cache_links': cache_links(),
            'native_audit_claimed': False, 'correspondence_approval_claimed': False,
            'coverage_complete': False}


def validate_objects(plan):
    for row in plan['files']:
        exact({'file': row['object'], 'sha256': row['sha256'], 'bytes': row['bytes']})
        assert not path(row['object']).stat().st_mode & 0o222, 'Writable source object: ' + row['object']


def make_plan(plan_name, claims_name=CLAIMS, claims_sha256=CLAIMS_SHA256):
    plan = model(plan_name, claims_name, claims_sha256)
    for row in plan['files']:
        raw = exact(row['source']) if row['source'] else aggregate(
            r['target'] for r in plan['files'] if r['kind'] in {'baseline_proof', 'candidate_proof'})
        assert sha(raw) == row['sha256']
        put(row['object'], raw, readonly=True)
    protect(plan['protected_inputs'])
    validate_objects(plan)
    put(plan_name, encode(plan))
    protect(plan['protected_inputs'])
    assert path(plan_name).read_bytes() == encode(plan)
    return plan


def check_native_outputs(plan, completed):
    reports = path(RUNTIME + '/reports')
    if reports.exists():
        assert completed, 'Native outputs precede completed source preparation'
        assert {p.name for p in reports.iterdir()} <= {'lean-verification'}, 'Unexpected native report directory'
        output = path(RUNTIME + '/reports/lean-verification')
        if output.exists():
            assert output.is_dir()
            fixed = {'lean-version.txt', 'build.log', 'axioms.log', 'verification.json',
                     'reused-verification-original.json', 'kernel-progress.json'}
            kernels = {'kernel-SafeLearning-' + Path(r['target']).stem + '.log'
                       for r in plan['files'] if r['kind'] in {'baseline_proof', 'candidate_proof'}}
            for item in output.iterdir():
                temporary = re.fullmatch(r'\.(?:kernel-progress|verification)\.json-[A-Za-z0-9_-]+', item.name)
                assert item.name in fixed | kernels or temporary, 'Unexpected native output: ' + item.name
                assert item.is_file() and not item.is_symlink(), 'Native outputs must be flat regular files'
    lake = path(RUNTIME + '/verification/lean') / '.lake'
    if lake.exists():
        assert lake.is_dir() and not lake.is_symlink()
        assert {p.name for p in lake.iterdir()} <= ({'packages', 'build', 'config'} if completed else {'packages', 'build'})
        config = lake / 'config'
        if config.exists() or config.is_symlink():
            assert completed and config.is_dir() and not config.is_symlink()
            for directory in config.iterdir():
                assert re.fullmatch(r'[0-9]+', directory.name) and directory.is_dir() and not directory.is_symlink()
                for item in directory.iterdir():
                    assert item.name in {'lakefile.olean', 'lakefile.olean.trace'}
                    assert item.is_file() and not item.is_symlink()


def check_runtime(plan, *, complete=False):
    """Bounded immediate listings of the planned source directories only."""
    children = {}
    for row in plan['files']:
        relative = Path(row['target'])
        for parent in [relative.parent, *relative.parent.parents]:
            directory = parent.as_posix()
            child = relative.relative_to(parent).parts[0]
            children.setdefault(directory, set()).add(child)
    completed = path(REPORT).exists()
    check_native_outputs(plan, completed)
    for directory, expected in children.items():
        target = path(RUNTIME + ('' if directory == '.' else '/' + directory))
        if not target.exists():
            assert not complete, 'Missing runtime directory: ' + directory
            continue
        assert target.is_dir()
        allowed = set(expected)
        if directory == '.':
            allowed.add('reports')  # Native verifier output, never a copied input.
        if directory == 'verification/lean':
            allowed.add('.lake')
            if completed:
                allowed.add('AxiomAudit.lean')  # Generated by the separate native audit.
        entries = {p.name: p for p in target.iterdir()}
        assert entries.keys() <= allowed, 'Unexpected runtime entry: ' + directory
        if complete:
            assert expected <= entries.keys(), 'Incomplete runtime source directory: ' + directory
        for name, entry in entries.items():
            assert not entry.is_symlink(), 'Unexpected runtime symlink: ' + str(entry)
            if name in expected:
                child_directory = (Path(directory) / name).as_posix()
                assert entry.is_dir() if child_directory in children else entry.is_file()
    for row in plan['files']:
        name = RUNTIME + '/' + row['target']
        if path(name).exists():
            exact({'file': name, 'sha256': row['sha256'], 'bytes': row['bytes']})
            assert path(name).samefile(path(row['object'])), 'Runtime source is not its planned object: ' + name
            assert not path(name).stat().st_mode & 0o222, 'Writable runtime source: ' + name
        else:
            assert not complete, 'Missing runtime source: ' + row['target']


def install_links(plan, *, create=False):
    assert cache_links() == plan['runtime_only_cache_links'], 'Original cache links changed'
    project = path(RUNTIME + '/verification/lean')
    lake = project / '.lake'
    if not lake.exists():
        if not create:
            return
        lake.mkdir()
    assert lake.is_dir() and not lake.is_symlink()
    if not path(REPORT).exists():
        assert {p.name for p in lake.iterdir()} <= {'packages', 'build'}
    for part, link in plan['runtime_only_cache_links'].items():
        target = lake / part
        expected = Path(link['resolved_target'])
        if not target.exists() and not target.is_symlink():
            if not create:
                continue
            target.symlink_to(expected, target_is_directory=True)
            fsync_directory(lake)
        assert target.is_symlink() and target.resolve() == expected and target.is_dir(), 'Runtime cache differs: ' + part


def link_source(row):
    """Link one verified object; never replace a prior runtime file."""
    if row['source']:
        exact(row['source'])
    exact({'file': row['object'], 'sha256': row['sha256'], 'bytes': row['bytes']})
    assert not path(row['object']).stat().st_mode & 0o222, 'Writable source object: ' + row['object']
    name = RUNTIME + '/' + row['target']
    target = path(name)
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        try:
            os.link(path(row['object']), target)
        except FileExistsError:
            pass  # Verify a competing exact link below; never overwrite it.
        fsync_directory(target.parent)
    exact({'file': name, 'sha256': row['sha256'], 'bytes': row['bytes']})
    assert target.samefile(path(row['object'])), 'Runtime source is not its planned object: ' + name
    assert not target.stat().st_mode & 0o222, 'Writable runtime source: ' + name


def apply(plan_name, fingerprint):
    assert ref(plan_name)['sha256'] == fingerprint, 'Plan SHA differs'
    plan = read(plan_name)
    assert plan == model(plan_name, plan['candidate_claim_packet']['file'], plan['candidate_claim_packet']['sha256']), 'Plan no longer matches the exact selection'
    validate_objects(plan)
    check_runtime(plan)
    install_links(plan)
    reused = path(REPORT).exists()
    for row in plan['files']:
        link_source(row)
    install_links(plan, create=True)
    protect(plan['protected_inputs'])
    validate_objects(plan)
    check_runtime(plan, complete=True)
    assert cache_links() == plan['runtime_only_cache_links']
    assert ref(plan_name)['sha256'] == fingerprint, 'Plan edited during preparation'
    result = {'status': 'source_only_source91_piece01_runtime_prepared_native_audit_and_correspondence_pending',
              'helper': ref(SELF), 'plan': ref(plan_name), 'runtime': RUNTIME,
              'baseline_passing_audit': plan['baseline_passing_audit'],
              'baseline_proof_files': 1267, 'candidate_proof_files': 4, 'proof_files': 1271,
              'aggregate_import_count': 1271, 'candidate_additions': list(ADDITIONS),
              'candidate_claim_packet': plan['candidate_claim_packet'],
              'candidate_source_public_theorem_counts': plan['candidate_source_public_theorem_counts'],
              'expected_public_theorems_pending_actual_native_audit': 11508,
              'runtime_source_sha256': {r['target']: r['sha256'] for r in plan['files']},
              'all31_source91_assets_unchanged': True,
              'immutable_source_object_hardlinks': True, 'source_byte_copies_into_runtime': 0,
              'copied_cache_or_archive_trees': 0, 'runtime_only_cache_links': plan['runtime_only_cache_links'],
              'unselected_working_proof_files_copied': 0, 'native_aggregate_audit_claimed': False,
              'source_correspondence_approval_claimed': False, 'coverage_complete': False}
    put(REPORT, encode(result))
    protect(plan['protected_inputs'])
    check_runtime(plan, complete=True)
    assert path(REPORT).read_bytes() == encode(result)
    return result, reused


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    phase = parser.add_mutually_exclusive_group(required=True)
    phase.add_argument('--plan', action='store_true', help='Snapshot sources and write the immutable plan; do not stage the runtime')
    phase.add_argument('--apply', action='store_true', help='Validate and stage/resume the exact planned runtime')
    parser.add_argument('--plan-file', default=PLAN)
    parser.add_argument('--plan-sha256')
    parser.add_argument('--claims', default=CLAIMS, help='Exact candidate correspondence packet to bind, without approving it')
    parser.add_argument('--claims-sha256', default=CLAIMS_SHA256)
    args = parser.parse_args()
    assert Path(args.plan_file).parent.as_posix() == PIECE and re.fullmatch(r'runtime-plan-[A-Za-z0-9_-]+\.json', Path(args.plan_file).name)
    assert Path(args.claims).parent.as_posix() == PIECE and re.fullmatch(r'claims-[A-Za-z0-9_-]+\.json', Path(args.claims).name)
    assert re.fullmatch(r'[0-9a-f]{64}', args.claims_sha256)
    assert args.plan_sha256 if args.apply else args.plan_sha256 is None
    lock_path = path(PIECE + '/runtime-preparation.lock')
    with lock_path.open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if args.plan:
            value = make_plan(args.plan_file, args.claims, args.claims_sha256)
            print(json.dumps({'status': value['status'], 'plan': ref(args.plan_file), 'proof_files': 1271,
                              'runtime_staged': False}))
        else:
            value, reused = apply(args.plan_file, args.plan_sha256)
            print(json.dumps({'status': value['status'], 'report': ref(REPORT), 'proof_files': 1271, 'reused': reused}))


if __name__ == '__main__':
    main()

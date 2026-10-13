"""Prepare the reviewed checkpoint35 selection and a resumable source-only runtime.

Completed native compiler receipts and independent source reviews are required.
Each copied object and stage receipt is installed atomically. Existing exact
objects are accepted on reruns; different bytes are rejected. Historical trees
and build artifacts are never copied.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import importlib.util
import json
import os
import re
import tempfile

ROOT = Path(__file__).resolve().parents[4]
BASE = 'reports/full-coverage/checkpoint-34-selection.json'
AUDIT = 'reports/full-coverage/lean-checkpoint-34-source90-v1/verification-original.json'
SELECTION = 'reports/full-coverage/checkpoint-35-selection.json'
RUNTIME = 'reports/full-coverage/runtime-checkpoint-35-source90-v1'
OUT = 'reports/full-coverage/checkpoint35-runtime-preparation-v1.json'


def path(name):
    p = Path(name)
    assert name and not p.is_absolute() and p.as_posix() == name
    assert not {'..', '.git', '.lake'}.intersection(p.parts)
    p = ROOT / p
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(ROOT))
    return p


def sha(name):
    with path(name).open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def ref(name):
    return {'file': name, 'sha256': sha(name)}


def read(name):
    return json.loads(path(name).read_bytes())


def exact(row):
    assert sha(row['file']) == row['sha256'], row['file']
    return path(row['file'])


def encode(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()


def put(name, data):
    p = path(name)
    if p.exists():
        assert p.read_bytes() == data, name
        return
    p.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix='.' + p.name + '-', dir=p.parent)
    try:
        with os.fdopen(fd, 'wb') as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.replace(temporary, p)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def check_compiler(receipt, source, kind):
    d = json.loads(exact(receipt).read_bytes())
    assert d['status'] == 'passed' and d['actual_exit_code'] == 0
    before = d.get('input_sha256_before', d.get('helper_sha256_before', {}))
    after = d.get('input_sha256_after', d.get('helper_sha256_after', {}))
    assert before == after and before[source['file']] == source['sha256']
    assert sha(d['log']) == d['log_sha256']
    project = ROOT / 'verification/lean'
    cwd = Path(d['actual_workdir'])
    command = d['actual_command']
    assert Path(command[0]).name == 'lake'
    assert cwd in {ROOT, project}
    if cwd == ROOT:
        assert command[1:3] == ['--dir', 'verification/lean']
        command = [command[0]] + command[3:]
    if kind == 'standalone':
        assert command[1:3] == ['env', 'lean'] and len(command) == 4
        assert (cwd / command[3]).resolve() == exact(source)
    else:
        assert command[1:] == ['build', 'SafeLearning.' + Path(source['file']).stem]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', required=True)
    parser.add_argument('--plan-sha256', required=True)
    args = parser.parse_args()
    exact({'file': args.plan, 'sha256': args.plan_sha256})
    plan = read(args.plan)
    assert plan['status'] == 'passed_reviewed_compiled_additions_ready_for_selection'
    assert plan['baseline_selection'] == ref(BASE)
    assert plan['baseline_audit'] == ref(AUDIT)
    assert plan['inventory'] == ref('book/coverage/inventory.json')
    base, prior = read(BASE), read(AUDIT)
    assert prior['status'] == 'passed' and prior['proof_file_count'] == 1264
    assert prior['theorem_count'] == 11459
    assert prior['proof_sha256'] == {n: r['sha256'] for n, r in base['proof_files'].items()}
    spec = importlib.util.spec_from_file_location('checkpoint35_names', path('book/coverage/lean_names.py'))
    names = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(names)
    selected = {n: {'sha256': r['sha256'], 'original_checkpoint34_metadata': {
        **ref(BASE), 'JSON_pointer': ['proof_files', n]}} for n, r in base['proof_files'].items()}
    public = set()
    for n, r in selected.items():
        exact({'file': n, 'sha256': r['sha256']})
        public.update(d['name'] for d in names.declarations(path(n).read_text()))
    count = 0
    for row in plan['sources']:
        source = row['source']
        p = exact(source)
        assert p.parent == ROOT / 'verification/lean/SafeLearning' and p.suffix == '.lean'
        assert source['file'] not in selected
        declarations = names.declarations(p.read_text())
        found = {d['name'] for d in declarations}
        assert len(found) == len(declarations) and not found.intersection(public)
        public.update(found)
        assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b', names.without_comments(p.read_text()))
        theorem_count = sum(d['kind'] in {'theorem', 'lemma'} for d in declarations)
        assert theorem_count == row['public_theorem_count']
        count += theorem_count
        for kind in ['standalone', 'named']:
            check_compiler(row[kind], source, kind)
        assert row['independent_source_reviews']
        for review in row['independent_source_reviews']:
            peer = json.loads(exact(review).read_bytes())
            assert peer['status'].startswith(('passed', 'approved')) and peer['errors'] == []
            assert any(r['file'] == source['file'] and r['sha256'] == source['sha256']
                       for r in peer['proof_sources'])
            exact(peer['inventory'])
            assert peer['inventory']['sha256'] == plan['inventory']['sha256']
        selected[source['file']] = {
            'sha256': source['sha256'], 'public_theorem_count': theorem_count,
            'actual_standalone': row['standalone'], 'actual_named': row['named'],
            'independent_source_reviews': row['independent_source_reviews']}
    assert len(plan['sources']) == 3 and count == 13 and len(selected) == 1267
    files = {n: r['sha256'] for n, r in selected.items()}
    files.update(prior['source_sha256'])
    for n in ['book/coverage/lean_names.py', 'verification/lean/lean-toolchain',
              'verification/lean/lakefile.toml', 'verification/lean/lake-manifest.json',
              'verification/lean/verify.py']:
        files[n] = sha(n)
    protected = {**files, BASE: sha(BASE), AUDIT: sha(AUDIT), args.plan: args.plan_sha256,
                 'book/coverage/inventory.json': plan['inventory']['sha256']}
    for n, h in protected.items():
        assert sha(n) == h, n
    object_refs = {}
    for n, h in sorted(files.items()):
        object_name = 'reports/full-coverage/source-objects/' + h[:2] + '/' + h
        put(object_name, path(n).read_bytes())
        path(object_name).chmod(0o444)
        destination = path(RUNTIME + '/' + n)
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists():
            os.link(path(object_name), destination)
        assert sha(RUNTIME + '/' + n) == h
        object_refs[n] = {'file': object_name, 'sha256': h}
    aggregate = ('\n'.join('import SafeLearning.' + Path(n).stem for n in sorted(selected)) + '\n').encode()
    put(RUNTIME + '/verification/lean/SafeLearning.lean', aggregate)
    lake = path(RUNTIME) / 'verification/lean/.lake'
    lake.mkdir(exist_ok=True)
    for part in ['packages', 'build']:
        original = ROOT / 'verification/lean/.lake' / part
        assert original.is_dir()
        target = lake / part
        if not target.exists():
            target.symlink_to(original, target_is_directory=True)
        assert target.is_symlink() and target.resolve() == original.resolve()
    selection = {
        'status': 'actual_compiled_reviewed_checkpoint35_selection_aggregate_pending',
        'baseline_selection': ref(BASE), 'baseline_actual_passing_audit': ref(AUDIT),
        'additions_plan': ref(args.plan), 'proof_files': selected,
        'proof_file_count': 1267, 'new_file_count': 3,
        'expected_public_theorem_count_pending_actual_aggregate': 11472,
        'coverage_complete': False, 'aggregate_kernel_axiom_or_whole_coverage_claimed': False}
    put(SELECTION, encode(selection))
    result = {
        'status': 'source_only_checkpoint35_runtime_prepared_audit_pending',
        'runtime': RUNTIME, 'selection': ref(SELECTION), 'plan': ref(args.plan),
        'source_hashes': {**files, 'verification/lean/SafeLearning.lean': hashlib.sha256(aggregate).hexdigest()},
        'selected_source_count': 1267, 'new_sources': 3, 'new_theorems': 13,
        'inventory': plan['inventory'], 'all31_site_assets_identical_to_checkpoint34': True,
        'copied_lake_build_artifact_count': 0, 'copied_earlier_snapshot_tree_count': 0,
        'package_and_build_cache_symlinks_are_runtime_only': True,
        'immutable_source_object_hardlinks': object_refs, 'source_byte_copies_into_runtime': 0,
        'coverage_complete': False}
    put(OUT, encode(result))
    for n, h in protected.items():
        assert sha(n) == h, n
    print(json.dumps({'status': result['status'], 'runtime': RUNTIME,
                      'proof_files': 1267, 'new_theorems': 13, 'record': ref(OUT)}))


if __name__ == '__main__':
    main()

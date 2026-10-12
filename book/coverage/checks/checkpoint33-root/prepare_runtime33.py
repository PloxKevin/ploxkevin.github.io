"""Select exact compiled additions and prepare a source-only Lean runtime.

The plan contains canonical source references and genuine standalone/named
compiler records. Earlier selection metadata stays in its original file;
the new selection identifies it by hash and JSON pointer.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import importlib.util
import json
import re

ROOT = Path(__file__).resolve().parents[4]
BASE = 'reports/full-coverage/checkpoint-32-selection.json'
BASE_AUDIT = 'reports/full-coverage/lean-checkpoint-32-source81-recovery-v1/verification-original.json'
OUT = 'reports/full-coverage/checkpoint-33-selection.json'
RUNTIME = 'reports/full-coverage/runtime-checkpoint-33-source88-v1'
RECORD = 'reports/full-coverage/checkpoint33-runtime-source88-preparation-v1.json'


def path(n):
    assert isinstance(n, str) and n and Path(n).as_posix() == n
    assert not Path(n).is_absolute() and not {'..', '.git', '.lake'}.intersection(Path(n).parts)
    p = ROOT / n
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(ROOT))
    return p


def sha(n):
    return hashlib.sha256(path(n).read_bytes()).hexdigest()


def read(n):
    return json.loads(path(n).read_bytes())


def ref(n):
    return dict(file=n, sha256=sha(n))


def exact(r):
    assert sha(r['file']) == r['sha256'], r['file']
    return path(r['file'])


def contains_hash(d, h):
    if isinstance(d, dict):
        return any(contains_hash(v, h) for v in d.values())
    if isinstance(d, list):
        return any(contains_hash(v, h) for v in d)
    return d == h


def write(n, data):
    p = path(n)
    assert not p.exists()
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f:
        f.write(data)


ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--plan', required=True)
ap.add_argument('--plan-sha256', required=True)
args = ap.parse_args()
exact(dict(file=args.plan, sha256=args.plan_sha256))
plan = read(args.plan)
assert plan['status'] == 'passed_reviewed_compiled_additions_ready_for_selection'
assert not path(OUT).exists() and not path(RUNTIME).exists() and not path(RECORD).exists()
base, previous = read(BASE), read(BASE_AUDIT)
assert previous['status'] == 'passed' and previous['proof_file_count'] == 1254 and previous['theorem_count'] == 11267
assert previous['proof_sha256'] == {n: r['sha256'] for n, r in base['proof_files'].items()}
selected = {n: dict(sha256=r['sha256'], original_checkpoint32_metadata=dict(**ref(BASE), JSON_pointer=['proof_files', n])) for n, r in base['proof_files'].items()}
spec = importlib.util.spec_from_file_location('checkpoint33_names', path('book/coverage/lean_names.py'))
names = importlib.util.module_from_spec(spec)
spec.loader.exec_module(names)
public = set()
for n, row in selected.items():
    exact(dict(file=n, sha256=row['sha256']))
    public.update(d['name'] for d in names.declarations(path(n).read_text()))
new_count = 0
for row in plan['sources']:
    source = row['source']
    p = exact(source)
    assert p.parent == ROOT / 'verification/lean/SafeLearning' and p.suffix == '.lean'
    n = source['file']
    assert n not in selected
    declarations = names.declarations(p.read_text())
    found = {d['name'] for d in declarations}
    assert len(found) == len(declarations) and not found.intersection(public)
    public.update(found)
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b', names.without_comments(p.read_text()))
    count = sum(d['kind'] in {'theorem', 'lemma'} for d in declarations)
    assert count == row['public_theorem_count']
    new_count += count
    for kind in ['standalone', 'named']:
        receipt = row[kind]
        d = json.loads(exact(receipt).read_bytes())
        codes = [d[k] for k in ['exit_code', 'actual_exit_code'] if k in d]
        assert d['status'] == 'passed' and codes and all(type(c) is int and c == 0 for c in codes)
        recorded_source = d['source']['file'] if isinstance(d['source'], dict) else d['source']
        assert recorded_source == n and d['source_sha256_before'] == d['source_sha256_after'] == source['sha256']
        expected = ['lake', 'env', 'lean', 'SafeLearning/' + p.name] if kind == 'standalone' else ['lake', 'build', 'SafeLearning.' + p.stem]
        assert d['command'] == expected and d['actual_workdir'] == str(ROOT / 'verification/lean')
        if isinstance(d.get('raw_log'), dict):
            exact(d['raw_log'])
        else:
            assert sha(d['log']) == d['log_sha256']
    assert row['independent_source_reviews']
    for r in row['independent_source_reviews']:
        peer = json.loads(exact(r).read_bytes())
        assert peer['status'].startswith('passed') and peer.get('errors', []) == [] and peer.get('protection_errors', []) == []
        assert contains_hash(peer, source['sha256']), 'Independent peer does not identify these source bytes'
    selected[n] = dict(sha256=source['sha256'], public_theorem_count=count,
                       actual_standalone=row['standalone'], actual_named=row['named'],
                       independent_source_reviews=row['independent_source_reviews'])
assert len(selected) == 1254 + len(plan['sources'])
inventory = read('book/coverage/inventory.json')
assert sha('book/coverage/inventory.json') == plan['inventory']['sha256'] == '87b8457614b7a9a127c171e1a95adf43bd94d05de6d63921b5e69493e3822202'
exact(plan['source_application'])
application = read(plan['source_application']['file'])
assert application['status'].startswith('passed') and application['exercises_changed'] == 0
exact(plan['independent_actual_source_application_review'])
assert read(plan['independent_actual_source_application_review']['file'])['status'].startswith('passed')
files = {n: r['sha256'] for n, r in selected.items()}
files.update(inventory['source_sha256'])
for n in ['SafeLearning/components.js', 'SafeLearning/style.css', 'book/coverage/lean_names.py', 'verification/lean/lean-toolchain', 'verification/lean/lakefile.toml', 'verification/lean/lake-manifest.json', 'verification/lean/verify.py']:
    files[n] = sha(n)
protected = {**files, BASE: sha(BASE), BASE_AUDIT: sha(BASE_AUDIT), args.plan: args.plan_sha256, 'book/coverage/inventory.json': sha('book/coverage/inventory.json')}
current_site = {n: h for n, h in files.items() if n.startswith('SafeLearning/')}
assert set(current_site) == set(previous['source_sha256'])
changed_pages = {'SafeLearning/primer-basics.html', 'SafeLearning/primer-linalg.html'}
assert {n for n in current_site if current_site[n] != previous['source_sha256'][n]} == changed_pages
assert all(current_site[n] == sha(n) for n in changed_pages)
for n in changed_pages:
    assert any(a['source'] == n and a['after_sha256'] == current_site[n] for a in application['applications'])
assert all(sha(n) == h for n, h in protected.items())
for n, h in files.items():
    write(RUNTIME + '/' + n, path(n).read_bytes())
    assert sha(RUNTIME + '/' + n) == h
aggregate = ('\n'.join('import SafeLearning.' + Path(n).stem for n in sorted(selected)) + '\n').encode()
write(RUNTIME + '/verification/lean/SafeLearning.lean', aggregate)
lake = path(RUNTIME) / 'verification/lean/.lake'
lake.mkdir()
for part in ['packages', 'build']:
    original = ROOT / 'verification/lean/.lake' / part
    assert original.is_dir()
    (lake / part).symlink_to(original, target_is_directory=True)
assert all(sha(n) == h for n, h in protected.items())
selection = dict(status='actual_compiled_reviewed_checkpoint33_selection_aggregate_pending',
                 created_at_utc=datetime.now(timezone.utc).isoformat(), baseline_selection=ref(BASE),
                 baseline_actual_passing_audit=ref(BASE_AUDIT), additions_plan=ref(args.plan),
                 proof_files=selected, proof_file_count=len(selected), new_file_count=len(plan['sources']),
                 expected_public_theorem_count_pending_actual_aggregate=11267 + new_count,
                 coverage_complete=False, aggregate_kernel_axiom_or_whole_coverage_claimed=False)
write(OUT, (json.dumps(selection, indent=2) + '\n').encode())
record = dict(status='source_only_checkpoint33_runtime_prepared_audit_pending', runtime=RUNTIME,
              selection=ref(OUT), source_hashes={**files, 'verification/lean/SafeLearning.lean': hashlib.sha256(aggregate).hexdigest()},
              selected_source_count=len(selected), new_sources=len(plan['sources']), new_theorems=new_count,
              unchanged_site_assets_from_actual_checkpoint32=29, changed_site_pages_reviewed_source88=sorted(changed_pages),
              source_application=plan['source_application'], inventory=plan['inventory'],
              copied_lake_build_artifact_count=0, copied_earlier_snapshot_tree_count=0,
              package_and_build_cache_symlinks_are_runtime_only=True, coverage_complete=False)
write(RECORD, (json.dumps(record, indent=2) + '\n').encode())
print(json.dumps(dict(status=record['status'], proof_files=len(selected), new_theorems=new_count, runtime=RUNTIME, selection=ref(OUT))))

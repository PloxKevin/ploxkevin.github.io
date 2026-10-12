"""Prepare a source-only runtime for an actual selected checkpoint30 audit.

Runtime dependency/cache symlinks borrow the local installation. No .lake
build output or earlier snapshot tree is copied into a new checkpoint.
The normal build, kernel replay and axiom audit remain separate executions.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, re

ROOT = Path(__file__).resolve().parents[3]
RUNTIME = ROOT / 'reports/full-coverage/runtime-checkpoint-30'
RESULT = ROOT / 'reports/full-coverage/checkpoint30-runtime-preparation-v1.json'
SELECTION = 'reports/full-coverage/checkpoint-30-selection.json'
OLD_SELECTION = 'reports/full-coverage/checkpoint-29-selection.json'
OLD_SELECTION_SHA = 'ad4eb2940daa6f89dfb52390abc26c8bedb00dae7f97534957f5a4e87ac0d8a9'
INVENTORY_SHA = '9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def safe(n):
    assert type(n) is str and n and not Path(n).is_absolute()
    assert Path(n).as_posix() == n and '..' not in Path(n).parts and '.lake' not in Path(n).parts
    p = ROOT / n
    assert p.is_file() and not p.is_symlink() and p.resolve().is_relative_to(ROOT)
    return p


def output_path(p):
    assert p.is_absolute() and p.resolve().is_relative_to(ROOT.resolve())
    assert not p.is_symlink()
    for parent in [p, *p.parents]:
        if parent.is_relative_to(ROOT):
            assert not parent.is_symlink()
            if parent != p and parent.exists():
                assert parent.is_dir()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--selection-sha256', required=True)
    args = parser.parse_args()
    assert re.fullmatch('[0-9a-f]{64}', args.selection_sha256)
    output_path(RUNTIME)
    output_path(RESULT)
    assert not RUNTIME.exists() and not RESULT.exists()
    assert sha(safe(SELECTION)) == args.selection_sha256
    assert sha(safe(OLD_SELECTION)) == OLD_SELECTION_SHA
    selected = json.loads(safe(SELECTION).read_bytes())
    old = json.loads(safe(OLD_SELECTION).read_bytes())
    assert selected['proof_file_count'] == len(selected['proof_files']) == 1242
    assert selected['new_file_count'] == 45
    assert len(old['proof_files']) == 1197
    assert all(selected['proof_files'][n]['sha256'] == r['sha256'] for n, r in old['proof_files'].items())
    inventory = safe('book/coverage/inventory.json')
    assert sha(inventory) == INVENTORY_SHA
    source_hashes = json.loads(inventory.read_bytes())['source_sha256']
    assert len(source_hashes) == 29
    files = {n: r['sha256'] for n, r in selected['proof_files'].items()}
    assert all(Path(n).parent == Path('verification/lean/SafeLearning') and n.endswith('.lean') for n in files)
    files.update(source_hashes)
    for n in ['SafeLearning/style.css', 'SafeLearning/components.js', 'book/coverage/lean_names.py',
              'verification/lean/lean-toolchain', 'verification/lean/lakefile.toml',
              'verification/lean/lake-manifest.json', 'verification/lean/verify.py']:
        files[n] = sha(safe(n))
    aggregate_name = 'verification/lean/SafeLearning.lean'
    aggregate = ('\n'.join('import SafeLearning.' + Path(n).stem for n in sorted(selected['proof_files'])) + '\n').encode()
    assert aggregate_name not in files
    for n, h in files.items():
        assert sha(safe(n)) == h, n
    packages = ROOT / 'verification/lean/.lake/packages'
    cache = ROOT / 'verification/lean/.lake/build'
    assert packages.is_dir() and cache.is_dir()
    # Every source identity/collision check precedes the first runtime write.
    for n, h in files.items():
        target = RUNTIME / n
        output_path(target)
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as f:
            f.write(safe(n).read_bytes())
        assert sha(target) == h
    output_path(RUNTIME / aggregate_name)
    with (RUNTIME / aggregate_name).open('xb') as f:
        f.write(aggregate)
    lake = RUNTIME / 'verification/lean/.lake'
    lake.mkdir()
    (lake / 'packages').symlink_to(packages, target_is_directory=True)
    (lake / 'build').symlink_to(cache, target_is_directory=True)
    assert all(sha(safe(n)) == h for n, h in files.items())
    assert sha(safe(SELECTION)) == args.selection_sha256
    assert sha(safe(OLD_SELECTION)) == OLD_SELECTION_SHA
    assert sha(inventory) == INVENTORY_SHA
    runtime_hashes = {**files, aggregate_name: hashlib.sha256(aggregate).hexdigest()}
    assert all(sha(RUNTIME / n) == h for n, h in runtime_hashes.items())
    record = {'status': 'source_only_checkpoint30_runtime_prepared_audit_not_yet_run',
              'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
              'runtime': RUNTIME.relative_to(ROOT).as_posix(),
              'selection': {'file': SELECTION, 'sha256': args.selection_sha256},
              'baseline_selection29_before_and_after': {'file': OLD_SELECTION, 'sha256': OLD_SELECTION_SHA},
              'source79_inventory_before_and_after': {'file': 'book/coverage/inventory.json', 'sha256': INVENTORY_SHA},
              'source_hashes': runtime_hashes, 'selected_source_count': 1242,
              'site_asset_count': 31, 'copied_lake_build_artifact_count': 0,
              'copied_earlier_snapshot_tree_count': 0,
              'external_local_packages_symlink': str(packages), 'external_local_build_cache_symlink': str(cache),
              'cache_use_requires_actual_normal_build': True, 'coverage_complete': False,
              'kernel_or_axiom_or_aggregate_success_claimed': False}
    output_path(RESULT)
    with RESULT.open('x') as f:
        f.write(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'status': record['status'], 'runtime': record['runtime'],
                      'record': RESULT.relative_to(ROOT).as_posix(), 'record_sha256': sha(RESULT),
                      'selected_sources': 1242, 'copied_lake_build_artifacts': 0, 'coverage_complete': False}))


if __name__ == '__main__':
    main()

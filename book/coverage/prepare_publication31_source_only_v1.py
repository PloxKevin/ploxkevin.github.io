"""Prepare explicit checkpoint31 Git inputs without recursive archive copies.

This reads the successful source-only manifest and a pinned supplemental file
map, copies exact bytes into the clean publication repo, and records a staging
whitelist. It does not stage, commit, push, or claim successful delivery.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, re, shutil, subprocess

ROOT = Path(__file__).resolve().parents[2]
PUB = ROOT / 'reports/book/publication-repo'
BASELINE = '676db1f7d13ddbf65c2f0253d1fab79c44948a7e'
RESULT = 'reports/full-coverage/publication31-prepared-exact-files-v1.json'


def safe(root, n):
    assert type(n) is str and n and Path(n).as_posix() == n
    assert not Path(n).is_absolute() and '..' not in Path(n).parts and '.git' not in Path(n).parts
    assert not any(c in n for c in '\0\n\r')
    p = root / n
    assert p.resolve().is_relative_to(root) and not p.is_symlink()
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(root))
    return p


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def git(args):
    return subprocess.run(['git', *args], cwd=PUB, capture_output=True, check=True).stdout


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--supplements', required=True)
    ap.add_argument('--supplements-sha256', required=True)
    args = ap.parse_args()
    assert git(['rev-parse', 'HEAD']).decode().strip() == BASELINE
    assert not git(['status', '--porcelain', '-z', '--untracked-files=all'])
    index_path = (PUB / git(['rev-parse', '--git-path', 'index']).decode().strip()).resolve()
    assert index_path.is_relative_to(PUB / '.git') and index_path.is_file()
    original_index_sha256 = sha(index_path)
    assert not safe(ROOT, RESULT).exists() and not safe(PUB, RESULT).exists()
    manifest_name = 'reports/full-coverage/checkpoint-31-manifest.json'
    mp = safe(ROOT, manifest_name)
    assert sha(mp) == args.manifest_sha256
    manifest = json.loads(mp.read_bytes())
    assert manifest['status'] == 'formal_verification_passed_partial_coverage'
    assert manifest['coverage_complete'] is False and manifest['source_only_snapshot'] is True
    assert manifest['old_snapshot_or_lake_tree_copied'] is False
    assert len(manifest['proof_files']) == 1248
    audit_ref = manifest['successful_verification']
    audit_path = safe(ROOT, audit_ref['report'])
    assert sha(audit_path) == audit_ref['report_sha256']
    audit = json.loads(audit_path.read_bytes())
    assert audit['status'] == 'passed' and audit['proof_file_count'] == 1248 and audit['theorem_count'] == 11184
    assert len(audit['checks']) == 1251 and all(c['exit_code'] == 0 for c in audit['checks'])
    assert all(set(a) <= {'Classical.choice', 'propext', 'Quot.sound'} for a in audit['axiom_dependencies'].values())
    assert audit['proof_sha256'] == {n: r['sha256'] for n, r in manifest['proof_files'].items()}
    supplement_path = safe(ROOT, args.supplements)
    assert sha(supplement_path) == args.supplements_sha256
    supplement = json.loads(supplement_path.read_bytes())
    assert supplement['status'] == 'explicit_source31_publication_supplement_paths_and_existing_historical_references'
    snapshot = safe(ROOT, manifest['snapshot'])
    planned = {n: {'source': snapshot / n, 'sha256': h} for n, h in manifest['frozen_inputs_sha256'].items()}
    for n, h in supplement['copy_root_paths_sha256'].items():
        assert n not in planned or planned[n]['sha256'] == h
        planned[n] = {'source': safe(ROOT, n), 'sha256': h}
    planned[manifest_name] = {'source': mp, 'sha256': args.manifest_sha256}
    planned[args.supplements] = {'source': supplement_path, 'sha256': args.supplements_sha256}
    existing = supplement['unchanged_existing_publication_paths_sha256']
    for n, h in existing.items():
        assert sha(safe(PUB, n)) == h and n not in planned
    assets = {n: h for n, h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
    assert len(assets) == 31 and all(audit['source_sha256'][n] == h for n, h in assets.items())
    for n, r in planned.items():
        assert '.lake' not in Path(n).parts and '__pycache__' not in Path(n).parts
        assert not any(re.fullmatch(r'checkpoint-\d+', part) for part in Path(n).parts[:-1])
        assert r['source'].is_file() and not r['source'].is_symlink()
        assert sha(r['source']) == r['sha256'] and r['source'].stat().st_size < 100000000
        safe(PUB, n)
    copied = []
    for n, r in sorted(planned.items()):
        target = safe(PUB, n)
        if target.is_file() and sha(target) == r['sha256']:
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(r['source'], target)
        assert sha(target) == r['sha256']
        copied.append(n)
    expected = {n: r['sha256'] for n, r in planned.items()}
    assert expected == {n: sha(safe(PUB, n)) for n in expected}
    assert expected == {n: sha(r['source']) for n, r in planned.items()}
    assert existing == {n: sha(safe(PUB, n)) for n in existing}
    assert git(['rev-parse', 'HEAD']).decode().strip() == BASELINE
    assert sha(index_path) == original_index_sha256
    result = {'publication_index_sha256_before_and_after': original_index_sha256, 'status': 'exact_checkpoint31_publication_inputs_prepared_awaiting_staging_and_delivery',
              'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'baseline_publication_head': BASELINE,
              'manifest': {'file': manifest_name, 'sha256': args.manifest_sha256},
              'supplements': {'file': args.supplements, 'sha256': args.supplements_sha256},
              'expected_publication_paths_sha256': expected, 'actual_copied_paths': copied,
              'unchanged_existing_publication_paths_sha256': existing,
              'no_snapshot_tree_or_lake_build_output_copied': True, 'coverage_complete': False,
              'commit_push_Pages_or_live_success_claimed': False}
    safe(ROOT, RESULT).write_text(json.dumps(result, indent=2) + '\n')
    shutil.copyfile(safe(ROOT, RESULT), safe(PUB, RESULT))
    print(json.dumps({'status': result['status'], 'planned_files': len(expected), 'copied_files': len(copied),
                      'historical_existing_files_verified': len(existing), 'coverage_complete': False}))


if __name__ == '__main__':
    main()

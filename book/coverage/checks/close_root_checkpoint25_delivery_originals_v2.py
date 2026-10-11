"""Preserve completed25 delivery bytes before source53 or owner26 integration."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess

ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / 'reports/full-coverage'
BASE = ROOT / 'book/coverage/checks/future26-core/closed-checkpoint25-delivery-originals-v2'
OUT = BASE / 'closed-original-byte-aliases-v1.json'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(p):
    return json.loads(p.read_text())


def main():
    assert not BASE.exists()
    predecessor_path = ROOT / 'book/coverage/checks/future26-core/closed-checkpoint25-delivery-originals-v1/closed-original-byte-aliases-v1.json'
    predecessor = read(predecessor_path)
    prior = {r['original']['file']: r['immutable_original_byte_copy'] for r in predecessor['aliases']}
    active_stem = 'close-checkpoint25-delivery-originals-execution-v2'
    old_log = 'reports/full-coverage/close-checkpoint25-delivery-originals-execution-v1.log'
    old_running = prior[old_log]
    assert old_running['sha256'] == sha(ROOT / old_running['file']) == hashlib.sha256(b'').hexdigest()
    assert sha(ROOT / old_log) != old_running['sha256']
    assert all(sha(ROOT / r['original']['file']) == r['original']['sha256']
               for r in predecessor['aliases'] if r['original']['file'] != old_log)
    commits = {}
    for attempt in [1, 2]:
        live = read(REPORTS / f'live-checkpoint-25-attempt{attempt}.json')
        pages = read(REPORTS / f'pages-checkpoint-25-attempt{attempt}.json')
        assert live['status'] == 'passed_all31_asset_sha256' and len(live['assets']) == 31
        assert live['commit'] == live['remote_main'] == pages['commit'] == pages['expected_commit']
        assert pages['status'] == 'passed'
        commits[attempt] = live['commit']
        actual = read(REPORTS / f'live25-attempt{attempt}-execution-v1.json')
        assert type(actual['actual_exit_code']) is int and actual['actual_exit_code'] == 0
        assert sha(ROOT / actual['log']) == actual['log_sha256']
    assert subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT / 'reports/book/publication-repo',
                          check=True, capture_output=True).stdout.decode().strip() == commits[2]
    progress = read(ROOT / 'book/coverage/progress.json')
    assert progress['publication_status'] == 'checkpoint25_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial'
    assert progress['last_published_content_commit'] == commits[1]
    assert progress['verified_checkpoint']['proof_files'] == 1156
    assert progress['verified_checkpoint']['theorems'] == 9369
    manifest = read(REPORTS / 'checkpoint-25-manifest.json')
    protected = {n: row['sha256'] for n, row in manifest['proof_files'].items()}
    protected.update({n: h for n, h in manifest['working_inputs_sha256'].items()
                      if n.startswith('SafeLearning/') or n in {
                          'book/coverage/' + owner + '.json'
                          for owner in ['core', 'foundations', 'applied', 'modules', 'applied-promotions']}})
    for n, digest in protected.items():
        assert sha(ROOT / n) == digest, n
    names = {ROOT / 'book/coverage/progress.json', REPORTS / 'README.md'}
    # Only direct completed25 reports; checkpoint trees are already frozen.
    for p in REPORTS.glob('*25*'):
        if p.is_file() and p.suffix in {'.json', '.log', '.md', '.yml'} and p.stem != active_stem:
            names.add(p)
            if p.suffix == '.json' and '-execution-' in p.name:
                actual = read(p)
                assert type(actual['actual_exit_code']) is int
                assert actual['actual_exit_code'] in {0, 1}
                assert sha(ROOT / actual['log']) == actual['log_sha256']
                names.add(ROOT / actual['log'])
    for p in (ROOT / 'book/coverage/checks').glob('*25*.py'):
        names.add(p)
    for p in (ROOT / 'book/coverage/checks/future25-core').glob('*.json'):
        if any(s in p.name for s in ['publication25', 'checkpoint25', 'pages25']):
            names.add(p)
    for p in (ROOT / 'book/coverage/checks').glob('pages25-*.json'):
        names.add(p)
    names.add(predecessor_path)
    names.add(ROOT / 'book/coverage/inventory.json')
    names.add(ROOT / 'book/coverage/material-corrections.json')
    names.update(ROOT / ('book/coverage/' + owner + '.json')
                 for owner in ['core', 'foundations', 'applied', 'modules', 'applied-promotions'])
    originals = {}
    for p in names:
        assert p.is_file() and not p.is_symlink() and p.is_relative_to(ROOT)
        originals[p.relative_to(ROOT).as_posix()] = sha(p)
    rows = []
    for name, digest in sorted(originals.items()):
        original = ROOT / name
        assert sha(original) == digest
        if name in prior and prior[name]['sha256'] == digest:
            target = ROOT / prior[name]['file']
        else:
            target = BASE / 'original-root' / name
            target.parent.mkdir(parents=True, exist_ok=True)
            with target.open('xb') as stream:
                stream.write(original.read_bytes())
        assert sha(target) == digest
        rows.append({'original': {'file': name, 'sha256': digest},
                     'immutable_original_byte_copy': {'file': target.relative_to(ROOT).as_posix(),
                                                      'sha256': digest}})
    recorder = Path('/tmp/root_actual_step25_v1.py')
    alias = BASE / 'original-tmp/root_actual_step25_v1.py'
    alias.parent.mkdir(parents=True, exist_ok=True)
    with alias.open('xb') as stream:
        stream.write(recorder.read_bytes())
    assert sha(alias) == sha(recorder)
    for name, digest in protected.items():
        assert sha(ROOT / name) == digest
    record = {'status': 'completed_checkpoint25_actual_content_and_metadata_delivery_original_bytes_closed',
        'closed_at_utc': datetime.now(timezone.utc).isoformat(),
        'content_commit': commits[1], 'metadata_commit': commits[2],
        'both_actual_pages_runs_and_all31_live_assets_passed': True,
        'aliases': rows,
        'predecessor_catalogue': {'file': predecessor_path.relative_to(ROOT).as_posix(), 'sha256': sha(predecessor_path)},
        'entire_predecessor_catalogue_body_and_time': predecessor,
        'predecessor_self_log_scope_observation': {'original_running_log': old_running,
            'scope': 'The first closer captured its own still-empty stdout before returning. That byte snapshot is retained as historical preparation data; this successor closes the completed actual-v1 JSON/log and excludes its own running log. All other predecessor originals are exact; no result or original time is rewritten.'},
        'original_absolute_recorder_byte_alias': {'original_absolute_path': str(recorder),
            'canonical_file': alias.relative_to(ROOT).as_posix(), 'sha256': sha(alias)},
        'scope': 'Exact completed source/helper/review/execution/report/README/progress bytes and original times preserved before source53 or owner26 integration. Genuine failed attempts remain failures; no mathematical coverage is added.'}
    with OUT.open('x') as stream:
        stream.write(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'status': 'passed', 'closed_original_root_files': len(rows),
                      'content_commit': commits[1], 'metadata_commit': commits[2],
                      'live_owners_unchanged': True}))


if __name__ == '__main__':
    main()

"""Run a TMP Lean trial while protecting the genuinely installed26 inputs.

This records only the actual temporary compiler run. It installs no canonical
proof, modifies no ledger, and makes no aggregate or mathematical coverage claim.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys, time

ROOT = Path('/home/oxrexkevin/SafetyBased')
source, record = map(Path, sys.argv[1:3])
assert len(sys.argv) == 3
for path in (source, record):
    assert path.is_absolute() and path.resolve().is_relative_to(Path('/tmp'))
assert source.is_file() and source.suffix == '.lean'
assert record.suffix == '.json'
log = record.with_suffix('.log')
snapshot = record.with_name(record.stem + '-source.lean')
assert all(not p.exists() for p in (record, log, snapshot))

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(name): return json.loads((ROOT / name).read_text())
def ref(name): return {'file': name, 'sha256': sha(ROOT / name)}

PINNED = {
    'reports/full-coverage/checkpoint-26-selection.json': '12527ed93a283e1b37a491f7f799ac04e6217b1d7e20aee74116b312e580e23f',
    'reports/full-coverage/checkpoint-25-selection.json': '3559445215b6b5b9bd176363ded8d307a93724b2b68c1ba9845dc709a3b4ddff',
    'reports/full-coverage/checkpoint-25-manifest.json': '0329596719e09459730f34c9c84e9bacf4f3698a7c1699c4f848cef975ee5363',
    'book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json': '00a94eefea80aff4bd57ee2d511d3102f1a8652dfda1977272aefd9b7fe41cfb',
    'reports/full-coverage/owner26-reviewed-candidate-integration-v1.json': '7fa88d829c47797ab8258eb84ff5c7ce3399da66c9b03b591ea9820ca1eca06e',
    'reports/full-coverage/root-source53-final-owner-integration26-v1.json': '4029138dca32a74e8fd718fbe563d0b867d8ed408ad49a869e7308ea9867259d',
    'book/coverage/inventory.json': '4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be',
    'book/coverage/inventory-after-correction53.json': '4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be',
}
for name, digest in PINNED.items(): assert sha(ROOT / name) == digest, name
selection = read('reports/full-coverage/checkpoint-26-selection.json')
baseline = read('reports/full-coverage/checkpoint-25-selection.json')
binding = read('book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json')
integration = read('reports/full-coverage/owner26-reviewed-candidate-integration-v1.json')
global_audit = read('reports/full-coverage/root-source53-final-owner-integration26-v1.json')
assert selection['proof_file_count'] == len(selection['proof_files']) == 1167
assert selection['new_file_count'] == binding['new_proof_sources'] == 11
assert len(baseline['proof_files']) == 1156
assert set(baseline['proof_files']) <= set(selection['proof_files'])
assert all(selection['proof_files'][n]['sha256'] == r['sha256'] for n, r in baseline['proof_files'].items())
assert global_audit['integrity_status'] == 'passed' and global_audit['errors'] == []
assert integration['applied'] is True and integration['all44111_frozen25_inputs_exact'] is True
assert integration['all1156_selected25_root_source_hashes_exact'] is True
assets = binding['exact_current53_safelearning_assets_sha256']
assert len(assets) == 31
owners = {r['destination']: r['candidate']['sha256'] for r in integration['exact_replacements']}
assert len(owners) == 5
for row in global_audit['domains']:
    assert row['ledger_sha256'] == owners['book/coverage/' + row['domain'] + '.json']
held = {n: r['sha256'] for n, r in selection['proof_files'].items()}
held.update(assets)
held.update(owners)
corrections = 'book/coverage/material-corrections.json'
assert len(read(corrections)['corrections']) == 53
PINNED[corrections] = sha(ROOT / corrections)
for stem in ('owner26-integration-apply-execution-v1', 'root-source53-final-owner-integration26-execution-v1', 'prepare-checkpoint26-selection-execution-v1'):
    name = 'reports/full-coverage/' + stem + '.json'
    actual = read(name)
    assert type(actual['actual_exit_code']) is int and actual['actual_exit_code'] == 0
    assert actual['helper_sha256_before'] == actual['helper_sha256_after']
    assert sha(ROOT / actual['log']) == actual['log_sha256']
    for helper, digest in actual['helper_sha256_after'].items():
        assert sha(ROOT / helper) == digest
        PINNED[helper] = digest
    PINNED[name] = sha(ROOT / name)
    PINNED[actual['log']] = actual['log_sha256']
for name in ('verification/lean/lean-toolchain', 'verification/lean/lakefile.toml', 'verification/lean/lake-manifest.json'):
    PINNED[name] = sha(ROOT / name)
runner_before = sha(Path(__file__))

def guard():
    for name, digest in {**held, **PINNED}.items():
        assert sha(ROOT / name) == digest, name
    assert sha(Path(__file__)) == runner_before

guard()
before = sha(source)
with snapshot.open('xb') as stream: stream.write(source.read_bytes())
assert sha(snapshot) == before
command = ['lake', 'env', 'lean', str(source)]
started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
with log.open('xb') as stream:
    actual = subprocess.run(command, cwd=ROOT / 'verification/lean', stdout=stream, stderr=subprocess.STDOUT)
finished = datetime.now(timezone.utc).isoformat()
after = sha(source)
protection_errors = []
try: guard()
except Exception as error: protection_errors.append(str(error))
passed = actual.returncode == 0 and before == after and not protection_errors
out = {
    'status': 'passed_actual_tmp_lean_only' if passed else 'failed_actual_tmp_lean_or_protection',
    'actual_exit_code': actual.returncode, 'actual_runner_exit_code': 0 if passed else 1,
    'actual_command': command, 'actual_workdir': str(ROOT / 'verification/lean'),
    'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': time.monotonic() - tick,
    'source': str(source), 'source_sha256_before': before, 'source_sha256_after': after,
    'source_unchanged': before == after, 'source_snapshot': str(snapshot), 'source_snapshot_sha256': sha(snapshot),
    'raw_log': str(log), 'raw_log_sha256': sha(log),
    'original_actual_runner': {'file': str(Path(__file__)), 'sha256': runner_before},
    'actual_installed26_selection': ref('reports/full-coverage/checkpoint-26-selection.json'),
    'actual_installed26_global_integrity': ref('reports/full-coverage/root-source53-final-owner-integration26-v1.json'),
    'protected_proof_sources': 1167, 'unchanged_baseline25_selected_proof_sources': 1156,
    'unchanged_canonical_new26_proof_sources': 11, 'unchanged_current53_book_assets': 31,
    'unchanged_installed26_live_owners': 5, 'installed26_owner_sha256': owners,
    'original_installed26_provenance_sha256': PINNED, 'protection_errors': protection_errors,
    'canonical_installation_or_aggregate_verification_claimed': False,
}
with record.open('x') as stream: stream.write(json.dumps(out, indent=2) + '\n')
print(json.dumps(out))
raise SystemExit(0 if passed else 1)

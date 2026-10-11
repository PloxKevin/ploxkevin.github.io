from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys, time

root = Path('/home/oxrexkevin/SafetyBased')
source = Path(sys.argv[1]); record = Path(sys.argv[2])
log = record.with_suffix('.log'); snapshot = record.with_name(record.stem + '-source.lean')
assert source.is_absolute() and source.is_file()
assert not record.exists() and not log.exists() and not snapshot.exists()

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(name): return json.loads((root / name).read_text())
def ref(name): return {'file': name, 'sha256': sha(root / name)}

manifest_name = 'reports/full-coverage/checkpoint-24-manifest.json'
assert sha(root / manifest_name) == '5e0a58f71b685edbd3bbf7c965a2fda3ffd18f8edfde75c5bf810c7bb63d18e0'
manifest = read(manifest_name); assert len(manifest['proof_files']) == 1144
binding_name = 'book/coverage/checks/root-owner25-reviewed-candidate-bindings-v2.json'
assert sha(root / binding_name) == '512a65b16499e71e60ab8ba80ef0a27c2ad8a96e386ff45abc7de7ef6dd0256a'
binding = read(binding_name)
execution_name = 'reports/full-coverage/owner25-integration-apply-execution-v1.json'
execution = read(execution_name)
assert type(execution['actual_exit_code']) is int and execution['actual_exit_code'] == 0
assert execution['actual_command'] == ['python3', binding['helper']['file'], binding_name, '--apply']
assert execution['helper_sha256_before'] == execution['helper_sha256_after']
assert execution['helper_sha256_after'][binding['helper']['file']] == binding['helper']['sha256']
assert sha(root / execution['log']) == execution['log_sha256']
result_name = 'reports/full-coverage/owner25-reviewed-candidate-integration-v1.json'
result = read(result_name)
assert result['applied'] is True and result['all40485_frozen24_inputs_exact'] is True
assert result['all1144_selected24_root_source_hashes_exact'] is True
global_name = 'reports/full-coverage/root-source52-final-owner-integration25-v1.json'
global_audit = read(global_name)
assert global_audit['integrity_status'] == 'passed' and global_audit['errors'] == []
assert global_audit['inventory_sha256'] == '38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
held = {name: row['sha256'] for name, row in manifest['proof_files'].items()}
for owner in binding['owners'].values():
    for name, row in owner['new_immutable_proof_sources'].items():
        assert name not in held; held[name] = row['sha256']
assert len(held) == 1156
assets = binding['exact_current52_safelearning_assets_sha256']; assert len(assets) == 31
held.update(assets)
owner_hashes = {row['destination']: row['candidate']['sha256'] for row in result['exact_replacements']}
assert len(owner_hashes) == 5
for row in global_audit['domains']:
    assert row['ledger_sha256'] == owner_hashes['book/coverage/' + row['domain'] + '.json']
held.update(owner_hashes)
provenance = {name: sha(root / name) for name in [manifest_name, binding_name, execution_name, execution['log'], result_name, global_name, binding['helper']['file']]}
selection_name = 'reports/full-coverage/checkpoint-25-selection.json'
if (root / selection_name).exists():
    selection = read(selection_name)
    assert selection['proof_file_count'] == 1156
    assert {name: row['sha256'] for name, row in selection['proof_files'].items()} == {name: digest for name, digest in held.items() if name.startswith('verification/lean/')}
    provenance[selection_name] = sha(root / selection_name)

def guard():
    for name, digest in held.items(): assert sha(root / name) == digest, name
    for name, digest in provenance.items(): assert sha(root / name) == digest, name
    assert sha(root / 'book/coverage/inventory.json') == sha(root / 'book/coverage/inventory-after-correction52.json') == global_audit['inventory_sha256']

guard()
with snapshot.open('xb') as stream: stream.write(source.read_bytes())
before = sha(source); command = ['lake', 'env', 'lean', str(source)]
started = datetime.now(timezone.utc).isoformat(); tick = time.monotonic()
with log.open('xb') as stream:
    actual = subprocess.run(command, cwd=root / 'verification/lean', stdout=stream, stderr=subprocess.STDOUT)
finished = datetime.now(timezone.utc).isoformat(); after = sha(source)
protection_errors = []
try: guard()
except Exception as error: protection_errors.append(str(error))
passed = actual.returncode == 0 and before == after and not protection_errors
out = dict(status='passed_actual_tmp_lean_only' if passed else 'failed_actual_tmp_lean_or_protection',
    actual_exit_code=actual.returncode, actual_runner_exit_code=0 if passed else 1,
    actual_command=command, actual_workdir=str(root / 'verification/lean'),
    started_at_utc=started, finished_at_utc=finished, elapsed_seconds=time.monotonic() - tick,
    source=str(source), source_sha256_before=before, source_sha256_after=after, source_unchanged=before == after,
    source_snapshot=str(snapshot), source_snapshot_sha256=sha(snapshot), raw_log=str(log), raw_log_sha256=sha(log),
    original_actual_runner={'file': str(Path(__file__)), 'sha256': sha(Path(__file__))},
    actual_installed25_global_integrity=ref(global_name), installed25_owner_sha256=owner_hashes,
    protected_proof_sources=1156, unchanged_baseline24_selected_proof_sources=1144,
    unchanged_canonical_new25_proof_sources=12, unchanged_current52_book_assets=31,
    unchanged_current52_installed_live_owners=5, original_installed25_provenance_sha256=provenance,
    protection_errors=protection_errors, canonical_installation_or_aggregate_verification_claimed=False)
with record.open('x') as stream: stream.write(json.dumps(out, indent=2) + '\n')
print(json.dumps(out)); raise SystemExit(0 if passed else 1)

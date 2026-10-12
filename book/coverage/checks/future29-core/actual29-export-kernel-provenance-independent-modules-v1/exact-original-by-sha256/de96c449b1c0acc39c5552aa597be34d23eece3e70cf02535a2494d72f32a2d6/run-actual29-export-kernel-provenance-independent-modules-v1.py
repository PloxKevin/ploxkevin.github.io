from pathlib import Path
from datetime import datetime, timezone
import json, hashlib, subprocess, time

R = Path('/home/oxrexkevin/SafetyBased')
S = R/'reports/full-coverage/checkpoint-29'
E = R/'reports/full-coverage/lean-checkpoint-29'
H = Path('/tmp/review-actual29-export-kernel-provenance-independent-modules-v3.py')
O = Path('/tmp/actual29-export-kernel-provenance-independent-modules-actual-v1.json')
L = O.with_suffix('.log')
assert not O.exists() and not L.exists()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_bytes())
def rootref(p): return {'file': str(p.relative_to(R)), 'sha256': sha(p)}
selectionpath = R/'reports/full-coverage/checkpoint-29-selection.json'
selection = read(selectionpath)
originalpath = S/'reports/lean-verification/verification.json'
original = read(originalpath)
assert original['status'] == 'passed'
assert sha(originalpath) == '4cf89c6cfb19ab13cea59ef2e775b6b8b2c1432d83f56f79b7547e91c772d8d3'
proofs = {n: v['sha256'] for n, v in selection['proof_files'].items()}
assert proofs == original['proof_sha256'] and len(proofs) == 1197
pins = {}
def pin(n, h=None):
    p = Path(n)
    assert not p.is_absolute() and '..' not in p.parts
    assert (R/p).resolve().is_relative_to(R)
    expected = sha(R/p) if h is None else h
    if n in pins: assert pins[n] == expected
    pins[n] = expected
for n, h in proofs.items(): pin(n, h)
for n, h in original['source_sha256'].items(): pin(n, h)
assert len(original['source_sha256']) == 31
for field in ['proof_sha256', 'source_sha256', 'project_sha256']:
    for n, h in original[field].items(): pin('reports/full-coverage/checkpoint-29/'+n, h)
for n in ['book/coverage/core.json', 'book/coverage/foundations.json', 'book/coverage/applied.json', 'book/coverage/applied-promotions.json', 'book/coverage/modules.json', 'book/coverage/inventory.json', 'book/coverage/material-corrections.json', 'book/inventory_claims.py', 'reports/full-coverage/checkpoint-28-selection.json', 'reports/full-coverage/checkpoint-29-selection.json', 'reports/full-coverage/checkpoint-29-manifest.json', 'reports/full-coverage/checkpoint-29-ledger-manifest.json', 'reports/full-coverage/root-source65-final-owner-integration29-v1.json', 'reports/full-coverage/owner29-reviewed-candidate-integration-v1.json', 'reports/full-coverage/owner29-reviewed-candidate-integration-execution-v1.json', 'reports/full-coverage/root-source65-final-owner-integration29-execution-v1.json', 'book/coverage/checks/future29-core/current65-owner29-binding-v1.json', 'verification/lean/lakefile.toml', 'verification/lean/lake-manifest.json', 'verification/lean/lean-toolchain', 'verification/lean/SafeLearning.lean', 'book/coverage/lean_names.py']:
    pin(n)
global_report = read(R/'reports/full-coverage/root-source65-final-owner-integration29-v1.json')
assert global_report['status'].startswith('passed') and global_report['errors'] == []
for n in ['verify-checkpoint29-execution-v1.json', 'export-checkpoint29-execution-v1.json', 'export-integrity29-execution-v1.json']:
    p = R/'reports/full-coverage'/n
    d = read(p)
    assert d['status'] == 'passed' and type(d['actual_exit_code']) is int and d['actual_exit_code'] == 0
    pin(str(p.relative_to(R)))
    pin(d['log'], d['log_sha256'])
    for helper, h in d['helper_sha256_before'].items(): pin(helper, h)
    pin(d['recorder']['file'], d['recorder']['sha256'])
for base in [S/'reports/lean-verification', E]:
    for p in base.rglob('*'):
        if p.is_file(): pin(str(p.relative_to(R)))
pin('reports/full-coverage/checkpoint-28/reports/lean-verification/verification.json', '7f12161869033e85af7927332eddee77cf62cdefbc5bb351150adec6b300adf8')
before = {n: sha(R/n) for n in pins}
assert before == pins
command = ['python3', str(H)]
helpers_before = {str(H): sha(H), str(Path(__file__)): sha(Path(__file__))}
started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
with L.open('xb') as output:
    process = subprocess.run(command, cwd=R, stdout=output, stderr=subprocess.STDOUT)
finished = datetime.now(timezone.utc).isoformat()
elapsed = time.monotonic()-tick
after = {n: sha(R/n) for n in pins}
helpers_after = {n: sha(n) for n in helpers_before}
errors = [n for n in pins if after[n] != pins[n]] + [n for n in helpers_before if helpers_after[n] != helpers_before[n]]
record = {
    'status': 'passed' if process.returncode == 0 and not errors else 'failed',
    'actual_exit_code': process.returncode, 'actual_command': command, 'actual_workdir': str(R),
    'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': elapsed,
    'helper': str(H), 'helper_sha256_before': helpers_before, 'helper_sha256_after': helpers_after,
    'runner': str(Path(__file__)), 'runner_sha256': sha(Path(__file__)),
    'log': str(L), 'log_sha256': sha(L), 'raw_log': str(L), 'raw_log_sha256': sha(L),
    'protected_current_selected_source_count': len(proofs), 'protected_actual_current_site_asset_count': len(original['source_sha256']),
    'protected_live_owner_files': ['book/coverage/'+n+'.json' for n in ['core', 'foundations', 'applied', 'applied-promotions', 'modules']],
    'protected_inputs_sha256': pins, 'protected_before_sha256': before, 'protected_after_sha256': after,
    'protection_errors': errors, 'only_TMP_actual_data_peer_written': True,
    'compiler_started': False, 'producer_or_audit_rerun': False,
    'unchanged_exported_original_report': rootref(E/'verification-original.json')}
O.write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps({'actual_record': str(O), 'sha256': sha(O), 'actual_exit_code': process.returncode, 'elapsed_seconds': elapsed, 'protection_errors': errors, 'raw_log_sha256': sha(L)}))
raise SystemExit(process.returncode or int(bool(errors)))

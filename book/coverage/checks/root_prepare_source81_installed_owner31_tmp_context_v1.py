"""Prepare fresh TMP guards after the actual Source81/owner31 aggregate audit."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]
OLD = Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')
OLD_SHA = 'f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
TEMPLATE = Path('/tmp/root_tmp_lean_current81_historical_owner30_runner_v1.py')
TEMPLATE_SHA = 'e34da3e274cbb5f24a0abb7775024f6d26e6464b04c4ff48be212242588c5588'
CONTEXT = Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json')
RUNNER = Path('/tmp/root_tmp_lean_current81_installed_owner31_runner_v1.py')
REPORT = ROOT / 'reports/full-coverage/source81-installed-owner31-tmp-context-preparation-v1.json'
SELECTION = 'reports/full-coverage/checkpoint-31-selection.json'
SELECTION_SHA = 'cfe49bb94bf13fe8e464df60213a6639ffb99e63383f2f9300b93ef8a21d33da'
AUDIT = 'reports/full-coverage/runtime-checkpoint-31-source81-v1/reports/lean-verification/verification.json'
NATIVE = 'reports/full-coverage/verify-runtime-checkpoint31-source81-execution-v1.json'
INTEGRATION = 'reports/full-coverage/owner31-reviewed-candidate-integration-v4.json'
LEDGER = 'reports/full-coverage/lean-checkpoint-31/ledger-audit-working-v1.json'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file': str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}
def encode(d): return (json.dumps(d, indent=2)+'\n').encode()
def write_new(p, data):
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f: f.write(data)
def read(n): return json.loads((ROOT/n).read_bytes())

assert sha(OLD) == OLD_SHA and sha(TEMPLATE) == TEMPLATE_SHA
assert all(not p.exists() and not p.is_symlink() for p in [CONTEXT, RUNNER, REPORT])
old = json.loads(OLD.read_bytes())
assert sha(ROOT/SELECTION) == SELECTION_SHA
selection, audit, native, integration, ledger = map(read, [SELECTION, AUDIT, NATIVE, INTEGRATION, LEDGER])
assert native['status'] == 'passed' and type(native['actual_exit_code']) is int and native['actual_exit_code'] == 0
assert native['actual_command'] == ['python3', 'reports/full-coverage/runtime-checkpoint-31-source81-v1/verification/lean/verify.py', '--reuse-kernel-from', str(ROOT/'reports/full-coverage/runtime-checkpoint-30-final-css-v1')]
assert native['actual_workdir'] == str(ROOT) and sha(ROOT/native['log']) == native['log_sha256']
assert native['helper_sha256_before'] == native['helper_sha256_after'] == {'reports/full-coverage/runtime-checkpoint-31-source81-v1/verification/lean/verify.py': sha(ROOT/'reports/full-coverage/runtime-checkpoint-31-source81-v1/verification/lean/verify.py')}
assert audit['status'] == 'passed' and audit['proof_file_count'] == len(audit['proof_sha256']) == 1248
assert audit['theorem_count'] == len(audit['declarations']) == len(audit['axiom_dependencies']) == 11184
assert len(audit['checks']) == 1251 and all(type(c['exit_code']) is int and c['exit_code'] == 0 for c in audit['checks'])
assert sum(c.get('evidence_mode') == 'fresh_kernel_replay' for c in audit['checks']) == 6
assert sum(bool(c.get('reused_from')) for c in audit['checks']) == 1242
assert set(audit['allowed_standard_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(a) <= set(audit['allowed_standard_axioms']) for a in audit['axiom_dependencies'].values())
assert audit['proof_sha256'] == {n:r['sha256'] for n,r in selection['proof_files'].items()}
assert integration['applied'] is True and integration['coverage_complete'] is False
assert integration['new_canonical_files'] == 6 and integration['new_public_theorems'] == 104
assert ledger['integrity_status'] == 'passed' and ledger['errors'] == [] and ledger['mathematical_coverage_complete'] is False
assert ledger['inventory_sha256'] == sha(ROOT/'book/coverage/inventory.json')
owners = {r['destination']: r['candidate']['sha256'] for r in integration['exact_replacements']}
assert len(owners) == 5 and set(owners) == set(old['owners_sha256'])
for n,h in owners.items(): assert sha(ROOT/n) == h
for d in ledger['domains']: assert sha(ROOT/('book/coverage/'+d['domain']+'.json')) == d['ledger_sha256']
for field in ['source_sha256', 'proof_sha256', 'project_sha256']:
    for n,h in audit[field].items():
        assert sha(ROOT/'reports/full-coverage/runtime-checkpoint-31-source81-v1'/n) == h
        if n != 'verification/lean/SafeLearning.lean': assert sha(ROOT/n) == h
pins = {n:h for n,h in old['pins_sha256'].items() if not n.startswith('verification/lean/SafeLearning/')}
for n,h in pins.items(): assert sha(ROOT/n) == h
pins.update(audit['proof_sha256'])
for n in [SELECTION, AUDIT, NATIVE, INTEGRATION, LEDGER, str(Path(__file__).relative_to(ROOT))]: pins[n] = sha(ROOT/n)
assert len(audit['source_sha256']) == 31 and old['held_current_source_sha256'] == audit['source_sha256']
data = {'status': 'actual_source81_installed_owner31_selected31_audited_TMP_context_only',
    'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'pins_sha256': pins,
    'held_current_source_sha256': audit['source_sha256'], 'owners_sha256': owners,
    'selection': ref(ROOT/SELECTION), 'actual_audit': ref(ROOT/AUDIT),
    'actual_audit_execution': ref(ROOT/NATIVE), 'actual_owner31_integration': ref(ROOT/INTEGRATION),
    'actual_global_ledger': ref(ROOT/LEDGER), 'previous_historical_owner30_context': ref(OLD),
    'original_runner_template': ref(TEMPLATE), 'protected_selected31_proof_sources': 1248,
    'held_current81_final_css_book_assets': 31, 'held_installed_source81_raw_owner31_files': 5,
    'owner_identity_rebase_pending': False, 'aggregate_source81_verification_claimed': True,
    'new_TMP_trials_imply_new_canonical_or_whole_coverage': False, 'coverage_complete': False,
    'scope': 'Current Source81 and installed raw owner31, with actual selected31 aggregate Lean evidence. Each future TMP result proves only its exact encoded source; it makes no new canonical installation, source edit, or whole material claim.'}
write_new(CONTEXT, encode(data))
rendered = TEMPLATE.read_text()
substitutions = [(str(OLD), str(CONTEXT)), (OLD_SHA, sha(CONTEXT)),
    ('actual_source81_with_unchanged_raw_source79_owner30_for_tmp_trials_only', data['status']),
    ('actual_source81_historical_source79_owner30_context', 'actual_source81_installed_owner31_context'),
    ('actual_installed30_selection', 'actual_installed31_selection'),
    ('actual_runtime30_final_css_original_audit', 'actual_runtime31_source81_original_audit'),
    ('protected_selected30_proof_sources\':1242', 'protected_selected31_proof_sources\':1248'),
    ('unchanged_current_source79_raw_owner30_files', 'unchanged_installed_source81_raw_owner31_files'),
    ('installed30_raw_owner_sha256', 'installed31_raw_owner_sha256'),
    ('Run a genuine TMP Lean trial under actual Source81 and unchanged raw Source79 owner30.',
     'Run a genuine TMP Lean trial under audited Source81 and installed raw owner31.')]
for before, after in substitutions:
    assert rendered.count(before) == 1, before
    rendered = rendered.replace(before, after, 1)
compile(rendered, str(RUNNER), 'exec')
write_new(RUNNER, rendered.encode())
assert sha(OLD) == OLD_SHA and sha(TEMPLATE) == TEMPLATE_SHA
assert {n:sha(ROOT/n) for n in pins} == pins
assert {n:sha(ROOT/n) for n in owners} == owners
assert {n:sha(ROOT/n) for n in data['held_current_source_sha256']} == data['held_current_source_sha256']
record = {'status': 'prepared_actual_source81_installed_owner31_audited_TMP_context_only',
    'context': ref(CONTEXT), 'runner': ref(RUNNER), 'original_context': ref(OLD),
    'original_runner': ref(TEMPLATE), 'helper': ref(Path(__file__)),
    'actual_audit': ref(ROOT/AUDIT), 'actual_audit_execution': ref(ROOT/NATIVE),
    'actual_owner31_integration': ref(ROOT/INTEGRATION), 'actual_global_ledger': ref(ROOT/LEDGER),
    'literal_template_substitutions': substitutions, 'selected31_proofs': 1248,
    'installed_owner31_files': 5, 'owner_identity_rebase_pending': False,
    'aggregate_source81_verification_claimed': True, 'coverage_complete': False}
write_new(REPORT, encode(record))
print(json.dumps({'status': record['status'], 'context': record['context'], 'runner': record['runner'], 'report': ref(REPORT), 'coverage_complete': False}))

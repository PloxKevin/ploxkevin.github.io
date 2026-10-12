"""Bind new TMP trials to actual corrected64 bytes without relabeling audit28."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]
OLD = Path('/tmp/root_tmp_lean_current60_owner28_context_v1.json')
OLD_RUNNER = Path('/tmp/root_tmp_lean_current60_owner28_runner_v1.py')
NEW = Path('/tmp/root_tmp_lean_current64_owner28_context_v1.json')
RUNNER = Path('/tmp/root_tmp_lean_current64_owner28_runner_v1.py')

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_bytes())
def ref(p): return {'file':str(p),'sha256':sha(p)}

assert sha(OLD) == '35ac327b8d62c70dd9e0f83236716ee465d9b188cf656c58be97078b3eea5054'
assert sha(OLD_RUNNER) == 'f9f9f273bfa7c0f22d78f75fed23d32af794f13d51f329ae06747d3dac691c1a'
assert not NEW.exists() and not RUNNER.exists()
application = ROOT/'reports/full-coverage/source61-64-corrections-application-v1.json'
native = ROOT/'reports/full-coverage/source61-64-corrections-application29-execution-v1.json'
a = read(application); n = read(native)
assert a['status'] == 'passed_actual_source61_to64_corrections_full29_inventory_owner_identity_rebase_pending'
assert n['status'] == 'passed' and type(n['actual_exit_code']) is int and n['actual_exit_code'] == 0
assert sha(ROOT/n['log']) == n['log_sha256']
assert n['actual_command'] == ['python3','book/coverage/checks/root_apply_source61_64_v1.py','apply','--contract-sha256','f77619b105d1a9219c23795668a4a925e173874453f4c29904d8bf4b044a56bc']
assert [r['correction_id'] for r in a['applications']] == [61,62,63,64]
context = read(OLD)
changed = {}
for r in a['applications']:
    row = r['source_after']; assert sha(ROOT/row['file']) == row['sha256']
    changed[row['file']] = row['sha256']
assert len(changed) == 4
for name,h in context['held_current_source_sha256'].items():
    assert sha(ROOT/name) == changed.get(name,h), name
context['held_current_source_sha256'].update(changed)
context['pins_sha256']['book/coverage/inventory.json'] = sha(ROOT/'book/coverage/inventory.json')
context['pins_sha256']['book/coverage/material-corrections.json'] = sha(ROOT/'book/coverage/material-corrections.json')
context['pins_sha256']['book/coverage/inventory-after-correction64.json'] = sha(ROOT/'book/coverage/inventory-after-correction64.json')
for p in [application,native,ROOT/n['log'],ROOT/'book/coverage/checks/future28-core/completed28-content-and-metadata-delivery-closure-v1.json']:
    context['pins_sha256'][p.relative_to(ROOT).as_posix()] = sha(p)
for name,h in context['pins_sha256'].items(): assert sha(ROOT/name) == h, name
for name,h in context['owners_sha256'].items(): assert sha(ROOT/name) == h, name
inv = read(ROOT/'book/coverage/inventory.json')
assert all(context['held_current_source_sha256'][name] == h for name,h in inv['source_sha256'].items())
assert len(read(ROOT/'book/coverage/material-corrections.json')['corrections']) == 64
context.update(status='actual_current64_owner28_context_after_reviewed_source_corrections_for_new_tmp_trials_only',
    prepared_at_utc=datetime.now(timezone.utc).isoformat(),
    original_source60_context=ref(OLD), original_source60_runner=ref(OLD_RUNNER),
    actual_source61_to64_application=ref(application), actual_application_native=ref(native),
    scope='All 1186 actual audited checkpoint28 proof sources and five raw owner28 ledgers remain exact. Four lesson sources and current inventory/corrections are the actual independently reviewed Source64 version. Audit28 remains immutable evidence for its original Source60 inputs. New TMP trials do not claim owner identity rebasing, canonical installation or a new aggregate/kernel audit.',coverage_complete=False)
with NEW.open('xb') as f: f.write((json.dumps(context,indent=2)+'\n').encode())
text = OLD_RUNNER.read_text()
text = text.replace(str(OLD),str(NEW)).replace(sha(OLD),sha(NEW))
text = text.replace("context['status']=='actual_current60_owner28_verified_context_for_new_tmp_trials_only'", "context['status']=='actual_current64_owner28_context_after_reviewed_source_corrections_for_new_tmp_trials_only'")
text = text.replace('exact actually verified owner28 context','actual corrected Source64 and unchanged audited owner28 context')
text = text.replace("'actual_verified_owner28_context'", "'actual_source64_installed28_context'")
text = text.replace("'unchanged_current60_book_assets'", "'unchanged_current64_book_assets'")
assert str(OLD) not in text and sha(OLD) not in text
with RUNNER.open('x') as f: f.write(text)
assert sha(OLD) == '35ac327b8d62c70dd9e0f83236716ee465d9b188cf656c58be97078b3eea5054'
assert sha(OLD_RUNNER) == 'f9f9f273bfa7c0f22d78f75fed23d32af794f13d51f329ae06747d3dac691c1a'
print(json.dumps({'status':context['status'],'new_context':ref(NEW),'new_runner':ref(RUNNER),'coverage_complete':False}))

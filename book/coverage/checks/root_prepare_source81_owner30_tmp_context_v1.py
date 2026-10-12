"""Pin actual Source81 and unchanged raw Source79 owner30 for future TMP trials.

The previous aggregate audited Source79. This new context makes no Source81
aggregate or owner correspondence claim, and leaves the previous context intact.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]
OLD = Path('/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json')
OLD_SHA = '73ab502d42458069b9c5a9cfaa9a501c588558493eba0ea635b0a1eb869e6e72'
TEMPLATE = Path('/tmp/root_tmp_lean_current79_owner30_finalcss_runner_v1.py')
TEMPLATE_SHA = '82861b9eb3cbd7bccbb6bc7662de6972bc67cfc0548807a6f2983402b0ded281'
CONTEXT = Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')
RUNNER = Path('/tmp/root_tmp_lean_current81_historical_owner30_runner_v1.py')
REPORT = ROOT/'reports/full-coverage/source81-owner30-tmp-context-preparation-v1.json'
APPLICATION = 'reports/full-coverage/source80-81-corrections-application-v3.json'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file': str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}
def encode(d): return (json.dumps(d, indent=2)+'\n').encode()
def write_new(p, data):
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f: f.write(data)

assert sha(OLD) == OLD_SHA and sha(TEMPLATE) == TEMPLATE_SHA
assert all(not p.exists() and not p.is_symlink() for p in [CONTEXT, RUNNER, REPORT])
old = json.loads(OLD.read_bytes()); application = json.loads((ROOT/APPLICATION).read_bytes())
assert application['status'] == 'passed_actual_reviewed_source80_81_two_corrections_owner_rebase_pending'
assert application['coverage_complete'] is False and application['1242_selected_proofs_and_five_raw_owner30_files_unchanged'] is True
assert [r['correction_id'] for r in application['applications']] == [80, 81]
changed = {'SafeLearning/primer-linalg.html', 'SafeLearning/nn-in-the-loop.html', 'book/coverage/inventory.json', 'book/coverage/material-corrections.json'}
for n, h in {**old['pins_sha256'], **old['held_current_source_sha256'], **old['owners_sha256']}.items():
    p = ROOT/n; assert p.is_file() and not p.is_symlink()
    if n not in changed: assert sha(p) == h, n
for row in application['applications']:
    assert sha(ROOT/row['source']) == row['after_sha256']
    for key in ['inventory_before', 'inventory_after', 'source_proposal', 'independent_semantic_review', 'actual_fresh_parser']:
        r = row[key]; p = Path(r['file']); p = p if p.is_absolute() else ROOT/p
        assert sha(p) == r['sha256']
assert sha(ROOT/'book/coverage/inventory.json') == application['applications'][-1]['inventory_after']['sha256']
assert len(json.loads((ROOT/'book/coverage/material-corrections.json').read_bytes())['corrections']) == 81
data = {**old, 'status': 'actual_source81_with_unchanged_raw_source79_owner30_for_tmp_trials_only',
    'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
    'pins_sha256': {n: sha(ROOT/n) if n in changed else h for n, h in old['pins_sha256'].items()},
    'held_current_source_sha256': {n: sha(ROOT/n) if n in changed else h for n, h in old['held_current_source_sha256'].items()},
    'held_current81_final_css_book_assets': 31, 'held_historical_source79_raw_owner30_files': 5,
    'previous_source79_context': ref(OLD), 'actual_source80_81_application': ref(ROOT/APPLICATION),
    'owner_identity_rebase_pending': True, 'aggregate_source81_verification_claimed': False,
    'scope': 'Actual currentSource81/finalCSS with exact previously audited selected30 proof sources and unchanged rawSource79 owner30. Future TMP compiler results alone do not rebase ownership or prove whole material scope.'}
data.pop('held_current79_final_css_book_assets'); data.pop('held_current_source79_raw_owner30_files')
write_new(CONTEXT, encode(data))
rendered = TEMPLATE.read_text()
substitutions = [(str(OLD), str(CONTEXT)), (OLD_SHA, sha(CONTEXT)),
    ('actual_source79_final_css_owner30_selected30_audited_TMP_context_only', data['status']),
    ('actual_source79_final_css_owner30_context', 'actual_source81_historical_source79_owner30_context'),
    ('unchanged_current79_final_css_book_assets', 'unchanged_current81_final_css_book_assets'),
    ('Run a genuine TMP Lean trial under the actual Source79 final CSS and raw owner30 context.',
     'Run a genuine TMP Lean trial under actual Source81 and unchanged raw Source79 owner30.')]
for before, after in substitutions:
    assert rendered.count(before) == 1
    rendered = rendered.replace(before, after, 1)
compile(rendered, str(RUNNER), 'exec')
write_new(RUNNER, rendered.encode())
assert sha(OLD) == OLD_SHA and sha(TEMPLATE) == TEMPLATE_SHA
record = {'status': 'prepared_actual_source81_historical_source79_owner30_TMP_context_only', 'context': ref(CONTEXT), 'runner': ref(RUNNER), 'original_context': ref(OLD), 'original_runner': ref(TEMPLATE), 'actual_application': ref(ROOT/APPLICATION), 'helper': ref(Path(__file__)), 'literal_template_substitutions': substitutions, 'selected30_proofs_unchanged': 1242, 'owners_unchanged': 5, 'owner_identity_rebase_pending': True, 'aggregate_source81_verification_claimed': False, 'coverage_complete': False}
write_new(REPORT, encode(record))
print(json.dumps({'status': record['status'], 'context': record['context'], 'runner': record['runner'], 'report': ref(REPORT), 'coverage_complete': False}))

from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

root = Path('/home/oxrexkevin/SafetyBased')
output = Path('/tmp/foundations-metric-set-distance26-two-literals-full-source-review-request-v1.json')
assert not output.exists()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file': str(p), 'sha256': sha(p)}
def read(p): return json.loads(p.read_text())

inventory_path = root / 'book/coverage/inventory.json'
assert sha(inventory_path) == '38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
ledger_path = root / 'book/coverage/foundations.json'
assert sha(ledger_path) == '9c84c42febeaa5f398258eb03a485bfb3549d2bd165b3dc06ad6f35085737ada'
inventory = read(inventory_path); ledger = read(ledger_path)
keys = ['primer-linalg.html::node-197', 'primer-linalg.html::node-199']
key = keys[0]
units = [next(x for x in inventory['material_source_units'] if x['key'] == key) for key in keys]
unit = units[0]
old = [x for x in ledger['material_claims'] if any(k in x['source_unit_keys'] for k in keys)]
assert len(old) == 2 and all(x['status'] == 'pending' for x in old)
assert old[0]['source_text'] == unit['source_text']
source = Path('/tmp/foundations-metric-set-distance26-trial2.lean')
record_path = Path('/tmp/foundations-metric-set-distance26-trial2.json')
record = read(record_path)
assert type(record['actual_exit_code']) is int and record['actual_exit_code'] == 0
assert record['actual_runner_exit_code'] == 0 and record['protection_errors'] == []
assert record['source_sha256_before'] == record['source_sha256_after'] == sha(source)
snapshot = Path(record['source_snapshot']); raw = Path(record['raw_log'])
assert sha(snapshot) == sha(source) and sha(raw) == record['raw_log_sha256']
assert 'has been deprecated' in raw.read_text() and 'error' not in raw.read_text()
selection_path = root / 'reports/full-coverage/checkpoint-25-selection.json'
selection = read(selection_path); assert selection['proof_file_count'] == 1156
for p, row in selection['proof_files'].items(): assert sha(root / p) == row['sha256'], p
binding = read(root / 'book/coverage/checks/root-owner25-reviewed-candidate-bindings-v2.json')
assets = binding['exact_current52_safelearning_assets_sha256']; assert len(assets) == 31
for p, h in assets.items(): assert sha(root / p) == h, p
for p, h in record['installed25_owner_sha256'].items(): assert sha(root / p) == h, p
lines = (root / unit['source']).read_text().splitlines(keepends=True)
context = ''.join(lines[182:234])
names = re.findall(r'^theorem\s+(\w+)', source.read_text(), re.M)
assert len(names) == 8
prefix = 'SafeLearning.CompleteFoundationsMetricAndSetDistance26.'
groups = [
  {'component_id': 'metric_axioms_and_norm_induced_metric', 'lean_declarations': [prefix + x for x in names[:2]],
   'hypotheses': 'An actual MetricSpace for the metric axioms and normed additive group for norm-induced distance.',
   'per_component_reason': 'Proves separation iff, symmetry, triangle inequality, and actual norm difference equality for arbitrary points.'},
  {'component_id': 'literal_closed_ball_and_negative_zero_radius', 'lean_declarations': [prefix + x for x in names[2:5]],
   'hypotheses': 'Pseudometric space suffices for the sublevel definition and negative-radius emptiness; zero singleton requires a MetricSpace.',
   'per_component_reason': 'Derives the exact closed-ball distance sublevel, negative-radius empty set, and genuine zero-radius center singleton.'},
  {'component_id': 'genuine_nonempty_real_infimum_of_norm_distances', 'lean_declarations': [prefix + x for x in names[5:]],
   'hypotheses': 'Normed additive group and an explicitly nonempty set C, with no compactness or infimum attainment premise.',
   'per_component_reason': 'Proves the norm distance-value set is nonempty and bounded below by zero, then derives the actual greatest lower bound and its equality with the real infimum. Empty-set totalization is never used in the printed nonempty-set clause.'},
]
failed_path = Path('/tmp/foundations-metric-set-distance26-trial1.json')
failed = read(failed_path)
assert type(failed['actual_exit_code']) is int and failed['actual_exit_code'] == 1 and failed['protection_errors'] == []
for trial in [failed, record]:
 assert sha(Path(trial['source'])) == trial['source_sha256_before'] == trial['source_sha256_after']
 assert sha(Path(trial['source_snapshot'])) == trial['source_snapshot_sha256']
 assert sha(Path(trial['raw_log'])) == trial['raw_log_sha256']
trial_history = [{'trial': i, 'actual_record': ref(p), 'entire_actual_record': t, 'actual_exit_code': t['actual_exit_code'], 'source_snapshot': ref(Path(t['source_snapshot'])), 'raw_log': ref(Path(t['raw_log'])), 'raw_log_body': Path(t['raw_log']).read_text()} for i,p,t in [(1,failed_path,failed),(2,record_path,record)]]

api = root / 'verification/lean/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean'
api_lines = api.read_text().splitlines(keepends=True)
packet = {
 'schema_version': 1, 'status': 'request_for_fresh_independent_whole_literal_semantic_review_tmp_only',
 'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
 'current52_inventory': ref(inventory_path), 'installed25_foundations_ledger': ref(ledger_path),
 'entire_inventory_records': units, 'entire_original_pending_claims': old,
 'full_context': {'file': unit['source'], 'sha256': sha(root / unit['source']), 'first_line': 183, 'last_line': 234, 'text': context},
 'source': ref(source), 'full_source_body': source.read_text(),
 'public_declarations': [prefix + x for x in names], 'public_declaration_count': 8,
 'actual_standalone': ref(record_path), 'entire_actual_standalone_record': record,
 'raw_log': ref(raw), 'source_snapshot': ref(snapshot),
 'actual_original_runner': ref(Path(record['original_actual_runner']['file'])),
 'trial_history': trial_history, 'actual_failed_trials': [trial_history[0]], 'precise_groups_for_independent_decision': groups,
 'primary_local_definition': {'file': str(api), 'sha256': sha(api), 'first_line': 463, 'last_line': 481, 'text': ''.join(api_lines[462:481])},
 'protected_current52_assets_sha256': assets, 'protected_installed25_owners_sha256': record['installed25_owner_sha256'],
 'protected_selected25': ref(selection_path), 'all1156_selected_source_hashes_exact': True,
 'whole_literal_approval_requested_only_if_all_mathematical_clauses_match': True,
 'whole_parent_exercise_approval_requested': False,
 'scope_limits': ['TMP standalone only; no canonical or named execution.', 'No source HTML, inventory, live ledger, or current/frozen25 selection mutation.', 'The real norm-value infimum is explicitly nonempty and bounded below. No closedness, attainment or compactness assertion is added.', 'No neighboring metric-example, signed-distance, Hausdorff-distance, isometry or covering-number unit promotion.'],
 'original_preparation_helper': ref(Path(__file__)),
}
with output.open('x') as stream: json.dump(packet, stream, indent=2); stream.write('\n')
print(json.dumps({'status': 'actual_request_preparation_passed', 'request': ref(output), 'eight_public_theorems_actual_standalone_exit_code': 0, 'whole_math_decision_reserved_to_independent_peer': True}))

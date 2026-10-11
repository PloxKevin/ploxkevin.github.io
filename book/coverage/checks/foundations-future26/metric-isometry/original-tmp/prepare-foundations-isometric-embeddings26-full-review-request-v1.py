from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

root = Path('/home/oxrexkevin/SafetyBased')
output = Path('/tmp/foundations-isometric-embeddings26-single-literal-full-source-review-request-v1.json')
assert not output.exists()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file': str(p), 'sha256': sha(p)}
def read(p): return json.loads(p.read_text())

inventory_path = root / 'book/coverage/inventory.json'
assert sha(inventory_path) == '38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
ledger_path = root / 'book/coverage/foundations.json'
assert sha(ledger_path) == '9c84c42febeaa5f398258eb03a485bfb3549d2bd165b3dc06ad6f35085737ada'
inventory = read(inventory_path); ledger = read(ledger_path)
key = 'primer-linalg.html::node-209'
unit = next(x for x in inventory['material_source_units'] if x['key'] == key)
old = [x for x in ledger['material_claims'] if key in x['source_unit_keys']]
assert len(old) == 1 and old[0]['status'] == 'pending'
assert old[0]['source_text'] == unit['source_text']
source = Path('/tmp/CompleteFoundationsIsometricEmbeddings26.lean')
record_path = Path('/tmp/foundations-isometric-embeddings26-trial1.json')
record = read(record_path)
assert type(record['actual_exit_code']) is int and record['actual_exit_code'] == 0
assert record['actual_runner_exit_code'] == 0 and record['protection_errors'] == []
assert record['source_sha256_before'] == record['source_sha256_after'] == sha(source)
snapshot = Path(record['source_snapshot']); raw = Path(record['raw_log'])
assert sha(snapshot) == sha(source) and sha(raw) == record['raw_log_sha256']
assert raw.read_bytes() == b''
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
assert len(names) == 7
prefix = 'SafeLearning.CompleteFoundationsIsometricEmbeddings26.'
groups = [
  {'component_id': 'exact_isometry_norm_distance_definition', 'lean_declarations': [prefix + names[0]],
   'hypotheses': 'D is a pseudometric space and the target is a normed additive group; finite real Euclidean target is an instance.',
   'per_component_reason': 'Proves the exact equivalence of Mathlib isometry with every source-domain pair having the displayed target norm difference equal to the domain distance.'},
  {'component_id': 'genuine_unit_vector_affine_line_embedding', 'lean_declarations': [prefix + x for x in names[1:3]],
   'hypotheses': 'Real normed vector space, arbitrary offset and a direction with norm exactly one; arbitrary real line parameters.',
   'per_component_reason': 'Computes the actual affine-point difference and norm and derives the genuine map isometry for every pair.'},
  {'component_id': 'arbitrary_radial_kernel_invariance', 'lean_declarations': [prefix + x for x in names[3:5]],
   'hypotheses': 'An actual isometry and arbitrary function kappa from real distances to any value type; no kernel positivity or statistical learning premise.',
   'per_component_reason': 'Both metric-distance and target-norm versions follow from exact equality of distances, matching the entire arbitrary radial-dependence clause.'},
  {'component_id': 'nonlinear_embedding_proximity_caution', 'lean_declarations': [prefix + x for x in names[5:7]],
   'hypotheses': 'The explicit square map on the real line supplies a countermodel; the page warning is conditional modeling advice rather than a universal assertion about all learned embeddings.',
   'per_component_reason': 'Proves that the genuine nonlinear square map is not an isometry and changes the membership of the pair zero/two in distance threshold three. This demonstrates why an arbitrary nonlinear map cannot inherit radial-distance/proximity conclusions.'},
]
api = root / 'verification/lean/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean'
api_lines = api.read_text().splitlines(keepends=True)
packet = {
 'schema_version': 1, 'status': 'request_for_fresh_independent_whole_literal_semantic_review_tmp_only',
 'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
 'current52_inventory': ref(inventory_path), 'installed25_foundations_ledger': ref(ledger_path),
 'entire_inventory_record': unit, 'entire_original_pending_claims': old,
 'full_context': {'file': unit['source'], 'sha256': sha(root / unit['source']), 'first_line': 183, 'last_line': 234, 'text': context},
 'source': ref(source), 'full_source_body': source.read_text(),
 'public_declarations': [prefix + x for x in names], 'public_declaration_count': 7,
 'actual_standalone': ref(record_path), 'entire_actual_standalone_record': record,
 'raw_log': ref(raw), 'source_snapshot': ref(snapshot),
 'actual_original_runner': ref(Path(record['original_actual_runner']['file'])),
 'trial_history': [{'trial': 1, 'actual_record': ref(record_path), 'actual_exit_code': 0, 'source_snapshot': ref(snapshot), 'raw_log': ref(raw), 'warnings': []}],
 'actual_failed_trials': [], 'precise_groups_for_independent_decision': groups,
 'primary_local_definition': {'file': str(api), 'sha256': sha(api), 'first_line': 37, 'last_line': 61, 'text': ''.join(api_lines[36:61])},
 'protected_current52_assets_sha256': assets, 'protected_installed25_owners_sha256': record['installed25_owner_sha256'],
 'protected_selected25': ref(selection_path), 'all1156_selected_source_hashes_exact': True,
 'whole_literal_approval_requested_only_if_all_mathematical_clauses_match': True,
 'whole_parent_exercise_approval_requested': False,
 'scope_limits': ['TMP standalone only; no canonical or named execution.', 'No source HTML, inventory, live ledger, or current/frozen25 selection mutation.', 'The nonlinear caution asserts no theorem that every learned or every nonlinear embedding fails isometry.', 'No surrounding metric, signed-distance, Hausdorff-distance or covering-number unit promotion.'],
 'original_preparation_helper': ref(Path(__file__)),
}
with output.open('x') as stream: json.dump(packet, stream, indent=2); stream.write('\n')
print(json.dumps({'status': 'actual_request_preparation_passed', 'request': ref(output), 'seven_public_theorems_actual_standalone_exit_code': 0, 'whole_math_decision_reserved_to_independent_peer': True}))

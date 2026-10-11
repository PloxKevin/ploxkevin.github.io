from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys

root = Path('/home/oxrexkevin/SafetyBased')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
ref = lambda p: {'file': str(p), 'sha256': sha(p)}
assert len(sys.argv) == 2
source = Path(sys.argv[1])
assert source.parent == Path('/tmp') and re.fullmatch(r'foundations-balanced-sensor-spectral27-trial[1-9][0-9]*\.lean', source.name)
actual = source.with_suffix('.json')
record = json.loads(actual.read_text())
assert type(record['actual_exit_code']) is int and record['actual_exit_code'] == 0
assert type(record['actual_runner_exit_code']) is int and record['actual_runner_exit_code'] == 0
assert record['protection_errors'] == []
assert sha(source) == record['source_sha256_before'] == record['source_sha256_after']
assert sha(Path(record['source_snapshot'])) == record['source_snapshot_sha256'] == sha(source)
assert sha(Path(record['raw_log'])) == record['raw_log_sha256']
names = re.findall(r'^theorem (\w+)', source.read_text(), re.M)
assert len(names) == 10
ns = 'SafeLearning.CompleteFoundationsBalancedSensorSpectral27.'
selection_name = 'reports/full-coverage/checkpoint-26-selection.json'
selection = json.loads((root / selection_name).read_text())
assert len(selection['proof_files']) == 1167
inventory = json.loads((root / 'book/coverage/inventory.json').read_text())
units = {x['key']: x for x in inventory['material_source_units']}
key = 'primer-linalg.html::node-1264'
ledger = json.loads((root / 'book/coverage/foundations.json').read_text())
old = [x for x in ledger['material_claims'] if key in x.get('source_unit_keys', [])]
assert any(x['status'] == 'pending' for x in old)
page = 'SafeLearning/primer-linalg.html'
context = ''.join((root / page).read_text().splitlines(keepends=True)[1347:1363])
dependency = 'verification/lean/SafeLearning/CompleteFoundationsSpectralModels.lean'
assert sha(root / dependency) == selection['proof_files'][dependency]['sha256']
def group(identifier, indices, assumptions, reason):
    return {'component_id': identifier, 'lean_declarations': [ns + names[i] for i in indices],
        'hypotheses': assumptions, 'per_component_reason': reason, 'source_unit_keys': [key]}
groups = [
    group('actual_fixture_measurement', [0, 1], ['Known dimensionless H=[[1,1],[1,-1]] on EuclideanSpace Real (Fin2).'],
        'The actual H action sends the source estimated state(4,2) to(6,2).'),
    group('actual_transpose_gram_and_quadratic_identity', [2, 3], ['The actual matrix transpose/product and real Euclidean inner product.'],
        'Proves literal H-transpose H=2I and x-transpose H-transpose H x=2 norm(x)^2, not only an untyped coordinate polynomial.'),
    group('actual_all_direction_norm_stretch', [4, 5, 9], ['Every real Euclidean vector; both compared directions have unit norm in the last theorem.'],
        'Derives the exact squared and unsquared norm factor sqrt2; every unit direction has the same observed stretch, so none is weakly preferred in this model.'),
    group('actual_mathlib_singular_values_and_spectral_condition_ratio', [6, 7, 8], ['Mathlib singularValues of the genuine Euclidean linear map, ordered zero-based; the spectral ratio is first/last genuine singular value.'],
        'Actual adjoint composition is2id. Genuine singularValues0 and1 both equal sqrt2; the remaining infinite-sequence entries are0. Their positive first/last ratio is exactly1.')
]
history = {}
for p in sorted(Path('/tmp').glob('foundations-balanced-sensor-spectral27-trial*')):
    if p.is_file() and p.suffix in {'.lean', '.json', '.log'}: history[str(p)] = sha(p)
runner = Path(record['original_actual_runner']['file'])
assert sha(runner) == record['original_actual_runner']['sha256']
history[str(runner)] = sha(runner)
for name in ('root-tmp-lean27-runner-independent-foundations-full-code-review-v1.json',
        'root-tmp-lean27-runner-independent-foundations-full-code-review-v2.json'):
    p = Path('/tmp') / name
    history[str(p)] = sha(p)
primary = []
for relative, first, last in [
    ('Mathlib/Analysis/InnerProductSpace/SingularValues.lean', 70, 148),
    ('Mathlib/Analysis/InnerProductSpace/Adjoint.lean', 1056, 1064),
    ('Mathlib/Analysis/CStarAlgebra/Matrix.lean', 95, 129),
    ('Mathlib/LinearAlgebra/Eigenspace/Basic.lean', 433, 484),
]:
    p = root / 'verification/lean/.lake/packages/mathlib' / relative
    excerpt = ''.join(p.read_text().splitlines(keepends=True)[first-1:last])
    primary.append({'file': str(p), 'sha256': sha(p), 'first_line': first, 'last_line': last,
        'exact_excerpt': excerpt, 'excerpt_sha256': hashlib.sha256(excerpt.encode()).hexdigest()})
out = Path('/tmp/foundations-balanced-sensor-spectral27-one-whole-literal-review-request-v1.json')
assert not out.exists()
body = {'status': 'actual_tmp_standalone10_body_whole1264_review_requested_no_whole_approval_yet',
    'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'source': ref(source),
    'entire_lean_source': source.read_text(), 'public_theorem_count': 10,
    'all_public_declarations': [ns + n for n in names], 'actual_standalone': ref(actual),
    'actual_raw_log': ref(Path(record['raw_log'])), 'actual_source_snapshot': ref(Path(record['source_snapshot'])),
    'literal_units': [{'source_unit_key': key, 'entire_inventory_record': units[key],
        'original_current_ledger_records': old, 'requested_whole_decision_only_if_all_clauses_match': True}],
    'full_context': {'file': page, 'sha256': sha(root / page), 'first_line': 1348, 'last_line': 1363,
        'exact_excerpt': context, 'excerpt_sha256': hashlib.sha256(context.encode()).hexdigest()},
    'precise_component_groups': groups, 'all_original_history_sha256': history,
    'selected_full_dependency': {'file': dependency, 'sha256': sha(root / dependency),
        'entire_lean_source': (root / dependency).read_text(), 'entire_original_selected_proof_row': selection['proof_files'][dependency]},
    'actual_installed26_selection': {'file': selection_name, 'sha256': sha(root / selection_name)},
    'current_inventory': {'file': 'book/coverage/inventory.json', 'sha256': sha(root / 'book/coverage/inventory.json')},
    'local_primary_api_passages': primary, 'packet_preparer': ref(Path(__file__)),
    'scope': 'Actual TMP standalone only. Fresh complete1264 decision requires independent full literal/context/body reading. No named/canonical/current ledger/selection/aggregate/physical calibration or parent-exercise claim.'}
out.write_text(json.dumps(body, indent=2, ensure_ascii=False) + '\n')
print(json.dumps(ref(out)))

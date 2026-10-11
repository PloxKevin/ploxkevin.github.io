from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

R = Path('/home/oxrexkevin/SafetyBased')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
REF = lambda p: {'file': str(p), 'sha256': H(p)}
source = Path('/tmp/foundations-residual-orthogonality27-trial2.lean')
actual = source.with_suffix('.json')
a = json.loads(actual.read_text())
assert type(a['actual_exit_code']) is int and a['actual_exit_code'] == 0
assert type(a['actual_runner_exit_code']) is int and a['actual_runner_exit_code'] == 0
assert a['protection_errors'] == []
assert H(source) == a['source_sha256_before'] == a['source_sha256_after'] == H(a['source_snapshot'])
assert H(a['raw_log']) == a['raw_log_sha256']
names = re.findall(r'^theorem (\w+)', source.read_text(), re.M)
assert len(names) == 12
key = 'primer-linalg.html::node-1289'
inventory = json.loads((R / 'book/coverage/inventory.json').read_text())
unit = next(x for x in inventory['material_source_units'] if x['key'] == key)
ledger = json.loads((R / 'book/coverage/foundations.json').read_text())
old = [x for x in ledger['material_claims'] if key in x.get('source_unit_keys', [])]
assert len(old) == 1 and old[0]['status'] == 'pending'
page = R / unit['source']
assert H(page) == unit['source_sha256']
lines = page.read_text().splitlines(keepends=True)
context = ''.join(lines[1365:1404])
ns = 'SafeLearning.CompleteFoundationsResidualOrthogonality27.'
def group(identifier, indices, hypotheses, reason):
    return {'component_id': identifier, 'lean_declarations': [ns + names[i] for i in indices], 'hypotheses': hypotheses, 'per_component_reason': reason, 'source_unit_keys': [key]}
groups = [
 group('generic_exact_two_sided_expansion', [0], ['Real inner-product spaces; A is the actual continuous linear measurement map; loss is actual squared residual norm.'], 'The exact residual expansion holds for every x,v,t and is derived from A linearity and the inner-product norm identity.'),
 group('local_minimum_normal_equation_and_whole_range', [2, 9, 10, 11], ['Actual local minimum in the two-sided real vector-space topology; real Hilbert adjoint.'], 'The directional derivative is derived from the actual quadratic expansion. A local minimum forces its derivative zero for every v, giving orthogonality to every modeled direction and the genuine adjoint normal equation. The latter proves global optimality; no global premise replaces the local necessity.'),
 group('exact_global_sufficiency_and_difference', [1, 3, 4], ['Actual loss norm²; same A,y and normal equation.'], 'Necessity also follows algebraically from an everywhere nonnegative quadratic. At any normal-equation solution the loss difference at every z is exactly norm(A(z-x))², giving actual global sufficiency.'),
 group('independent_columns_positive_gram_and_attained_uniqueness', [5, 6, 7, 8], ['Independent columns interpreted as injective measurement map. Finite-dimensional unknown space for attainment; arbitrary finite real rectangular H in the direct Matrix.PosDef theorem.'], 'Injectivity makes the adjoint Gram quadratic form strictly positive and the actual H.transpose*H Matrix.PosDef. Finite-dimensional Gram invertibility proves existence, and the exact loss difference plus injectivity proves the unique global estimate, rather than merely uniqueness conditional on existence.')
]
history = {}
for p in sorted(Path('/tmp').glob('foundations-residual-orthogonality27-*')):
    if p.is_file() and p.suffix in {'.lean', '.json', '.log'}:
        history[str(p)] = H(p)
for name in ['/tmp/root_tmp_lean27_runner_v2.py', '/tmp/root-tmp-lean27-runner-independent-foundations-full-code-review-v2.json']:
    history[name] = H(name)
primary = []
for relative, first, last in [
 ('Mathlib/Analysis/InnerProductSpace/Adjoint.lean', 101, 149),
 ('Mathlib/Analysis/InnerProductSpace/Adjoint.lean', 229, 252),
 ('Mathlib/Analysis/Matrix/Order.lean', 153, 188),
 ('Mathlib/LinearAlgebra/Matrix/DotProduct.lean', 145, 179),
 ('Mathlib/Topology/Order/LocalExtr.lean', 279, 295),
]:
    p = R / 'verification/lean/.lake/packages/mathlib' / relative
    excerpt = ''.join(p.read_text().splitlines(keepends=True)[first-1:last])
    primary.append({'file': str(p), 'sha256': H(p), 'first_line': first, 'last_line': last, 'exact_excerpt': excerpt, 'excerpt_sha256': hashlib.sha256(excerpt.encode()).hexdigest()})
selection_file = R / 'reports/full-coverage/checkpoint-26-selection.json'
selection = json.loads(selection_file.read_text())
assert len(selection['proof_files']) == 1167
dependency = 'verification/lean/SafeLearning/CompleteFoundationsSpectralModels.lean'
assert H(R / dependency) == selection['proof_files'][dependency]['sha256']
out = Path('/tmp/foundations-residual-orthogonality27-one-whole-literal-full-source-review-request-v1.json')
assert not out.exists()
body = {'status': 'actual_tmp_standalone12_body_whole1289_review_requested_no_whole_approval_yet', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'source': REF(source), 'entire_lean_source': source.read_text(), 'public_theorem_count': 12, 'all_public_declarations': [ns + x for x in names], 'actual_standalone': REF(actual), 'actual_raw_log': REF(a['raw_log']), 'actual_source_snapshot': REF(a['source_snapshot']), 'actual_warning_group_count': Path(a['raw_log']).read_text().count(': warning:'), 'literal_units': [{'source_unit_key': key, 'entire_inventory_record': unit, 'original_current_ledger_records': old, 'requested_whole_decision_only_if_all_clauses_match': True}], 'full_context': {'file': unit['source'], 'sha256': H(page), 'first_line': 1366, 'last_line': 1404, 'exact_excerpt': context, 'excerpt_sha256': hashlib.sha256(context.encode()).hexdigest()}, 'precise_component_groups': groups, 'all_original_failed_and_passed_history_sha256': history, 'selected_full_adjacent_spectral_dependency': {'file': dependency, 'sha256': H(R / dependency), 'entire_lean_source': (R / dependency).read_text(), 'entire_original_selected_proof_row': selection['proof_files'][dependency]}, 'actual_installed26_selection': {'file': str(selection_file.relative_to(R)), 'sha256': H(selection_file)}, 'current_inventory': {'file': 'book/coverage/inventory.json', 'sha256': H(R / 'book/coverage/inventory.json')}, 'current_foundation_ledger': {'file': 'book/coverage/foundations.json', 'sha256': H(R / 'book/coverage/foundations.json')}, 'local_primary_api_passages': primary, 'packet_preparer': REF(Path(__file__)), 'scope': 'TMP-only actual standalone source. Request a fresh complete single paragraph1289 decision, including generic local-minimum necessity, actual range orthogonality and independent-column attained uniqueness. Adjacent third-sensor numerical exercise, other neighboring literals, matrix-to-map teaching interpretation and whole parent must be checked directly if invoked; no automatic promotion, canonical/named build or live owner action.'}
out.write_text(json.dumps(body, indent=2, ensure_ascii=False) + '\n')
print(json.dumps(REF(out)))

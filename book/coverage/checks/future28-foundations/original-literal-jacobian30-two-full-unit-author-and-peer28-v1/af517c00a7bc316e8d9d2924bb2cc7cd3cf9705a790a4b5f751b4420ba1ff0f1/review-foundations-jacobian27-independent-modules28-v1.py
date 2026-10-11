from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

ROOT = Path('/home/oxrexkevin/SafetyBased')
REQUEST = Path('/tmp/foundations-literal-jacobian27-two-full-units28-v1/foundations-literal-jacobian27-two-full-units28-v1.json')
OUT = Path('/tmp/foundations-jacobian27-independent-modules-review28-v1.json')
assert not OUT.exists()

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def ref(p):
    return {'file': str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}

def check(r):
    p = Path(r['file'])
    assert p.is_file() and sha(p) == r['sha256'], str(p)
    return p

started = datetime.now(timezone.utc).isoformat()
assert sha(REQUEST) == '99dde84d022ebd69785dcea3c537c176e0450acc887733bbbc7267da796d4529'
P = json.loads(REQUEST.read_bytes())
source = check(P['source'])
assert source.read_text() == P['entire_source']
names = []
namespace = ''
for line in source.read_text().splitlines():
    if line.startswith('namespace '):
        namespace = line[len('namespace '):]
    m = re.match(r'theorem (\w+)', line)
    if m:
        names.append(namespace + '.' + m.group(1))
assert names == P['public_theorem_names'] and len(names) == 27
assert not re.search(r'\b(sorry|admit|axiom)\b', source.read_text())
inventory = json.loads(check(P['actual_current55_inventory']).read_bytes())
owner = json.loads(check(P['actual_installed27_foundations_owner']).read_bytes())
check(P['actual_current55_corrections'])
check(P['actual_installed27_selection'])
units = {u['key']: u for u in inventory['material_source_units']}
assert P['current_source55_full_literal_records'] == [units[k] for k in P['whole_unit_targets']]
html = ROOT / 'SafeLearning/primer-optimization.html'
assert sha(html) == units[P['whole_unit_targets'][0]]['source_sha256']
assert P['full_current_teaching_context129_to195'] == '\n'.join(html.read_text().splitlines()[128:195])
for c in P['entire_original_pending_claim_bodies_and_times']:
    actual = next(r for r in owner['material_claims'] if r['id'] == c['id'])
    assert actual == c
for dep in P['full_selected_dependency_sources_read']:
    path = check(dep['source'])
    assert path.read_text() == dep['entire_source']
for r in P['primary_API_source_refs']:
    check(r)
for original, alias in P['original_closed_byte_aliases'].items():
    assert sha(check(alias)) == sha(Path(original)), original
trials = []
for row in P['actual_trials_full_original_bodies_times_and_raw']:
    path = check(row['record'])
    actual = json.loads(path.read_bytes())
    assert actual == row['entire_original_body_and_time']
    log = check(row['raw_log'])
    snapshot = check(row['source_snapshot'])
    assert log.read_text() == row['entire_raw_log']
    assert snapshot.read_text() == row['entire_source_snapshot']
    assert actual['raw_log_sha256'] == sha(log)
    assert actual['source_snapshot_sha256'] == sha(snapshot)
    assert actual['source_sha256_before'] == actual['source_sha256_after'] == sha(snapshot)
    assert actual['actual_command'] == ['lake', 'env', 'lean', actual['source']]
    assert actual['actual_workdir'] == str(ROOT / 'verification/lean')
    assert actual['source_unchanged'] and actual['protection_errors'] == []
    trials.append({'record': ref(path), 'raw_log': ref(log), 'source_snapshot': ref(snapshot),
                   'native_exit_code': actual['actual_exit_code'],
                   'original_started_at_utc': actual['started_at_utc'],
                   'original_finished_at_utc': actual['finished_at_utc'],
                   'all_original_body_and_time_preserved_by_exact_reference': True})
assert [t['native_exit_code'] for t in trials] == [1, 1, 1, 1, 1, 0]
assert trials[-1]['raw_log']['bytes'] == 0 and trials[-1]['source_snapshot']['sha256'] == sha(source)
clauses = []
for c in P['all_literal_clause_correspondence']:
    assert all(n in names for n in c['lean_declarations'])
    clauses.append({**c, 'independent_semantic_decision': 'approved_under_the_stated_differentiability_scope',
                    'mathematical_reason': c['correspondence']})
gap = ('The literal initially defines J as the array of actual coordinate partial derivatives, '
       'including points where only partials exist. The draft sourceJacobian is defined from '
       'Mathlib total fderiv and proved equal to those entries under full differentiability. '
       'Its specific pitfall partial array is sound, but a distinct literal partial-array definition, '
       'the generic equality under component differentiability, and the pitfall zero-array bridge '
       'are needed to remove this scope ambiguity before whole approval.')
clauses[0]['independent_semantic_decision'] = 'correct_component_but_requires_literal_partial_array_bridge'
clauses[0]['remaining_gap'] = gap
result = {
    'status': 'independent_full27_semantic_review_correct_components_whole_units_pending_one_definition_bridge',
    'reviewer': '/root/modules_finish28', 'started_at_utc': started,
    'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
    'author_request': ref(REQUEST), 'source': ref(source),
    'all_27_entire_public_proof_bodies_and_definitions_read': True,
    'public_theorem_names': names, 'public_theorem_count': 27,
    'entire_current55_inventory_literals': P['current_source55_full_literal_records'],
    'entire_original_pending_claim_bodies': P['entire_original_pending_claim_bodies_and_times'],
    'full_context_lines129_to195_exact_sha256': hashlib.sha256(P['full_current_teaching_context129_to195'].encode()).hexdigest(),
    'full_context_preserved_by_original_request_reference': True,
    'complete_selected_dependencies_read': [dep['source'] for dep in P['full_selected_dependency_sources_read']],
    'primary_API_read_scope': 'Full WithLp; FDeriv first-order equivalences815ff; actual little-o ratio374ff; relevant genuine finite Euclidean matrix/gradient APIs, with full selected dependencies.',
    'all_original_native_trials_preserved': trials,
    'all_original_closed_byte_aliases_validated': P['original_closed_byte_aliases'],
    'clause_semantic_decisions': clauses,
    'individual_unit_decisions': [
        {'source_unit_key': u['key'], 'text_sha256': u['text_sha256'],
         'entire_literal_read': True, 'whole_approved': False, 'remaining_gaps': [gap]}
        for u in P['current_source55_full_literal_records']],
    'important_scope_findings': [
        'Every component differentiable at x correctly yields true full finite-dimensional differentiability; no proposed Jacobian is assumed.',
        'The norm ratio tends to0 using the actual little-o remainder. Total division at0 does not alter its punctured meaning.',
        'Best local map is interpreted precisely as uniqueness among continuous linear maps with little-o remainder, with no finite-radius least-squares assertion.',
        'The activation diagonal is proved at coordinates where actual scalar derivatives exist; arbitrary nonsmooth activations at kinks are not declared differentiable.',
        'The exact source polynomial (x0*x1,x0+x1^2), every-point matrix, and printed (1,2) matrix are genuinely derived.',
        'The exact pitfall x0*x1/(x0^2+x1^2) with value0 at origin has actual zero coordinate partials, constant half on the nonzero diagonal, no continuity, and no first-order linear map.'
    ],
    'errors': [], 'canonical_owner_source_selection_or_publication_change_claimed': False,
    'whole_review_scope_limit': 'This bounded decision records one definition correspondence bridge, not a mathematical error in the 27 checked declarations. It authorizes no whole owner promotion.'
}
with OUT.open('x') as f:
    f.write(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'review': ref(OUT)}))

from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys, time
sys.dont_write_bytecode = True
ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = Path('/tmp/applied31-polygonal14-component-review-v1')
REQUEST = 'book/coverage/checks/future32-core/filippov-polygonal14-author-v1/filippov-polygonal14-full-source-actual-Euler-component-independent-review-request32-v1.json'
REQUEST_SHA = '766d6570af5e494b966d4e544681b85f72e228a06ad875950a7a707637e62e93'
SOURCE = Path('/tmp/CompleteCoreFilippovPolygonalConstruction32-draft-v3.lean')
SOURCE_SHA = '868e7f57c4259095bb0621f2aa00b2868e31e1a2aa5cc236b66c2f0e520a65c9'
CONTEXT = Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json')
CONTEXT_SHA = '0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c'
def real(n):
    p = Path(n)
    return p if p.is_absolute() else ROOT / p
def sha(p): return hashlib.sha256(real(p).read_bytes()).hexdigest()
def ref(p):
    p = real(p)
    return {'file': str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}
def read(p): return json.loads(real(p).read_bytes())
def guard(d):
    for n, h in d.items():
        p = real(n)
        assert not p.is_symlink() and sha(p) == h, n
assert not OUT.exists()
OUT.mkdir()
start = datetime.now(timezone.utc)
tick = time.monotonic()
helper_before = sha(__file__)
assert sha(CONTEXT) == CONTEXT_SHA and sha(SOURCE) == SOURCE_SHA and sha(REQUEST) == REQUEST_SHA
ctx = read(CONTEXT)
assert ctx['status'] == 'actual_source81_installed_owner31_selected31_audited_TMP_context_only'
held = {**ctx['pins_sha256'], **ctx['held_current_source_sha256'], **ctx['owners_sha256'], str(CONTEXT): CONTEXT_SHA, str(SOURCE): SOURCE_SHA, REQUEST: REQUEST_SHA}
guard(held)
request = read(REQUEST)
source = SOURCE.read_text()
sys.path.insert(0, str(ROOT / 'book/coverage'))
from lean_names import declarations, without_comments
decls = declarations(source)
assert decls == request['public_declarations'] and len(decls) == 16
theorems = [d['name'] for d in decls if d['kind'] == 'theorem']
assert len(theorems) == 14 and sum(d['kind'] == 'def' for d in decls) == 2
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b', without_comments(source))
for original, row in request['all_original_byte_aliases'].items():
    assert row['original_file'] == original
    assert sha(row['file']) == row['sha256'] and real(row['file']).stat().st_size == row['bytes']
    if real(original).exists(): assert sha(original) == row['sha256']
imp = request['exact_audited_selected31_import']
assert ref(imp['file']) == imp
import_source = real(imp['file']).read_text()
assert 'Classical.choose (actual_velocity_nonempty μ F x M hF)' in import_source
assert 'eulerNodes μ F M hF h x₀ n +' in import_source
assert 'actual_velocity_norm_bound μ F x _ M hF (chosenVelocity_mem μ F M hF x)' in import_source
parent_ref = request['parent_full_increment_peer']
assert ref(parent_ref['file']) == parent_ref
parent = read(parent_ref['file'])
assert parent['errors'] == [] and parent['all24_proof_bodies_and_six_definitions_read']
assert parent['all_six_new_components_approved'] and not parent['whole_Exercise16_or_generic_Filippov_existence_approved']
halfspaces = ROOT / 'verification/lean/SafeLearning/CompleteBarrierFilippovHalfspaces.lean'
assert sha(halfspaces) == '711e89ebfad207b24bc953e62b4a24039c9aea63811341878a6afb5601f70402'
half_source = halfspaces.read_text()
assert 'closure (convexHull ℝ (F' in half_source and 'mu N = 0' in half_source
def native_history(descriptor, expected_code=None):
    original = real(descriptor['file'])
    assert ref(original) == descriptor
    d = read(original)
    assert d['protection_errors'] == []
    assert d['actual_command'] == ['lake', 'env', 'lean', d['source']]
    assert d['actual_workdir'] == str(ROOT / 'verification/lean')
    assert sha(d['source_snapshot']) == d['source_snapshot_sha256'] == d['source_sha256_before'] == d['source_sha256_after']
    assert sha(d['raw_log']) == d['raw_log_sha256']
    assert d['actual_source81_installed_owner31_context']['sha256'] == CONTEXT_SHA
    if expected_code is not None: assert d['actual_exit_code'] == expected_code
    return {'native': descriptor, 'actual_exit_code': d['actual_exit_code'], 'actual_runner_exit_code': d['actual_runner_exit_code'], 'actual_command': d['actual_command'], 'actual_workdir': d['actual_workdir'], 'started_at_utc': d['started_at_utc'], 'finished_at_utc': d['finished_at_utc'], 'elapsed_seconds': d['elapsed_seconds'], 'source_snapshot': ref(d['source_snapshot']), 'raw_log': ref(d['raw_log'])}
originals = [native_history(d, c) for d, c in zip(request['original_native_history'], [1, 0, 0, 0])]
assert len(originals) == 4
assert 'error: not a positivity goal' in real(originals[0]['raw_log']['file']).read_text()
assert originals[2]['source_snapshot']['sha256'] == SOURCE_SHA
fresh = [native_history(ref(p), 0) for p in ['/tmp/applied-finish31-polygonal14-owner31-independent-native-v1.json', '/tmp/applied-finish31-polygonal14-owner31-independent-axioms-v1.json']]
assert fresh[0]['source_snapshot']['sha256'] == SOURCE_SHA and fresh[0]['actual_runner_exit_code'] == fresh[1]['actual_runner_exit_code'] == 0
axsource = real(read(fresh[1]['native']['file'])['source'])
expected_axiom_source = source + '\n' + ''.join('#print axioms ' + n + '\n' for n in theorems)
assert axsource.read_text() == expected_axiom_source
axlog = real(fresh[1]['raw_log']['file']).read_text()
lists = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", axlog, re.S)
axioms = {n: [x.strip() for x in a.split(',') if x.strip()] for n, a in lists}
assert set(axioms) == set(theorems) and len(axioms) == 14
assert axioms == request['all14_actual_axiom_lists']
assert all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms.values())
assert 'warning:' not in real(fresh[0]['raw_log']['file']).read_text() and 'warning:' not in axlog
body_assessments = [
 ('actual_clamp_identity', 'h ≥ 0; three genuine cases u ≤ 0, 0 < u ≤ h, and h < u give the exact two-positive-parts identity by ordered min/max rewrites and ring arithmetic.'),
 ('actual_ramp_difference', 'h ≥ 0; substituting u=t-kh into the clamp identity and casting k+1 derives the exact neighboring positive-part difference.'),
 ('actual_ramp_nonnegative', 'No h or time sign premise; the outer max with 0 proves nonnegativity directly.'),
 ('actual_ramp_zero', 'h ≥ 0 and k natural; -kh ≤ 0 bounds the inner min and yields zero at time0. Includes h=0.'),
 ('actual_ramp_monotone', 's ≤ t only; subtraction, min and max are monotone, so each ramp increases without extra h or time sign assumptions.'),
 ('actual_ramp_sum', 'h ≥ 0; induction on the genuine range sum telescopes exact neighboring positive-part differences. n=0 and all real t are covered.'),
 ('actual_ramp_sum_bound', 'h ≥ 0, t ≥ 0; the exact telescoping identity minus a nonnegative positive-part gives sum ≤ t.'),
 ('actual_ramp_continuous', 'All real h and natural k; finite min/max of constant and affine continuous real functions is continuous.'),
 ('actual_polygonal_initial', 'h ≥ 0; every actual coefficient is zero at time0, so the finite vector sum vanishes and the path starts at x0.'),
 ('actual_polygonal_continuous', 'For fixed finite n and real h, each actually chosen velocity at a fixed recursive Euler node is a constant vector in t. Scalar continuity, continuous scalar multiplication, finite sum and translation prove continuity; selector measurability is unnecessary and not assumed.'),
 ('actual_polygonal_radius_bound', 'h ≥ 0, t ≥ 0 and actual global ‖Fz‖ ≤ M. Derive M ≥ 0 at z=0, use genuine chosenVelocity_norm_bound, nonnegative coefficients, norm-of-sum and norm_smul, then the scalar ramp-sum bound. The result tM is independent of n and no radius bound is a premise.'),
 ('actual_ramp_sum_as_cap', 'h ≥ 0, t ≥ 0; split t ≤ nh versus nh < t in the exact telescope to prove the capped time min(nh,t), including n=0 and h=0.'),
 ('actual_ramp_sum_increment_bound', 'h ≥ 0, 0 ≤ s ≤ t; the actual capped sums and two cases s ≤ nh versus nh < s prove increment ≤ t-s. No positive h or positive n is required.'),
 ('actual_polygonal_uniform_increment_bound', 'h ≥ 0, 0 ≤ s ≤ t. Expand the actual difference into the same fixed velocities weighted by ramp increments. Each increment is nonnegative by ramp monotonicity; apply the true norm triangle inequality and velocity bound, distribute the finite sum, then the capped-time increment bound and derived M ≥ 0. Constant M is independent of h and n; no equicontinuity or target estimate is assumed.')
]
assert {n for n, _ in body_assessments} == {n.split('.')[-1] for n in theorems}
page = ROOT / 'SafeLearning/barriers.html'
lines = page.read_text().splitlines()
contextfile = OUT / 'actual-Exercise16-local-existence-context.json'
contextfile.write_text(json.dumps({'source': ref(page), 'Exercise16_inventory_id_not_literal_number': True, 'actual_local_Exercise10_1_prompt_and_answer_html': '\n'.join(lines[957:974]), 'scope': 'Context only. These14 components do not prove the printed locally bounded Filippov local-existence assertion or the whole barrier exercise.'}, indent=2) + '\n')
guard(held)
assessment = {'status': 'passed_independent_full_polygonal14_actual_Euler_component_math_body_domain_review', 'errors': [], 'reviewed_request': ref(REQUEST), 'source': ref(SOURCE), 'full_source_read': True, 'all14_full_proof_bodies_read': True, 'both_actual_definitions_read': True, 'all14_components_mathematically_approved': True, 'public_theorem_count': 14, 'public_name_count': 16, 'per_theorem_full_body_and_domain_assessment': [{'name': n, 'approved': True, 'reason': s, 'missing_component_clauses': []} for n, s in body_assessments], 'definition_assessments': [{'name': 'ramp', 'approved': True, 'reason': 'Actual clamped affine time min(h,t-kh) with max0, giving a finite contribution per cell for nonnegative h.'}, {'name': 'polygonal', 'approved': True, 'reason': 'Actual x0 plus finite ramp-weighted essential velocities selected at actual recursively constructed Euler nodes. No arbitrary predeclared path or assumed derivative is supplied.'}], 'actual_import': imp, 'full_Euler24_import_source_read': True, 'exact_existing_Euler24_full_peer_read_without_scope_promotion': parent_ref, 'actual_essential_velocity_definition_full_source_read': ref(halfspaces), 'assumptions_and_domains': ['E is a real normed vector space with measurable space and ProperSpace; μ.IsOpenPosMeasure gives actual nonempty essential velocities in the selected import.', 'F is globally pointwise bounded by M. This entails M≥0; local essential bounds alone are not the premise of this polygonal family.', 'Bounds use h≥0 and nonnegative forward times0≤s≤t, with n natural; no division by h or n appears and their zero cases are valid.', 'Continuity is in all real t for fixed h,n and a finite collection of constant selected velocities, even without measurable or continuous global selector.', 'For h≥0, the finite path is constant after nh. Refinement of a fixed horizon requires choosing h,n appropriately in later work.'], 'uniform_in_n_and_h_increment_estimate_approved': True, 'radius_bound_derived_from_actual_velocities': True, 'no_desired_radius_or_increment_or_integral_curve_conclusion_assumed': True, 'actual_local_printed_existence_context_read': ref(contextfile), 'original_author_native_histories_preserved': originals, 'fresh_independent_whole_file_compiler_and_all14_axiom_histories': fresh, 'all14_actual_fresh_axiom_lists': axioms, 'all_native_raw_logs_warnings_snapshots_times_retained': True, 'fresh_native_warnings': [], 'remaining_whole_existence_gaps': ['Formal polygonal/Euler grid interpolation identity.', 'Compact subsequence extraction under a fixed finite-horizon refinement.', 'Measurable derivative or integral representation and limiting derivative inclusion in Γ.', 'Local-domain or locally essentially bounded field construction and local integral-curve existence.'], 'selector_measurability_or_derivative_inclusion_or_integral_curve_existence_claimed': False, 'current_whole_Exercise16_or_generic_Filippov_existence_approved': False, 'included_in_selected31': False, 'no_Source_HTML_style_raw_owner_selected_proof_or_publication_mutation': True, 'coverage_complete': False}
(OUT / 'assessment.json').write_text(json.dumps(assessment, indent=2) + '\n')
end = datetime.now(timezone.utc)
(OUT / 'inner-actual-reader.json').write_text(json.dumps({'status': 'passed', 'actual_exit_code': 0, 'actual_command': ['python3', str(Path(__file__))], 'actual_workdir': str(ROOT), 'started_at_utc': start.isoformat(), 'finished_at_utc': end.isoformat(), 'elapsed_seconds': time.monotonic() - tick, 'helper_sha256_before': {str(Path(__file__)): helper_before}, 'helper_sha256_after': {str(Path(__file__)): sha(__file__)}, 'protected_inputs_sha256_before': held, 'protected_inputs_sha256_after': {n: sha(n) for n in held}, 'protection_errors': [], 'scope': 'Genuine measured independent whole14 body/domain/native/history reader under released0396. Only component approval; no compiler times invented or whole-existence promotion.'}, indent=2) + '\n')
print(json.dumps({'status': assessment['status'], 'assessment': ref(OUT / 'assessment.json'), 'elapsed_seconds': time.monotonic() - tick}))

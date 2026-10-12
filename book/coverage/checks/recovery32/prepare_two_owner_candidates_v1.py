"""Prepare six exact whole-literal correspondences without installing owners."""
from pathlib import Path
from collections import Counter
from datetime import datetime, timezone
import contextlib, copy, hashlib, importlib.util, json, sys, tempfile, time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'book/coverage/checks/recovery32'
COMMAND = ['python3', '-B', 'book/coverage/checks/recovery32/prepare_two_owner_candidates_v1.py']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file': p.relative_to(ROOT).as_posix(), 'sha256': sha(p), 'bytes': p.stat().st_size}
def new(p, d):
    assert p.is_relative_to(BASE) and not p.exists() and not p.is_symlink()
    with p.open('xb') as f: f.write((json.dumps(d, indent=2, ensure_ascii=False) + '\n').encode())
def load(p): return json.loads(p.read_bytes())
def route(label, *suffixes): return {'source_clause': label, 'declaration_suffixes': list(suffixes)}

ROUTES = {
 'Frobenius15': [
  route('Entrywise square-root Frobenius definition, Gram trace formula, and flattened Euclidean norm', 'actual_literal_frobenius_is_the_matrix_frobenius_norm', 'actual_frobenius_is_the_square_root_of_the_actual_gram_trace', 'actual_frobenius_is_the_euclidean_norm_of_one_flattened_vector'),
  route('Trace inner product equals entrywise pairing and the Euclidean inner product of flattened matrices', 'actual_trace_inner_product_is_the_full_entrywise_inner_product', 'actual_trace_pairing_is_the_true_euclidean_inner_product_of_flattened_matrices'),
  route('Actual matrix action and operator norm bounded by Frobenius', 'actual_matrix_times_a_column_is_the_actual_matrix_vector_product', 'actual_rectangular_euclidean_matrix_action_is_bounded_by_frobenius', 'actual_euclidean_operator_norm_is_bounded_by_frobenius'),
  route('Sharp rank upper bound derived from actual Gram eigenvalues, together with the lower comparison', 'actual_gram_eigenvalue_is_the_squared_norm_of_a_true_unit_eigenvector_image', 'actual_each_gram_eigenvalue_is_nonnegative_and_bounded_by_operator_norm_squared', 'actual_gram_trace_has_the_sharp_rank_times_operator_norm_squared_bound', 'actual_rectangular_frobenius_has_the_sharp_two_sided_rank_comparison'),
  route('Identity Frobenius norm is square root dimension; the norm family is not induced', 'actual_frobenius_identity_is_square_root_dimension', 'actual_two_dimensional_identity_separates_frobenius_from_every_induced_norm'),
  route('Exact source running matrix has norm sqrt10 with the printed 3.16 rounding', 'actual_printed_running_matrix_has_exact_frobenius_and_the_true_rounding')],
 'WeightedAngle11': [
  route('Every plane pair satisfies the coordinate formulas and cosine alignment identity', 'actual_plane_inner_product_coordinates', 'actual_plane_norm_coordinates', 'actual_alignment_identity_for_every_plane_pair'),
  route('Printed x=(1,2) and y=(3,-1) have pairing1 and lengths sqrt5 and sqrt10', 'actual_printed_Euclidean_vectors_inner_product_and_lengths'),
  route('The actual Euclidean angle is the genuine arccosine and rounds rigorously to81.9 degrees', 'actual_printed_Euclidean_angle_is_the_genuine_arccosine', 'actual_printed_Euclidean_angle_has_the_rigorous_one_decimal_degree_rounding'),
  route('M=diag(1,4) is positive definite and amounts to scaling coordinate2 by two', 'actual_diagonal_weighted_pairing_is_Euclidean_after_the_coordinate_scaling', 'actual_source_metric_is_positive_definite'),
  route('Printed weighted pairing is -5, lengths are sqrt17 and sqrt13, and angle is obtuse', 'actual_weighted_printed_vectors_inner_product_lengths_and_angle', 'actual_weighted_angle_is_strictly_obtuse'),
  route('Actual examples demonstrate that length and perpendicularity depend on the inner product', 'actual_weighting_changes_perpendicularity_and_length')],
 'MetricExamplesAndCertifiedBalls10': [
  route('All-input coordinate halfspace distance is max(x_i,0)', 'actual_all_input_coordinate_halfspace_distance'),
  route('Every real normed unit ball, including the planar unit disc, has distance max(norm(x)-1,0)', 'actual_every_real_normed_unit_ball_has_the_printed_all_input_distance'),
  route('For every real radius an infinity ball is exactly the coordinate box, allowing coordinate-wise intervals', 'actual_all_real_radii_infinity_balls_are_coordinate_boxes'),
  route('Grid edges are the actual unit steps; rectangular grids are connected and have attained shortest-path metrics', 'actual_rectangular_grid_edges_are_exactly_horizontal_or_vertical_unit_steps', 'actual_rectangular_grid_is_connected', 'actual_rectangular_grid_shortest_path_length_is_a_real_metric', 'actual_every_connected_grid_or_other_graph_has_an_attained_shortest_path_metric'),
  route('The printed Lipschitz lower margin certifies positive-center closed balls and their union', 'actual_Lipschitz_values_have_the_printed_lower_margin', 'actual_union_of_all_positive_value_Lipschitz_balls_is_certified'),
  route('Zero Lipschitz constant gives one constant positive value on the entire declared domain without division', 'actual_zero_Lipschitz_constant_certifies_the_entire_domain_without_division')],
 'Convolution13': [
  route('The same kernel is used at every output and the printed dimensions are three outputs from four inputs', 'actual_shared_kernel_and_finite_dimensions', 'actual_printed_correlation_is_the_given_three_by_four_matrix'),
  route('Genuine tap reversal is involutive and has the opposite finite index', 'actual_reverse_kernel_is_an_involution', 'actual_reversed_tap_has_the_opposite_finite_index'),
  route('Mathematical convolution reverses correlation taps with the explicit right-edge shift; stride/dilation preserve the bridge', 'actual_finite_convolution_is_correlation_with_the_reversed_kernel', 'actual_finite_correlation_is_convolution_with_the_reversed_kernel', 'actual_stride_dilation_and_bias_preserve_the_reversal_bridge'),
  route('All finite valid window indices and both conventions agree after reversal', 'actual_forward_and_backward_window_indices_agree_after_reversal', 'actual_full_finite_valid_window_reversal_bridge', 'actual_full_finite_valid_window_reverse_bridge'),
  route('The printed kernel reversal changes the matrix orientation and gives distinct outputs, establishing why the convention matters', 'actual_printed_kernel_reversal', 'actual_printed_mathematical_convolution_reverses_the_matrix_orientation', 'actual_printed_example_conventions_give_distinct_outputs')],
 'StaticRegret20': [
  route('The actual bounded periodic objective changes the unique best arm each round', 'rewardA_even', 'rewardA_odd', 'rewardB_even', 'rewardB_odd', 'actual_reward_bounds', 'actual_changing_best_reward'),
  route('The actual fixed-comparator cumulative totals make always-A a best fixed comparator at every horizon', 'totalA_succ', 'actual_totalA_even', 'actual_totalA_odd', 'actual_totalB_complement', 'actual_totalB_even', 'actual_totalB_odd', 'actual_A_is_best_fixed_for_every_horizon'),
  route('The same actual learner has zero static regret at every horizon and vanishing average static regret', 'actual_static_regret_zero_for_every_horizon', 'actual_vanishing_average_static_regret'),
  route('The dynamic comparator exploits changes and has positive average dynamic regret at every positive even horizon', 'actual_dynamic_regret', 'actual_positive_even_average_dynamic_regret', 'actual_printed_two_round_case'),
  route('Despite vanishing average static regret, the actual tracking gap is one at every odd round and does not vanish', 'actual_odd_round_tracking_gap', 'actual_tracking_gap_does_not_vanish')]
}
HYPOTHESES = {
 'Frobenius15': ['Arbitrary finite real rectangular matrices with decidable finite index sets; empty input and output dimensions are included.', 'Operator norm is the actual sourceMatrixMap 2 2 between Euclidean PiLp spaces. Gram, rank, and eigenvalue bounds are derived.', 'The non-induced norm-family assertion is witnessed by I2 on nontrivial real normed spaces; one-dimensional coincidence is permitted.', 'Printed running matrix is !![2,2;-1,1], with |sqrt10-3.16|<0.005.'],
 'WeightedAngle11': ['Plane is EuclideanSpace R (Fin2); the coordinate and alignment identities quantify over every plane pair.', 'Printed numerical vectors are exactly (1,2) and (3,-1), with sourceMetric=diag(1,4) and the actual second-coordinate scaling.', 'The angle is independently defined by arccosine; |angleDegrees-81.9|<0.05 is derived, as are positive definiteness and strict obtuseness.'],
 'MetricExamplesAndCertifiedBalls10': ['Coordinate halfspace uses finite Euclidean coordinates and an actual named coordinate. Infinity boxes use a nonempty finite coordinate set and every real radius, including negative radii.', 'The unit-ball distance formula holds in every real normed vector space, specializing to the printed planar unit disc.', 'Rectangular nearest-neighbor grids have vertices Fin(r+1) x Fin(c+1) and derived connectivity. Other grid/graph metrics assume structural connectedness.', 'Lipschitz margin and balls remain in the declared pseudometric domain. L is nonnegative; the positive-radius division branch assumes L>0. The zero branch assumes LipschitzWith0 and one positive center value.'],
 'Convolution13': ['Finite single-channel valid windows; generic integer-signal statements use x:Z->R, w:Fin(k)->R and arbitrary integer indexing, with the explicit right-edge shift.', 'Finite valid input has n+k+1 entries, nonempty k+1-tap kernel, and n+1 outputs; all index bounds are derived.', 'The printed specialization has three outputs, four inputs, kernel(1,-1) and example input(1,2,3,4). No multichannel or general-padding output formula is inferred.'],
 'StaticRegret20': ['Independently defined bounded two-arm rewards alternate 0/1 at arbitrary natural times; the learner always chooses A.', 'Static comparator maximizes cumulative fixed-arm reward; dynamic comparator sums per-round maxima. Their values are derived from the reward definitions.', 'Horizons are arbitrary naturals; the positive even dynamic-average theorem assumes n>0. Printed round1 is zero-based time0.', 'This exact counterexample disproves the implication from vanishing average static regret to tracking; always-A is not claimed worst-case no-regret on arbitrary streams.']
}

def main():
    tick = time.monotonic(); started = datetime.now(timezone.utc).isoformat()
    plan = load(BASE / 'five-source-map-v1.json'); ready = load(BASE / 'five-canonical-readiness-v1.json')
    assert ready['errors'] == [] and ready['actual_compiler_command_count'] == 10
    assert ready['source_map'] == ref(BASE / 'five-source-map-v1.json')
    protected = plan['protected_inputs_sha256']
    def guard():
        for n, h in protected.items():
            p = Path(n) if Path(n).is_absolute() else ROOT/n
            assert sha(p) == h, n
        for row in plan['sources']: assert ref(ROOT / row['canonical_source']) == row['canonical_source_ref']
    guard()
    candidates = {}; replacements = []; mappings = []
    for owner in ['foundations', 'applied']:
        original_path = ROOT / ('book/coverage/' + owner + '.json')
        original = load(original_path); candidate = copy.deepcopy(original)
        rows = [r for r in plan['sources'] if r['owner'] == owner]
        changed_ids = []
        for row in rows:
            namespace = row['original_namespace'][0]
            theorem_names = [r['name'] for r in row['public_declarations'] if r['kind'] in ['theorem', 'lemma']]
            correspondence = []
            for entry in ROUTES[row['family']]:
                declarations = [namespace + '.' + s for s in entry['declaration_suffixes']]
                assert set(declarations) <= set(theorem_names)
                correspondence.append({'source_clause': entry['source_clause'], 'lean_declarations': declarations})
            if row['family'] == 'MetricExamplesAndCertifiedBalls10':
                theorem_names.append('SafeLearning.CompleteFoundationsGeometry.positive_lipschitz_certified_ball')
                correspondence[-2]['lean_declarations'].append(theorem_names[-1])
            for key in row['approved_whole_material_keys']:
                indices = [i for i, c in enumerate(candidate['material_claims']) if key in c.get('source_unit_keys', []) and c['status'] == 'pending']
                assert len(indices) == 1, (key, indices)
                index = indices[0]; claim = candidate['material_claims'][index]; before = copy.deepcopy(claim)
                assert claim['source_unit_keys'] == [key]
                literal = claim.get('source_text', claim['statement_in_prose'])
                claim.update(status='proved', statement_in_prose=literal, kind='reviewed_entire_current_mathematical_literal', lean_declarations=theorem_names, hypotheses=HYPOTHESES[row['family']], correspondence='All clauses of this entire unchanged Source81 literal are covered by the exact declarations in all_subclaim_correspondence. The cited independent peer approved the whole literal and its structural domains after reading all proof bodies. No neighboring unit or parent exercise is promoted.', remaining_gaps=[], all_subclaim_correspondence=correspondence, independent_whole_literal_peer=row['independent_peer'], actual_canonical_pairs=ref(BASE/'five-canonical-readiness-v1.json'), original_pending_record=before)
                changed_ids.append(claim['id'])
                mappings.append({'owner': owner, 'material_key': key, 'claim_id': claim['id'], 'family': row['family'], 'before_JSON_pointer': ['material_claims', index], 'before_record_sha256': hashlib.sha256(json.dumps(before, sort_keys=True, ensure_ascii=False).encode()).hexdigest(), 'all_subclaim_correspondence': correspondence, 'independent_peer': row['independent_peer']})
            name = row['canonical_source']; h = row['canonical_source_ref']['sha256']
            if isinstance(candidate['proof_files'], list):
                assert name not in candidate['proof_files']; candidate['proof_files'].append(name)
                candidate['proof_sha256'][name] = h
            else:
                assert name not in candidate['proof_files']; candidate['proof_files'][name] = h
        assert candidate['exercises'] == original['exercises']
        assert len(candidate['material_claims']) == len(original['material_claims'])
        for a,b in zip(original['material_claims'], candidate['material_claims']):
            if a['id'] not in changed_ids: assert a == b
            else:
                assert b['original_pending_record'] == a and a['status'] == 'pending' and b['status'] == 'proved'
                for k in ['id','source_unit_keys','source','source_sha256','source_text','text_sha256','source_text_sha256','locator']:
                    if k in a: assert a[k] == b[k]
        if 'material_claim_statuses' in candidate.get('counts', {}): candidate['counts']['material_claim_statuses'] = dict(Counter(c['status'] for c in candidate['material_claims']))
        candidate['recovery32_reviewed_candidate_mapping'] = {'status': 'prepared_exact_Source81_whole_material_candidate_pending_independent_root_mapping_review_and_installation', 'baseline_owner': ref(original_path), 'source_map': ref(BASE/'five-source-map-v1.json'), 'actual_canonical_readiness': ref(BASE/'five-canonical-readiness-v1.json'), 'changed_pending_claim_ids': changed_ids, 'all_exercises_and_other_material_rows_preserved': True, 'coverage_complete': False}
        destination = BASE / (owner + '-candidate-v1.json'); new(destination, candidate)
        candidates[owner] = destination
        replacements.append({'destination': 'book/coverage/' + owner + '.json', 'before': ref(original_path), 'candidate': ref(destination), 'changed_claim_ids': changed_ids})
    guard()
    binding = {'status': 'prepared_two_exact_Source81_owner32_candidates_six_whole_material_rows_for_independent_root_review_only', 'source_map': ref(BASE/'five-source-map-v1.json'), 'actual_compiler_readiness': ref(BASE/'five-canonical-readiness-v1.json'), 'replacements': replacements, 'exact_whole_material_mappings': mappings, 'changed_pending_material_count': 6, 'exercise_changes': 0, 'source_or_inventory_changes': 0, 'unchanged_owners': {k:v for k,v in protected.items() if k.startswith('book/coverage/') and Path(k).name in ['modules.json','core.json','applied-promotions.json']}, 'coverage_complete': False, 'installation_performed': False}
    new(BASE / 'two-owner-candidate-bindings-v1.json', binding)
    sys.path.insert(0, str(ROOT/'book/coverage'))
    spec = importlib.util.spec_from_file_location('recovery32_validator', ROOT/'book/coverage/validate.py')
    validator = importlib.util.module_from_spec(spec); spec.loader.exec_module(validator)
    log = BASE/'isolated-validator-v1.log'
    with log.open('x') as raw, contextlib.redirect_stdout(raw), contextlib.redirect_stderr(raw):
        with tempfile.TemporaryDirectory(prefix='safetybased-recovery32-two-owner-validator-') as td:
            isolated = Path(td); (isolated/'book/coverage').mkdir(parents=True); (isolated/'verification').mkdir()
            (isolated/'SafeLearning').symlink_to(ROOT/'SafeLearning', target_is_directory=True)
            (isolated/'verification/lean').symlink_to(ROOT/'verification/lean', target_is_directory=True)
            (isolated/'book/coverage/inventory.json').symlink_to(ROOT/'book/coverage/inventory.json')
            for owner in ['foundations','applied','modules','core']:
                (isolated/'book/coverage'/ (owner+'.json')).symlink_to(candidates.get(owner, ROOT/('book/coverage/'+owner+'.json')))
            validator.ROOT = isolated; report = validator.validate()
            print(json.dumps({k: report[k] for k in ['integrity_status','mathematical_coverage_complete','counts','errors']}, indent=2))
    guard(); new(BASE/'isolated-ledger-audit-v1.json', report)
    passed = report['integrity_status'] == 'passed' and report['errors'] == [] and not report['mathematical_coverage_complete']
    assert report['counts']['material_review_statuses']['pending'] == 7933
    execution = {'status': 'passed' if passed else 'failed', 'actual_exit_code': 0 if passed else 1, 'command': COMMAND, 'actual_workdir': str(ROOT), 'started_at_utc': started, 'finished_at_utc': datetime.now(timezone.utc).isoformat(), 'elapsed_seconds': time.monotonic()-tick, 'actual_helper': ref(Path(__file__)), 'validator_source': ref(ROOT/'book/coverage/validate.py'), 'actual_validator_invocation': 'Imported the unchanged validator from the repository and invoked validate() with ROOT set to an isolated symlink tree containing exactly the two candidate ledgers and unchanged remaining owners.', 'raw_log': ref(log), 'audit': ref(BASE/'isolated-ledger-audit-v1.json'), 'binding': ref(BASE/'two-owner-candidate-bindings-v1.json'), 'protected_inputs_unchanged': True, 'candidate_installation_performed': False, 'counts': report['counts'], 'coverage_complete': False}
    new(BASE/'isolated-validator-execution-v1.json', execution)
    print(json.dumps({'status': execution['status'], 'binding': execution['binding'], 'audit': execution['audit'], 'counts': report['counts']}, indent=2))
    assert passed

if __name__ == '__main__': main()

#!/usr/bin/env python3
"""Bind the fresh cumulative parser and independent owner-impact review to precise whole routes."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'book/coverage'))
from lean_names import declarations


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ref(path):
    return {'file': str(path.relative_to(ROOT)), 'sha256': sha(path), 'bytes': path.stat().st_size}


def exact(record):
    path = Path(record['file'])
    if not path.is_absolute():
        path = ROOT / path
    assert sha(path) == record['sha256'], record['file']
    if 'bytes' in record:
        assert path.stat().st_size == record['bytes']
    return path


def main():
    output = OUT / 'independent-current88-two-page-whole-correspondence-approval-v1.json'
    assert not output.exists()
    candidate_path = OUT / 'independent-current88-two-page-cumulative-candidate-review-v1.json'
    impact_path = OUT / 'independent-existing-component-impact-v1.json'
    candidate = json.loads(candidate_path.read_bytes())
    impact = json.loads(impact_path.read_bytes())
    assert sha(candidate_path) == 'abd2dae0e2dbe5688d0cc126ec2c7de566b6f90b1a548c3cd0fd27352619e3c3'
    assert sha(impact_path) == '95f7f850553649253a106cacda7b05dd4dc0c127adbc0053aae763356fbf8454'
    assert candidate['errors'] == impact['errors'] == []
    assert candidate['protection_errors'] == []
    assert impact['existing_changed_proved_row_count'] == 0 and impact['carry_counts']['total'] == 578
    assert impact['additional_changed_ancestor_inventory_keys'] == []
    changed = set(candidate['changed_physical_literal_keys']['material_source_units'] + candidate['changed_physical_literal_keys']['exercises'])
    assert changed == set(impact['exact_changed_inventory_literals'])
    for collection in candidate['changed_whole_inventory_rows'].values():
        for key, rows in collection.items():
            assert rows['entire_current'] == impact['exact_changed_inventory_literals'][key]['current']
            assert rows['entire_candidate'] == impact['exact_changed_inventory_literals'][key]['prospective']
    nn = candidate['NN14_3_whole_exercise_and_four_material_decisions_conditional_on_exact_application']
    source_nn = ROOT / 'verification/lean/SafeLearning/CompleteModulesNNScalarOriginLinearization34.lean'
    source_conditional = ROOT / 'verification/lean/SafeLearning/CompleteAppliedConditionalExpectationMSEDensityWhole34.lean'
    assert sha(source_nn) == '57dd88f43d890086c2edcd187afc07a85d8e4b89a3fd3a3bc372dfc48f01381c'
    assert sha(source_conditional) == 'a17a13e4b8ab97a3d020061b923eb5cdf15d115d30654ddf12a968fb0c53aba6'
    nn_names = {d['name'] for d in declarations(source_nn.read_text()) if d['kind'] == 'theorem'}
    conditional_names = {d['name'] for d in declarations(source_conditional.read_text()) if d['kind'] == 'theorem'}
    assert len(nn_names) == 65 and len(conditional_names) == 28
    prefix = 'SafeLearning.CompleteAppliedConditionalExpectationMaterial31.'
    conditional_routes = [
        {'clause': 'The conditional mean is a version of the actual conditional-law mean for almost every observation; it has finite first moment and factors through Y.',
         'hypotheses': 'Measurable real random variable X, measurable Y, probability measure, integrable X. Equality after observation is AE; no unique value on a null observation is inferred.',
         'declarations': ['actual_conditional_law_has_finite_first_moment_at_almost_every_observation',
                          'actual_conditional_mean_is_the_regular_conditional_law_integral',
                          'actual_conditional_mean_really_is_a_function_of_the_observation']},
        {'clause': 'The printed discrete conditional mass sum and its marginal-to-joint tower calculation are genuine countable sums.',
         'hypotheses': 'Countable measurable-singleton observation/latent spaces; measurable Z/Y/value and integrable value(Z). The target latent space is standard Borel and nonempty. Null atoms are handled separately; there is no unsupported rearrangement.',
         'declarations': ['actual_discrete_conditional_mean_is_the_countable_probability_mass_sum',
                          'actual_discrete_weighted_tower_has_the_exact_printed_joint_sum']},
        {'clause': 'The displayed density integral is a conditional mean where the actual conditional density exists, including a given measurable density version.',
         'hypotheses': 'Integrable X, measurable Y; HasPDF for almost every observation under law(Y), or a measurable nonnegative density with conditional law equal to volume.withDensity for almost every observation. Density existence is supplied explicitly.',
         'declarations': ['actual_conditional_density_integral_is_the_actual_conditional_law_mean',
                          'actual_conditional_mean_is_the_density_integral_where_a_density_exists',
                          'actual_any_given_conditional_density_has_the_printed_integral_mean',
                          'actual_given_density_version_defines_the_conditional_mean_after_observation']},
        {'clause': 'Under finite second moment the conditional mean minimizes squared prediction error over measurable functions of the observation, including competitors with infinite extended risk.',
         'hypotheses': 'AE measurable X; MemLp X 2 (equivalently integrable square), measurable Y, prediction AE strongly measurable with respect to comap(Y). The finite-real-risk result uses competitor L2; the extended-risk result does not assume finite competitor risk globally.',
         'declarations': ['actual_finite_second_moment_is_the_exact_square_integrability_condition',
                          'actual_conditional_mean_minimizes_mean_squared_error',
                          'actual_conditional_mean_minimizes_even_extended_mean_squared_error']},
        {'clause': 'Conditioning on a measurable positive-probability event uses its normalized restricted law and yields the printed ratio and product formulas.',
         'hypotheses': 'Integrable X, measurable A and 0<mu.real(A). The positive probability assumption gives a normalized conditional law.',
         'declarations': ['actual_positive_probability_event_has_a_normalized_conditional_law',
                          'actual_event_conditioned_mean_is_the_exact_probability_ratio',
                          'actual_positive_event_mean_has_the_printed_multiplicative_identity']},
        {'clause': 'The displayed expectation tower and take-out-known rule use genuine conditional expectation.',
         'hypotheses': 'Measurable Y and integrable X; measurable g and integrable g(Y)X for pull-out. Random-variable equalities denote AE versions, as in the original complete peer.',
         'declarations': ['actual_observation_is_measurable_in_its_own_sigma_algebra',
                          'actual_known_observation_function_is_strongly_measurable',
                          'actual_expected_conditional_mean_equals_original_mean',
                          'actual_take_out_a_function_of_the_observed_random_variable']},
    ]
    for route in conditional_routes:
        route['declarations'] = [prefix + name for name in route['declarations']]
        assert set(route['declarations']) <= conditional_names
    route_groups = {
        'nn-in-the-loop.html::node-1210': list(nn['precise_clauses']),
        'nn-in-the-loop.html::node-1217': [key for key in nn['precise_clauses'] if key.startswith('part_a_')],
        'nn-in-the-loop.html::node-1218': [key for key in nn['precise_clauses'] if key.startswith('part_b_')],
        'nn-in-the-loop.html::node-1220': [key for key in nn['precise_clauses'] if key.startswith('part_c_')],
        'nn-in-the-loop.html::exercise-17': list(nn['precise_clauses']),
    }
    routes = {key: {'whole_exact_candidate_literal_approved': True,
                    'declarations': list(dict.fromkeys(name for group in groups for name in nn['precise_clauses'][group])),
                    'exact_clause_groups': groups, 'required_actual_domains': nn['actual_domains'],
                    'conditional_on_exact_original_offer_changes_and_candidate_literal_identity': True}
              for key, groups in route_groups.items()}
    for route in routes.values():
        assert set(route['declarations']) <= nn_names
    routes['primer-probability.html::node-387'] = {'whole_exact_candidate_literal_approved': True,
        'precise_clause_routes': conditional_routes,
        'conditional_on_exact_two_original_domain_qualifiers_and_candidate_literal_identity': True}
    native = json.loads(exact(candidate['fresh_all29_parser']).read_bytes())
    assert native['actual_exit_code'] == 0 and native['protection_errors'] == []
    exact(candidate['fresh_candidate_inventory'])
    for page in candidate['pages']:
        exact(page['original'])
        exact(page['candidate'])
    value = {'status': 'approved_exact_two_page_six_replacement_source_qualification_and_six_whole_candidate_correspondences',
             'errors': [], 'completed_at_utc': datetime.now(timezone.utc).isoformat(),
             'cumulative_candidate_review': ref(candidate_path), 'fresh_all29_parser': candidate['fresh_all29_parser'],
             'exact_candidate_inventory': candidate['fresh_candidate_inventory'],
             'exact_two_page_candidates': [{'source': page['source'], 'original': page['original'], 'candidate': page['candidate']} for page in candidate['pages']],
             'whole_correspondence_by_exact_candidate_key': routes, 'NN65_source': ref(source_nn), 'Conditional28_source': ref(source_conditional),
             'independent_existing_row_impact': ref(impact_path), 'existing_proved_changed_literal_rows': [],
             'existing_proved_unchanged_literal_carry_count': 578, 'existing_proved_unchanged_literal_carry_counts': impact['carry_counts'],
             'carry_disposition': 'Retain exact proved statement, hypotheses, declarations, correspondence, scope and historical fields; rebase only active page/inventory identities after exact qualification. No old mathematical decision is relabelled as fresh.',
             'additional_changed_ancestor_inventory_keys': [],
             'IQC14_6_unchanged_whole_literal_approvals_retained': candidate['unchanged_IQC14_6_current_whole_literal_approvals_retained'],
             'all_three_fresh_source_compiler_readiness_packets_retained': candidate['all_three_fresh_source_readiness_packets_and_actual_native_records_checked'],
             'current_unqualified_NN14_3_or_Conditional387_whole_approved': False,
             'source89_90_or_other_ordinals_reserved_or_applied_by_this_review': False,
             'live_site_owner_selected_proof_aggregate_inventory_or_publication_edits_by_this_review': False,
             'scope_limits': ['Exact scalar global/local walkthrough; strict local certificates form an open union and do not certify critical boundary fixed points.',
                              'Finite two-initial-state simulation is observational; all-time conclusions belong to the exact Basin proofs.',
                              'Conditional densities are assumed where used; null-observation values are versions and all printed random-variable equalities are AE.',
                              'No Exercise14.4, default2D explorer, neighboring total-variance or environment-wide performance lemma is promoted.'],
             'closure_helper': ref(Path(__file__)), 'coverage_complete': False}
    output.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'approval': ref(output), 'exact_candidate_inventory': candidate['fresh_candidate_inventory']}))


if __name__ == '__main__':
    main()

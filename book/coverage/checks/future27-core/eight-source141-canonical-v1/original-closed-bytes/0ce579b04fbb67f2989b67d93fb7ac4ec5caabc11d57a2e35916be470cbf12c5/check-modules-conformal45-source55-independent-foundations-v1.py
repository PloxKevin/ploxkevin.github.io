from pathlib import Path
from datetime import datetime, timezone
import json, hashlib, re

ROOT = Path('/home/oxrexkevin/SafetyBased')
REQUEST = Path('/tmp/modules-conformal45-source55-full-whole-review-request27-v1.json')
OUT = Path('/tmp/modules-conformal45-source55-independent-foundations-full-whole-review27-v1.json')
EXPECTED = 'a7f3fb3988d41be91af9c882ee8ae295feb4b855b1ec2a12b0aec082089ed3a6'
def path(name):
    p = Path(name)
    return p if p.is_absolute() else ROOT / p
def sha(name): return hashlib.sha256(path(name).read_bytes()).hexdigest()
def ref(name): return {'file': str(name), 'sha256': sha(name)}
def pin(name, digest):
    assert path(name).is_file() and sha(name) == digest, ('bytes differ', name)
def zero(d):
    fields = [d[k] for k in ('actual_exit_code', 'exit_code', 'actual_runner_exit_code') if k in d]
    assert fields and all(type(x) is int and x == 0 for x in fields)
def wrapper(x):
    r = x['record']; pin(r['file'], r['sha256'])
    assert json.loads(path(r['file']).read_text()) == x['entire_original_body_and_time']

assert not OUT.exists()
pin(REQUEST, EXPECTED)
p = json.loads(REQUEST.read_text())
for f, h in p['evidence_sha256'].items(): pin(f, h)
assert len(p['evidence_sha256']) == 71
for k in ('source55_proposal', 'source55_independent_semantic_and_full29_parser_peer',
          'original_eight_body_three_answer_peer'):
    wrapper(p[k])
old8 = p['original_eight_body_three_answer_peer']['entire_original_body_and_time']
precision = p['source55_independent_semantic_and_full29_parser_peer']['entire_original_body_and_time']
proposal = p['source55_proposal']['entire_original_body_and_time']
assert old8['errors'] == precision['errors'] == []
assert precision['proposal_approved'] is True and precision['whole_d_question_or_exercise_approved'] is False
assert len(p['three_entire_actual_sources']) == 3
assert [x['public_theorem_count'] for x in p['three_entire_actual_sources']] == [8, 28, 9]
assert p['total_public_theorem_count'] == 45
full_declarations = []
full_bodies = []
for s in p['three_entire_actual_sources']:
    r = s['source']; pin(r['file'], r['sha256'])
    text = path(r['file']).read_text()
    assert text == s['entire_source']
    assert not re.search(r'\b(sorry|axiom|admit)\b', text)
    ns = re.search(r'^namespace (\S+)', text, re.M).group(1)
    starts = list(re.finditer(r'^theorem (\w+)\b', text, re.M))
    names = [ns + '.' + m.group(1) for m in starts]
    assert names == s['all_public_declarations'] and len(names) == s['public_theorem_count']
    for ix, m in enumerate(starts):
        end = starts[ix + 1].start() if ix + 1 < len(starts) else text.rfind('\nend ')
        body = text[m.start():end]
        full_bodies.append({'lean_declaration': names[ix], 'source': r,
                            'entire_theorem_and_following_local_context': body,
                            'statement_with_all_hypotheses': body.split(':= by', 1)[0]})
    full_declarations.extend(names)
assert len(full_declarations) == len(set(full_declarations)) == 45
for s in p['selected_actual_source_bodies'].values():
    assert 'entire_source' in s
for f, s in p['selected_actual_source_bodies'].items():
    pin(f, s['sha256']); assert path(f).read_text() == s['entire_source']
assert len(p['selected_actual_source_bodies']) == 4

for actual, source in zip(p['genuine_successful_standalone_records'], p['three_entire_actual_sources']):
    wrapper(actual); d = actual['entire_original_body_and_time']; zero(d)
    assert d['protection_errors'] == [] and d['source_unchanged'] is True
    assert d['actual_command'] == ['lake', 'env', 'lean', source['source']['file']]
    assert d['actual_workdir'] == str(ROOT / 'verification/lean')
    assert d['source_sha256_before'] == d['source_sha256_after'] == source['source']['sha256']
    pin(d['source_snapshot'], d['source_snapshot_sha256'])
    assert d['source_snapshot_sha256'] == source['source']['sha256']
    pin(d['raw_log'], d['raw_log_sha256'])
    pin(d['original_actual_runner']['file'], d['original_actual_runner']['sha256'])
    assert d['protected_proof_sources'] == 1167
    assert d['unchanged_current53_book_assets'] == 31
    assert d['unchanged_installed26_live_owners'] == 5

history = []
for f, h in p['evidence_sha256'].items():
    if not re.search(r'-trial\d+\.json$', f): continue
    d = json.loads(path(f).read_text())
    assert type(d['actual_exit_code']) is int and d['actual_exit_code'] in (0, 1)
    assert d['protection_errors'] == []
    pin(d['raw_log'], d['raw_log_sha256'])
    pin(d['source_snapshot'], d['source_snapshot_sha256'])
    assert d['source_snapshot_sha256'] == d['source_sha256_before'] == d['source_sha256_after']
    history.append({'record': {'file': f, 'sha256': h}, 'entire_original_body_and_time': d,
                    'actual_failed': d['actual_exit_code'] == 1})
assert len(history) == 13

inventory = json.loads(path('book/coverage/inventory.json').read_text())
exercises = {x['key']: x for x in inventory['exercises']}
units = {x['key']: x for x in inventory['material_source_units']}
assert exercises[p['original_current53_entire_exercise']['key']] == p['original_current53_entire_exercise']
for u in p['original_current53_entire_units']: assert units[u['key']] == u
old_ex = p['original_current53_entire_exercise']; new_ex = p['proposed_source55_entire_exercise']
before, after = proposal['exact_replacements'][0]['before'], proposal['exact_replacements'][0]['after']
assert old_ex['source_text'].count(before) == 1
assert new_ex['source_text'] == old_ex['source_text'].replace(before, after)
for old, new in zip(p['original_current53_entire_units'], p['proposed_source55_entire_units']):
    expected = dict(old)
    expected['source_sha256'] = proposal['candidate_only']['sha256']
    if old['key'] == 'verification.html::node-1184':
        assert old['source_text'].count(before) == 1
        expected['source_text'] = old['source_text'].replace(before, after)
        expected['text_sha256'] = hashlib.sha256(expected['source_text'].encode()).hexdigest()
    assert new == expected
pin(proposal['candidate_only']['file'], proposal['candidate_only']['sha256'])
pin(proposal['primary_original']['file'], proposal['primary_original']['sha256'])
primary = path(proposal['primary_original']['file']).read_text()
primary_start = primary.index('Theorem D.1 (Conformal calibration coverage guarantee)')
primary_end_marker = 'Proof. See Theorem 2.2 of [83].'
primary_end = primary.index(primary_end_marker, primary_start) + len(primary_end_marker)
full_primary_d1_d2 = primary[primary_start:primary_end]
assert full_primary_d1_d2 == precision['full_relevant_primary_D1_D2_text_read']
assert 'D.2' in full_primary_d1_d2
current_html = path('SafeLearning/verification.html').read_text()
assert proposal['full_original_section5_html_excerpt'] in current_html
assert proposal['full_original_parent_html_excerpt'] in current_html
assert proposal['full_proposed_parent_html_excerpt'] in path(proposal['candidate_only']['file']).read_text()

selection = json.loads(path('reports/full-coverage/checkpoint-26-selection.json').read_text())
binding = json.loads(path('book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json').read_text())
assert len(selection['proof_files']) == 1167
for f, row in selection['proof_files'].items(): pin(f, row['sha256'])
assert len(binding['exact_current53_safelearning_assets_sha256']) == 31
for f, h in binding['exact_current53_safelearning_assets_sha256'].items(): pin(f, h)
owner_map = p['genuine_successful_standalone_records'][0]['entire_original_body_and_time']['installed26_owner_sha256']
assert len(owner_map) == 5
for f, h in owner_map.items(): pin(f, h)
modules = json.loads(path('book/coverage/modules.json').read_text())
current_module_rows = modules['material_claims'] if 'material_claims' in modules else modules['material']
for row in p['original_current_material_rows_and_times']:
    assert row in current_module_rows

C = 'SafeLearning.CompleteModulesConformalContinuous27.'
L = 'SafeLearning.CompleteModulesConformalLexicographic27.'
U = 'SafeLearning.CompleteModulesConformalCommonUniform27.'
def names(prefix, *suffixes): return [prefix + s for s in suffixes]
groups = [
 {'component_id': 'actual_joint_exchangeable_distinct_rank_and_calibration',
  'lean_declarations': names(C, 'actual_tie_free_joint_exchangeability_gives_every_rank_cdf',
    'actual_calibration_success_is_the_strict_rank_cdf', 'actual_tie_free_split_calibration_coverage_is_exact'),
  'hypotheses': ['Arbitrary probability law on n+1 real scores, invariant under every index permutation.',
    'Joint score vector is almost surely injective; the test index is any fixed coordinate.',
    'k is the finite calibration rank with k <= n; the printed inherited 0 < alpha < 1 gives 1 <= k.'],
  'per_component_reason': 'Actual finite strict ranks and equal coordinate rank probabilities derive every rank CDF. The genuine finite-subset calibrationThreshold is the kth order statistic of the other n scores, retaining multiplicities. Calibration membership equals strictRank < k, giving k/(n+1) under a.s. distinctness.'},
 {'component_id': 'actual_ceiling_and_numeric_full_rank_example',
  'lean_declarations': names(C, 'actual_ceiling_rank_has_the_literal_two_sided_coverage_arithmetic',
    'actual_nine_and_ten_calibration_ranks_and_exact_ratios', 'actual_nine_calibration_threshold_is_an_attained_real_maximum',
    'actual_tie_free_split_calibration_has_both_literal_coverage_bounds'),
  'hypotheses': ['The page fixes alpha in (0,1), k=ceil((n+1)(1-alpha)) <= n.',
    'The equality of coverage with the ceiling fraction retains the same joint exchangeability and a.s. distinctness.'],
  'per_component_reason': 'Both ceiling inequalities are derived and divided by the positive n+1. Exact n9/alpha1/10 gives k9, attained calibration maximum and coverage9/10; n10 gives k10 and10/11. The descriptive tightness sentence concerns ceiling rounding of the probability guarantee, with no optimal prediction-set-size theorem.'},
 {'component_id': 'actual_independent_uniform_joint_seed_construction',
  'lean_declarations': names(L, 'actual_attached_seed_pairs_are_measurable',
    'actual_iid_seed_law_is_invariant_under_permutations', 'actual_two_independent_atomless_seed_coordinates_cannot_tie',
    'actual_all_independent_atomless_seed_coordinates_are_distinct',
    'actual_independent_seed_attachment_preserves_joint_exchangeability',
    'actual_independent_atomless_seed_attachment_is_almost_surely_tie_free'),
  'hypotheses': ['Original score law is an arbitrary exchangeable probability law, including dependent or atomic scores.',
    'Seed law is the genuine finite product of Uniform[0,1], independent of the entire original score vector.',
    'The more general atomless-seed exports require probability and NullSingletonClass of the seed law.'],
  'per_component_reason': 'Volume restricted to Icc0 1 supplies actual probability/atomless instances. The product law and measurable score-seed attachment are constructed. Product permutation invariance and commutation derive pair exchangeability, while independence plus atomlessness derives a.s. pair injectivity; neither conclusion is assumed.'},
 {'component_id': 'actual_lex_rank_cdf_event_inclusion_and_raw_tied_lower',
  'lean_declarations': names(L, 'actual_tie_free_exchangeable_rank_is_uniform',
    'actual_lexicographic_joint_exchangeability_gives_every_rank_cdf',
    'actual_forgetting_independent_seeds_recovers_the_original_score_law',
    'actual_original_strict_score_count_is_bounded_by_lexicographic_pair_count',
    'actual_small_lexicographic_rank_implies_original_calibration_membership',
    'actual_independent_uniform_seed_lexicographic_membership_has_exact_probability',
    'actual_independent_uniform_seed_construction_proves_the_tied_lower_coverage_bound',
    'actual_ties_preserve_the_one_minus_alpha_original_calibration_guarantee'),
  'hypotheses': ['Arbitrary original exchangeable probability law; no original-score iid or no-ties premise.',
    'Uniform seeds are genuinely independent and attached to every calibration and test score.',
    'k <= n; the printed ceiling rank and inherited alpha in (0,1) remain explicit.'],
  'per_component_reason': 'The full finite rank bijection, one occurrence of each rank, measurable rank events and indicator integration derive the pair rank CDF. Strict raw count is bounded by the pair count, giving pointwise inclusion in the actual raw calibration event. Forgetting seeds recovers precisely the original score law, so probability monotonicity proves raw coverage >= k/(n+1) >= 1-alpha.'},
 {'component_id': 'actual_consistent_randomized_calibration_and_test_rule',
  'lean_declarations': names(L, 'actual_lexicographic_rank_counts_only_the_other_calibration_pairs',
    'actual_seeded_ceiling_rank_has_both_literal_coverage_arithmetic_bounds',
    'actual_consistently_seeded_calibration_and_prediction_membership_has_both_bounds'),
  'hypotheses': ['Independent uniforms on all n+1 scores, independent of the arbitrary exchangeable original vector.',
    'Prediction membership uses the same lexicographic score-seed order for calibration and test comparisons.',
    'The finite ceiling rank k <= n and the actual probability-level hypotheses remain.'],
  'per_component_reason': 'randomizedCalibrationMembership explicitly counts only the other calibration pairs preceding the test pair. Its equality to the actual pair strict rank is proved, so the constructed seeded law gives exact probability k/(n+1), then both lower and strict upper bounds. This does not assume a uniform rank premise or apply a separate test-only randomization rule.'},
 {'component_id': 'true_tie_and_continuous_marginal_countermodels',
  'lean_declarations': names(C, 'actual_constant_nine_calibration_scores_are_always_covered_and_break_the_strict_upper') +
    names(U, 'actual_common_uniform_score_joint_law_is_exchangeable', 'actual_every_common_score_marginal_is_uniform',
      'actual_every_common_score_marginal_has_zero_atom_mass', 'actual_unit_uniform_cdf_formula',
      'actual_every_common_score_marginal_cdf_is_continuous',
      'actual_common_uniform_scores_are_tied_everywhere_almost_surely',
      'actual_common_uniform_scores_are_always_calibration_covered',
      'actual_continuous_marginals_do_not_give_the_strict_upper_coverage_bound'),
  'hypotheses': ['The counterexamples use actual n9/alpha1/10/k9 laws.',
    'Common Uniform uses one actual uniform draw shared by every coordinate, with no coordinate-independence claim.'],
  'per_component_reason': 'Constant scores have actual coverage1 and fail the strict upper bound1. The singular common-Uniform joint law is exchangeable with continuous Uniform marginals and zero singleton masses, but its scores tie a.s. and its actual calibration coverage is1. Thus continuous marginals alone cannot replace joint a.s. distinctness. For a constant scoring function the page definition C={y:s(x,y)<=q}, with q the same constant maximum, gives all labels directly.'}
]
for g in groups:
    assert set(g['lean_declarations']).issubset(full_declarations)
    g['missing_clauses'] = []

unit_groups = {
 'verification.html::node-1176': [0,1,2,3,4,5],
 'verification.html::node-1180': [0],
 'verification.html::node-1182': [1],
 'verification.html::node-1183': [1],
 'verification.html::node-1184': [2,3,4,5],
}
scope = [
 'Fresh whole decisions apply only to the exact virtual Source55 exercise and five proposed inventory units; current Source53 rows/statuses remain untouched.',
 'The theorem is marginal over the actual exchangeable score law, and over independent seeds when used. No conditional-on-fixed-calibration or per-input guarantee is inferred.',
 'Original-score exchangeability is arbitrary joint permutation invariance. Original scores need not be iid, independent, continuous, or atomless in the tied lower-bound and seeded branches.',
 'The independent iid Uniform seed product is constructed independently of the original vector; almost sure pair distinctness and uniform ranks are derived.',
 'Printed alpha in (0,1), k=ceil((n+1)(1-alpha))<=n and the other-n calibration order statistic are retained. The infinite-threshold k>n case is outside this whole exercise.',
 'The phrase requires gives sufficient hypotheses for the general strict-upper guarantee, not an iff assertion that every tied law violates it. The possibility of inflation by boundary ties is qualitative, not an asserted exact general inflation formula.',
 'The n9 tightness parenthetical describes probability ceiling-rounding tightness, not a universally optimal or smallest prediction set.',
 'No canonical/named compiler execution, current ledger promotion, source write, future selection, aggregate verification, PUB, Git, or deployment execution is claimed.'
]
material = []
for old, new in zip(p['original_current53_entire_units'], p['proposed_source55_entire_units']):
    gs = [groups[ix] for ix in unit_groups[new['key']]]
    material.append({'source_unit_key': new['key'], 'entire_inventory_record': new,
      'original_current53_entire_inventory_record': old,
      'whole_unit_approved': True, 'missing_clauses': [],
      'components': gs, 'hypotheses': sorted(set(h for g in gs for h in g['hypotheses'])),
      'lean_declarations': sorted(set(d for g in gs for d in g['lean_declarations'])),
      'per_unit_reason': 'All clauses of this entire literal were independently read and matched to the listed complete proof bodies and genuine inherited page hypotheses. ' + ' '.join(g['per_component_reason'] for g in gs),
      'scope_limits': scope})

evidence = dict(p['evidence_sha256'])
evidence[str(REQUEST)] = EXPECTED
evidence[str(Path(__file__))] = sha(__file__)
evidence[proposal['primary_original']['file']] = proposal['primary_original']['sha256']
evidence['book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json'] = sha('book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json')
report = {
 'status': 'independent_full_source55_virtual_whole_exercise_and_five_literals_approved',
 'errors': [], 'reviewer': '/root/config21_next (independent of Module author)',
 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
 'request': ref(REQUEST), 'all_45_complete_bodies_and_definitions_read': True,
 'all_public_declarations': full_declarations, 'public_theorem_count': 45,
 'three_complete_actual_sources': p['three_entire_actual_sources'],
 'all_complete_theorem_bodies_and_hypotheses': full_bodies,
 'genuine_successful_standalone_records': p['genuine_successful_standalone_records'],
 'genuine_failed_and_passed_trial_history': history,
 'source55_virtual_exercise': {'key': new_ex['key'], 'entire_inventory_record': new_ex,
   'original_current53_entire_inventory_record': old_ex, 'whole_exercise_approved': True,
   'missing_clauses': [], 'reviewed_components': groups, 'hypotheses': sorted(set(h for g in groups for h in g['hypotheses'])),
   'per_exercise_reason': 'Fresh full question and all four answer clauses, parent and Section5 were read together. Generic distinct exchangeable rank/calibration equality, exact ceiling arithmetic/numeric maximum, actual arbitrary-law seed construction, raw tied event inclusion and consistent randomized membership, plus both genuine tie countermodels close the entire corrected virtual exercise under the explicit page hypotheses.',
   'scope_limits': scope},
 'material_units': material, 'whole_current_source53_exercise_approved': False,
 'original_eight_body_three_answer_peer': p['original_eight_body_three_answer_peer'],
 'original_precision_semantic_and_full29_parser_peer': p['source55_independent_semantic_and_full29_parser_peer'],
 'original_source55_proposal': p['source55_proposal'],
 'entire_original_current_material_rows_and_times': p['original_current_material_rows_and_times'],
 'full_original_parent_and_proposed_parent_read': {'original': proposal['full_original_parent_html_excerpt'], 'proposed': proposal['full_proposed_parent_html_excerpt']},
 'full_original_section5_read': proposal['full_original_section5_html_excerpt'],
 'full_primary_D1_D2_read': {'source': proposal['primary_original'], 'entire_relevant_text': full_primary_d1_d2,
   'correspondence': 'D1 gives iid and weaker joint-exchangeability rank proofs; D2 distinct joint scores control the upper bound. The actual project proof obtains strict ceiling arithmetic and explicitly distinguishes continuous joint/no-ties from merely continuous marginals.'},
 'full_selected_dependency_sources_read': p['selected_actual_source_bodies'],
 'current_selected1167_sources31_assets5_owners_rehashed_exact': True,
 'scope': scope, 'closed_evidence_sha256': evidence,
}
OUT.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'], 'review': ref(OUT), 'units': len(material), 'whole_exercise_approved': True,
 'distinct_public_bodies': len(full_declarations), 'actual_trials': len(history), 'failed_trials': sum(x['actual_failed'] for x in history), 'errors': []}))

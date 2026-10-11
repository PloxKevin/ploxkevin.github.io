from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

R = Path('/home/oxrexkevin/SafetyBased')
B = R / 'book/coverage/checks/modules-future28/current60-pair-bound-v1'
OLD_CAND = B / 'modules28-current60-five-source-pair-bound-candidate-v1.json'
OLD_OFFER = B / 'modules28-current60-five-source-final-offer-v2.json'
OLD_PEER = R / 'book/coverage/checks/future28-core/modules28-current60-final-pair-bound-independent-applied-review-v1.json'
CAND = B / 'modules28-current60-three-stale-gap-repair-candidate-v2.json'
SUPPLEMENT = B / 'modules28-current60-three-stale-gap-completion-associations-v1.json'
OFFER = B / 'modules28-current60-three-stale-gap-repair-offer-draft-v3.json'
READER = Path('/tmp/modules28-current60-three-stale-gap-preparation-reader-v1.json')
HIST = B / 'three-stale-gap-originals-v1'

def H(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p): return {'file': str(Path(p).relative_to(R)), 'sha256': H(p)}
def J(p): return json.loads(Path(p).read_bytes())
def encoded(d): return (json.dumps(d, ensure_ascii=False, indent=2) + '\n').encode()
def canonical(d): return hashlib.sha256(json.dumps(d, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
def put(p, body):
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f: f.write(body)
def putj(p, d): put(p, encoded(d))
def preserve(p):
    p = Path(p); q = HIST / H(p) / p.name
    if q.exists(): assert q.read_bytes() == p.read_bytes()
    else: put(q, p.read_bytes())
    return ref(q)
def safe(n):
    p = R / n
    assert not Path(n).is_absolute() and '..' not in Path(n).parts
    assert p.resolve().is_relative_to(R.resolve()), n
    return p

assert H(OLD_CAND) == '2f1dd93a7f3d80a93954029d847bf286431d2ef919600828e32ee8eda7e2d715'
assert H(OLD_OFFER) == '8803f86a907dd6ef06bda0eceea50ede1be43110053a9abeee02fdee104408a7'
assert H(OLD_PEER) == '551b46799ca996cf2f136c8a0f6cf2b17e56adaccad6dd2ffa107a85eb7c45e6'
for p in [CAND, SUPPLEMENT, OFFER, READER]: assert not p.exists(), p
old = J(OLD_CAND); offer = J(OLD_OFFER); peer = J(OLD_PEER)
assert offer['candidate'] == ref(OLD_CAND) and peer['errors'] == []
inventory = R / 'book/coverage/inventory-after-correction60.json'
assert H(inventory) == '6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
inv = {e['key']: e for e in J(inventory)['exercises']}
originals = {e['inventory_key']: e for e in old['exercises']}
sel = J(R / 'reports/full-coverage/checkpoint-27-selection.json')
assert len(sel['proof_files']) == 1175
net = 'verification/lean/SafeLearning/CompleteModulesNetworks.lean'
assert H(R / net) == sel['proof_files'][net]['sha256']
sources = ['verification/lean/SafeLearning/CompleteModulesPhysicalSensorBox28.lean',
           'verification/lean/SafeLearning/CompleteModulesAffineIBP28.lean']
for n in sources:
    assert H(R / n) == offer['proof_files'][n]['sha256']
    assert len(offer['proof_files'][n]['actual_pair']) == 2
    for row in offer['proof_files'][n]['actual_pair']:
        assert row['actual_record'] and row['raw_log'] and row['source_snapshot']
        native = J(safe(row['actual_record']['file']))
        assert H(safe(row['actual_record']['file'])) == row['actual_record']['sha256']
        assert native['exit_code'] == 0 and native['status'] == 'passed' and row['actual_exit_code'] == 0
requirements = {}
for key in ['lipsdp.html#book-m12-b1', 'verification.html::exercise-15']:
    e = originals[key]
    assert e['status'] == 'complete_math' and e['source_text_sha256'] == inv[key]['text_sha256']
    assert e['source_sha256'] == inv[key]['source_sha256'] == H(R / e['source'])
    assert e['entire_literal_closure28']['whole_exercise_approved'] is True
    for c in e['claims']:
        if c['id'].endswith(('::requirement-3', '::requirement-4')):
            assert c['status'] == 'proved' and c['remaining_gaps'] == []
            p = c['independent_source_review']; assert H(safe(p['file'])) == p['sha256']
            requirements[c['id']] = c
sensor_req = requirements['lipsdp.html#book-m12-b1::requirement-3']
sensor_peer = J(safe(sensor_req['independent_source_review']['file']))
assert sensor_peer['prospective_source59_whole_exercise']['whole_exercise_approved_under_proposed_literal'] is True
assert sensor_peer['prospective_source59_whole_exercise']['entire_proposed_inventory_record'] == inv['lipsdp.html#book-m12-b1']

items = [
    ('lipsdp.html#book-m12-b1', 'lipsdp.html#book-m12-b1::proved-component-1',
     'The exact network global Euclidean and box Lipschitz constants, attainment, and final comparison with.06 remain to be established.',
     ['lipsdp.html#book-m12-b1::proved-component-2', 'lipsdp.html#book-m12-b1::requirement-3', 'lipsdp.html#book-m12-b1::requirement-4'],
     ['two_neuron_max_affine', 'two_neuron_lipschitz_l2', 'exact_l2_slope_attained', 'exact_l2_gain_necessary', 'two_neuron_lipschitz_box', 'physical_correction_box', 'physical_box_bound_attained'],
     ['actual_physical_box_bound', 'actual_hardware_exact_box_error_bound', 'actual_hardware_error_allowance_is_attained_in_one_active_region', 'actual_sdp_and_radius_six_decimal_roundings_and_rejection'],
     'The selected Networks twoNeuron and Sensor normalizedNetwork are exactly the same sum of two ReLUs divided by2; physical normalizedCorrection is twice that sum-normalized network. Networks proves the global Euclidean upper bound sqrt(5/4), its explicit slope witness and the lower necessity for every nonnegative global gain, so the sharp Euclidean constant is closed independently of the conservative SDP4/3. Its all-point box bound3/2 and explicit physical error witness with both coordinate increments1/50 establish sharpness of the normalized box gain3/2. The Sensor actual raw hardware preprocessing proves the same normalized coordinate box, global physical error<=3/50 and attained raw inputs T40->201/5,d3/5->301/500. Thus the non-strict.06 allowance passes exact box analysis. The independently enclosed SDP value remains conservative and strictly greater than.06; no physical violation or whole node976 is inferred.'),
    ('lipsdp.html#book-m12-b1', 'lipsdp.html#book-m12-b1::proved-component-2',
     'The specific conservative SDP-radius value.065320 and hardware scaling-factor approximation remain to be separately enclosed.',
     ['lipsdp.html#book-m12-b1::requirement-3', 'lipsdp.html#book-m12-b1::requirement-4'], [],
     ['actual_sdp_bound_square_and_sign', 'actual_sdp_and_radius_six_decimal_roundings_and_rejection', 'actual_exact_scaling_threshold_is_three_sqrt_six_over_eight', 'actual_scaled_sdp_allowance_iff_exact_threshold', 'actual_exact_threshold_rounds_to_the_source_target', 'actual_scaled_hardware_sdp_bound', 'actual_scaled_hardware_is_sdp_certified_at_the_threshold', 'actual_rounded_denominator_has_a_different_six_decimal_quotient'],
     'Sensor proves the actual positive SDP bound has square8/1875, encloses its six-decimal rounding.065320 and the normalized radius.028284 by strict half-unit bounds, and proves the SDP bound>.06. Genuine scaled raw hardware inequalities imply error<=s*sdpBound for s>=0. The precise threshold is.06 divided by the exact positive SDP bound, equals3sqrt6/8, is sufficient iff s is no larger, and rounds to.918559. The rounded denominator.065320 instead gives.918555 and is explicitly distinguished. The original Source59 conditional full literal is byte-exactly the actual Source60 B1 record, so its corrected exact denominator is now the current literal; the old peer body/time is retained.'),
    ('verification.html::exercise-15', 'verification.html::exercise-15::proved-component-1',
     'The requested shared-input joint-looseness witness still needs explicit association.',
     ['verification.html::exercise-15::requirement-3'], [],
     ['actual_source_matrix_coordinate_action', 'actual_source_center_radius_and_ibp_box', 'actual_source_true_image_iff_diamond', 'actual_source_true_image_is_diamond', 'actual_source_four_vertex_images', 'actual_source_ibp_corner_is_unreachable', 'actual_source_next_affine_layer_overestimates'],
     'Affine uses the exact source matrix[[1,1],[1,-1]], zero bias and common input square[-1,1]^2. It proves the actual image iff |z0|+|z1|<=2 in both directions using the explicit inverse; the four actual input corners have images(+-2,0),(0,+-2). The single box point(2,2) belongs to the actual IBP[-2,2]^2 and is not in that image. For the downstream affine row z0+z1, the actual attained greatest value on the joint image is2 while the IBP box has attained greatest value4. This explicitly associates the shared-input incompatibility with the exercise; it neither assumes joint independence nor asserts generic depth growth.')
]
new = copy.deepcopy(old); new_ex = {e['inventory_key']: e for e in new['exercises']}
associations = []
for key, cid, gap, support_ids, network_names, names, explanation in items:
    e = originals[key]; idx = next(i for i, c in enumerate(e['claims']) if c['id'] == cid)
    c = e['claims'][idx]
    assert c['remaining_gaps'] == [gap] and c['status'] == 'proved'
    source = sources[1] if key.startswith('verification') else sources[0]
    namespace = 'SafeLearning.CompleteModulesAffineIBP28.' if key.startswith('verification') else 'SafeLearning.CompleteModulesPhysicalSensorBox28.'
    declarations = [namespace + n for n in names]
    assert set(declarations) <= set(offer['proof_files'][source]['public_theorem_names'])
    supports = []
    for sid in support_ids:
        sc = next(c for c in e['claims'] if c['id'] == sid)
        assert sc['status'] == 'proved'
        supports.append({'claim_id': sid, 'claim_canonical_json_sha256': canonical(sc), 'lean_declarations': sc['lean_declarations']})
    network_declarations = ['SafeLearning.CompleteModulesNetworks.' + n for n in network_names]
    for n in network_names: assert 'theorem ' + n + ' ' in (R / net).read_text() or 'theorem ' + n + ' :' in (R / net).read_text()
    supporting_req = requirements[support_ids[-1]]
    new_ex[key]['claims'][idx]['remaining_gaps'] = []
    associations.append({'exercise_key': key, 'claim_index': idx, 'claim_id': cid,
       'original_entire_claim': c, 'original_claim_canonical_json_sha256': canonical(c),
       'exact_field_changed': 'remaining_gaps', 'before': [gap], 'after': [],
       'supporting_existing_claims': supports, 'selected_network_declarations': network_declarations,
       'selected_network_source': ref(R / net) if network_names else None,
       'actual_current60_canonical_source': ref(R / source), 'actual_canonical_declarations': declarations,
       'actual_canonical_pair': offer['proof_files'][source]['actual_pair'],
       'original_unchanged_full_source_peer': supporting_req['independent_source_review'],
       'current60_entire_literal': inv[key], 'discharged': True, 'remaining_missing_clauses': [],
       'completion_correspondence': explanation,
       'old_claim_declarations_hypotheses_correspondence_or_status_changed': False})

inverse = copy.deepcopy(new); inv_ex = {e['inventory_key']: e for e in inverse['exercises']}
for a in associations:
    assert inv_ex[a['exercise_key']]['claims'][a['claim_index']]['remaining_gaps'] == []
    inv_ex[a['exercise_key']]['claims'][a['claim_index']]['remaining_gaps'] = a['before']
assert inverse == old and encoded(inverse) == OLD_CAND.read_bytes()
assert new['counts'] == old['counts'] and new['proof_files'] == old['proof_files'] and new['declarations'] == old['declarations']
assert len(associations) == 3 and all(new_ex[a['exercise_key']]['status'] == 'complete_math' for a in associations)
put(CAND, encoded(new))
failure_paths = [R / 'reports/full-coverage' / n for n in [
    'owner28-binding-preflight-execution-v1.json', 'owner28-binding-preflight-execution-v1.log',
    'owner28-isolated-candidate-integrity-diagnostic-v1.json',
    'owner28-candidate-integrity-diagnostic-execution-v1.json', 'owner28-candidate-integrity-diagnostic-execution-v1.log']]
failure_refs = [preserve(p) for p in failure_paths]
diagnostic = J(R / 'reports/full-coverage/owner28-isolated-candidate-integrity-diagnostic-v1.json')
assert diagnostic['integrity_status'] == 'failed' and len(diagnostic['errors']) == 3
supplement = {'status': 'prepared_exact_three_stale_gap_completion_associations_pending_independent_peer', 'errors': [],
    'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'original_candidate': ref(OLD_CAND), 'candidate': ref(CAND),
    'original_final_offer': ref(OLD_OFFER), 'original_full_mapping_peer': ref(OLD_PEER),
    'current60_inventory': ref(inventory), 'associations': associations,
    'inverse': 'Restore exactly the three before remaining_gaps lists at the recorded exercise/claim indices; serialized ensure_ascii=False indent2 plus LF restores the entire original candidate2f1d byte-for-byte.',
    'all_other_candidate_fields_exact': True, 'candidate_counts_unchanged': new['counts'],
    'new_proof_source_count': 5, 'new_public_theorem_count': 153,
    'whole_exercises_unchanged': offer['whole_exercise_keys'], 'whole_material_units_unchanged': offer['whole_material_keys'],
    'new_whole_scope_or_promotion': False, 'whole976_approved': False,
    'genuine_root_preflight_and_integrity_failures_preserved': failure_refs,
    'original_math_peer_body_or_time_changed': False,
    'live_owner_source_selection_compiler_or_publication_action': False, 'coverage_complete': False}
putj(SUPPLEMENT, supplement)
new_offer = copy.deepcopy(offer)
new_offer['status'] = 'prepared_current60_modules28_three_stale_gap_repair_offer_pending_supplemental_independent_peer'
new_offer['candidate'] = ref(CAND)
new_offer['original_reviewed_three_gap_candidate'] = ref(OLD_CAND)
new_offer['original_reviewed_offer_before_three_gap_repair'] = ref(OLD_OFFER)
new_offer['three_stale_gap_completion_associations'] = ref(SUPPLEMENT)
new_offer['supplemental_three_gap_independent_peer'] = None
new_offer['actual_three_gap_candidate_preparation'] = None
required = new_offer['required_evidence_artifacts_sha256']
for p in [CAND, OLD_CAND, OLD_OFFER, OLD_PEER, SUPPLEMENT, R / net]: required[ref(p)['file']] = H(p)
for x in failure_refs: required[x['file']] = x['sha256']
for p in [Path(__file__), Path('/tmp/run-modules28-three-stale-gap-preparation-v1.py')]:
    alias = preserve(p); required[alias['file']] = alias['sha256']; new_offer['original_closed_byte_aliases'][str(p)] = alias
for n, h in required.items(): assert H(safe(n)) == h, n
assert new_offer['proof_files'] == offer['proof_files'] and new_offer['counts'] == offer['counts']
putj(OFFER, new_offer)
putj(READER, {'status': 'passed_exact_three_stale_gap_candidate_author_preparation', 'errors': [],
     'candidate': ref(CAND), 'offer': ref(OFFER), 'completion_associations': ref(SUPPLEMENT),
     'only_three_remaining_gaps_arrays_changed': True, 'entire_inverse_restores_original_candidate_bytes': True,
     'required_durable_refs': len(required), 'original_mapping_peer_unchanged': ref(OLD_PEER),
     'counts': new['counts'], 'proof_metadata_declarations_hypotheses_correspondence_exact': True,
     'canonical_or_owner_or_source_or_selection_or_compiler_written': False, 'coverage_complete': False})
print(json.dumps({'candidate': ref(CAND), 'offer': ref(OFFER), 'completion_associations': ref(SUPPLEMENT), 'closed_refs': len(required)}))

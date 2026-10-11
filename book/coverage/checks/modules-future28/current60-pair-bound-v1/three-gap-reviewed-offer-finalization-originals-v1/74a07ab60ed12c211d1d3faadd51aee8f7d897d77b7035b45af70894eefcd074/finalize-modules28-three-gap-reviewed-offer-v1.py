from pathlib import Path
import copy, hashlib, json
R = Path('/home/oxrexkevin/SafetyBased')
B = R / 'book/coverage/checks/modules-future28/current60-pair-bound-v1'
DRAFT = B / 'modules28-current60-three-stale-gap-repair-offer-draft-v4.json'
PEER = R / 'book/coverage/checks/future28-core/modules28-current60-three-gap-independent-applied-supplemental-review-v1.json'
OUT = B / 'modules28-current60-three-stale-gap-repair-final-offer-v1.json'
READER = Path('/tmp/modules28-current60-three-gap-reviewed-offer-finalization-reader-v1.json')
BASE = B / 'three-gap-reviewed-offer-finalization-originals-v1'
def H(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p): return {'file': str(Path(p).relative_to(R)), 'sha256': H(p)}
def safe(n):
    p = R / n
    assert not Path(n).is_absolute() and '..' not in Path(n).parts and p.resolve().is_relative_to(R.resolve()), n
    return p
def checked(v):
    assert H(safe(v['file'])) == v['sha256']
    return json.loads(safe(v['file']).read_bytes())
def putj(p,d):
    p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('xb') as f: f.write((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
def preserve(p):
    p = Path(p); q = BASE / H(p) / p.name
    q.parent.mkdir(parents=True,exist_ok=True)
    if q.exists(): assert q.read_bytes() == p.read_bytes()
    else:
        with q.open('xb') as f: f.write(p.read_bytes())
    return ref(q)
assert H(DRAFT) == '1a9f9de4e5bd876a1606b31c66dc7d2a0e9b0b17eebf209a28a53929266dc868'
assert H(PEER) == 'b4c704d6111d14c9c815bb36aa6519f562c22e7b66e0957c12528e5103f7bd07'
assert not OUT.exists() and not READER.exists()
draft = json.loads(DRAFT.read_bytes()); peer = json.loads(PEER.read_bytes())
assert peer['status'] == 'passed_independent_exact_modules28_current60_three_gap_supplemental_candidate_mechanics' and peer['errors'] == []
assert peer['candidate'] == draft['candidate'] and peer['offer'] == ref(DRAFT)
assert peer['three_stale_gap_completion_associations'] == draft['three_stale_gap_completion_associations']
assert peer['original_full_pair_bound_candidate_peer'] == draft['final_independent_candidate_mapping_peer']
assert len(peer['component_gap_associations']) == 3 and all(a['approved_discharge'] is True and a['missing_clauses'] == [] for a in peer['component_gap_associations'])
assert peer['exact_forward_and_byte_inverse'] is True and peer['whole976_approved'] is False
assert (peer['new_source_count_unchanged'],peer['new_public_theorem_count_unchanged'],peer['actual_existing_canonical_pairs_unchanged'],peer['whole_exercise_count_unchanged'],peer['whole_material_count_unchanged']) == (5,153,10,4,26)
candidate = checked(draft['candidate']); old = checked(draft['original_reviewed_three_gap_candidate'])
supplement = checked(draft['three_stale_gap_completion_associations']); inverse = copy.deepcopy(candidate)
exercises = {e['inventory_key']:e for e in inverse['exercises']}
for a in supplement['associations']:
    c = exercises[a['exercise_key']]['claims'][a['claim_index']]
    assert c['id'] == a['claim_id'] and c['remaining_gaps'] == []
    c['remaining_gaps'] = a['before']
assert inverse == old
assert (json.dumps(inverse,ensure_ascii=False,indent=2)+'\n').encode() == safe(draft['original_reviewed_three_gap_candidate']['file']).read_bytes()
native = checked(peer['actual_finalizer'])
assert type(native['actual_exit_code']) is int and native['actual_exit_code'] == 0 and native['status'] == peer['expected_actual_finalizer_status'] and native['protection_errors'] == []
assert native['actual_command'] == peer['expected_actual_finalizer_command']
assert native['helper_sha256_before'] == native['helper_sha256_after'] == peer['expected_actual_finalizer_helpers_sha256']
for original, alias in peer['actual_finalizer_original_byte_aliases'].items():
    assert H(safe(alias['file'])) == alias['sha256']
    assert alias['sha256'] == (native['log_sha256'] if original == native['log'] else native['helper_sha256_before'][original])
out = copy.deepcopy(draft)
out['status'] = 'passed_current60_modules28_five_source_actual_pair_offer_with_independently_reviewed_three_stale_gap_repair'
out['original_full_pair_bound_candidate_peer'] = draft['final_independent_candidate_mapping_peer']
out['original_full_pair_bound_mapping_actual'] = draft['final_independent_mapping_actual']
out['final_independent_candidate_mapping_peer'] = ref(PEER)
out['final_independent_mapping_actual'] = peer['actual_finalizer']
out['supplemental_three_gap_independent_peer'] = ref(PEER)
out['original_supplemental_reviewed_three_gap_offer'] = ref(DRAFT)
out['three_gap_finalization_scope'] = 'Composes exact original full551b five-source pair mapping and original math body/time with the new independent full three-gap association/inverse decision. Only three inherited remaining_gaps lists change; source proofs, counts, hypotheses, correspondence, declarations, original reviewer times and all other candidate fields remain exact. Root installation/selection/audit/publication remain separate.'
required = out['required_evidence_artifacts_sha256']
required.update(peer['closed_evidence_sha256'])
for p in [PEER,DRAFT]: required[ref(p)['file']] = H(p)
out['original_closed_byte_aliases'].update(peer['original_closed_byte_aliases'])
for p in [Path(__file__),Path('/tmp/run-modules28-three-gap-reviewed-offer-finalization-v1.py')]:
    alias = preserve(p); required[alias['file']] = alias['sha256']; out['original_closed_byte_aliases'][str(p)] = alias
for n,h in required.items(): assert H(safe(n)) == h,n
for alias in out['original_closed_byte_aliases'].values(): assert H(safe(alias['file'])) == alias['sha256']
assert out['candidate'] == peer['candidate'] and out['proof_files'] == draft['proof_files'] and out['counts'] == draft['counts']
putj(OUT,out)
putj(READER,{'status':'passed_exact_modules28_independently_reviewed_three_gap_offer_finalization','errors':[],
    'candidate':out['candidate'],'offer':ref(OUT),'supplemental_peer':ref(PEER),'actual_independent_reader':peer['actual_finalizer'],
    'only_three_candidate_gap_fields_changed':True,'entire_byte_inverse_2f1d':True,'all_original_math_and551b_peer_body_times_exact':True,
    'required_root_evidence_count':len(required),'original_closed_alias_count':len(out['original_closed_byte_aliases']),
    'counts_unchanged':out['counts'],'whole976_approved':False,'owner_source_selection_compiler_or_publication_written':False,'coverage_complete':False})
print(json.dumps({'offer':ref(OUT),'candidate':out['candidate'],'supplemental_peer':ref(PEER),'closed_refs':len(required)}))

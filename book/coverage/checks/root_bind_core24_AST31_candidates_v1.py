"""Bind two actual Core24 compiler commands to the preserved AST candidates."""
from pathlib import Path
import copy, hashlib, json

ROOT = Path(__file__).resolve().parents[3]
OLD = 'book/coverage/checks/future31-core/Core15NF-Applied21proof1NF-candidates-v1/draft-offer-v1.json'
OLD_SHA = 'd5d8b4385ecd50e7e861d1f71542e7322aa7180daa393b077efc0f8bf09217b0'
READY = 'book/coverage/checks/future31-core/current81-canonical-pairs6-v1/actual-reviewed31-canonical-paired-readiness-v1.json'
READY_SHA = 'c18752bbf4b29ef8218cb28d990aad7edfcf0220babe2bacbafb3101bde43520'
NATIVE = 'reports/full-coverage/current81-canonical31-six-paired-application-execution-v1.json'
SOURCE = 'verification/lean/SafeLearning/CompleteCoreFilippovEulerConstruction31.lean'
OUT = ROOT/'book/coverage/checks/future31-core/Core24-Core15NF-Applied21proof1NF-final-candidates-v2'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file': str(p.relative_to(ROOT)), 'sha256': sha(p), 'bytes': p.stat().st_size}
def checked(r):
    p = ROOT/r['file']; assert p.is_file() and not p.is_symlink() and sha(p) == r['sha256']
    return p
def read(p): return json.loads(p.read_bytes())
def encode(d): return (json.dumps(d, indent=2, ensure_ascii=False)+'\n').encode()
def new(p, data):
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f: f.write(data)

assert not OUT.exists() and sha(ROOT/OLD) == OLD_SHA and sha(ROOT/READY) == READY_SHA
offer, ready, native = read(ROOT/OLD), read(ROOT/READY), read(ROOT/NATIVE)
assert ready['status'] == 'passed_actual_reviewed31_canonical_standalone_and_named_pairs_unselected' and ready['errors'] == []
assert native['status'] == 'passed' and native['actual_exit_code'] == 0
assert sha(ROOT/native['log']) == native['log_sha256']
assert native['helper_sha256_before'] == native['helper_sha256_after']
row = next(r for r in ready['sources'] if r['canonical_source'] == SOURCE)
pairs = [r for r in ready['actual_paired_records'] if r['source']['file'] == SOURCE]
assert len(pairs) == 2 and {r['kind'] for r in pairs} == {'standalone', 'named'} and row['public_theorem_count'] == 24
evidence = {}
for pair in pairs:
    assert pair['actual_exit_code'] == 0 and pair['source']['sha256'] == row['original_tmp_source']['sha256'] == sha(ROOT/SOURCE)
    for key in ['actual_record', 'raw_log', 'source_snapshot']:
        r = pair[key]; checked(r); evidence[r['file']] = r['sha256']
    actual = read(checked(pair['actual_record']))
    assert actual['exit_code'] == 0 and actual['source_sha256_before'] == actual['source_sha256_after'] == sha(ROOT/SOURCE)
base_path = checked(offer['candidates']['core']); old = read(base_path); core = copy.deepcopy(old)
assert SOURCE not in core['proof_files']
core['proof_files'][SOURCE] = {'sha256': sha(ROOT/SOURCE), 'theorem_count': 24,
    'public_theorem_names': [r['name'] for r in row['public_declarations'] if r['kind'] in ['theorem', 'lemma']],
    'public_names': [r['name'] for r in row['public_declarations']], 'actual_pair': pairs,
    'evidence_sha256': evidence, 'actual_root12_primary_native': ref(ROOT/NATIVE), 'actual_root6_readiness': ref(ROOT/READY),
    'original_math_peers': row['independent_source_peers'],
    'component_only_source_association': {'exercise': 'barriers.html::exercise-16', 'whole_exercise_approved': False,
        'scope': 'Actual essential-convexified velocity compactness and local upper hemicontinuity, plus finite Euler nodes and bounds under stated ProperSpace/full-support/global-bound hypotheses. No measurable selector, polygonal limit or integral-curve existence theorem is claimed.'},
    'scope': 'Actual24 full-source theorem bodies with standalone/named0 and full-prefix/six-body independent peer. Aggregate kernel/axiom verification and raw owner installation are separate.'}
core['counts']['proof_files'] = len(core['proof_files'])
core['future31_actual_canonical_binding'] = {'status': 'candidate_only_Core24_real_two_command_pair_no_whole_exercise_promotion', 'readiness': ref(ROOT/READY), 'primary_native': ref(ROOT/NATIVE), 'new_sources': [SOURCE], 'new_public_theorems': 24, 'new_public_names': len(row['public_declarations']), 'original_AST_candidate': ref(base_path), 'raw_installed_owner_mutation': False, 'coverage_complete': False}
inverse = copy.deepcopy(core); inverse['proof_files'].pop(SOURCE); inverse.pop('future31_actual_canonical_binding'); inverse['counts']['proof_files'] = old['counts']['proof_files']
assert inverse == old
assert next(r for r in core['exercises'] if r['inventory_key'] == 'barriers.html::exercise-16') == next(r for r in old['exercises'] if r['inventory_key'] == 'barriers.html::exercise-16')
OUT.mkdir(parents=True)
new(OUT/'core-candidate.json', encode(core))
result = {'status': 'prepared_current81_Core24_actual_pairs_Core15NF_Applied21proved1NF_final_candidates_only', 'original_draft_offer': ref(ROOT/OLD), 'helper': ref(Path(__file__)), 'candidates': {**offer['candidates'], 'core': ref(OUT/'core-candidate.json')}, 'promotions': offer['promotions'], 'AST_exact_inverse': offer['inverse'], 'Core24_metadata_inverse': {'original_core_AST_candidate': ref(base_path), 'remove_proof_source': SOURCE, 'remove_metadata': 'future31_actual_canonical_binding', 'restore_proof_count': old['counts']['proof_files'], 'decoded_entire_original_restored': True}, 'real_canonical_readiness': ref(ROOT/READY), 'real_primary_execution': ref(ROOT/NATIVE), 'core_exercise16_entire_body_status_and_claims_unchanged': True, 'coverage_complete': False}
new(OUT/'final-offer-v2.json', encode(result))
print(json.dumps({'status': result['status'], 'offer': ref(OUT/'final-offer-v2.json'), 'new_Core_theorems': 24, 'existing_App_proofs_reused': 21, 'pure_NF_leaves': 16, 'coverage_complete': False}))

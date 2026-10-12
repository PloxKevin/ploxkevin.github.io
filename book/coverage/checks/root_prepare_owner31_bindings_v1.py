"""Bind the exact five candidates named by three completed mapping approvals."""
from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT/'book/coverage/checks/future31-core/owner31-exact-reviewed-bindings-v1.json'
CORE = 'book/coverage/checks/future31-core/Core-Applied-promotions31-final2-independent-foundations-v1/Core24-Core15NF-Applied21proof1NF-promotions31-current81-final2-full-mapping-independent-foundations31-closed-peer-v1.json'
FOUND = 'book/coverage/checks/future31-core/foundations31-real8-final-mapping-independent-modules-v1/foundations31-current81-four-source-real8-five-whole-disjoint-inverse-full-mapping-independent-modules31-closed-peer-v1.json'
MODULE = 'book/coverage/checks/future31-core/modules31-final3-independent-foundations-v1/modules31-current81-Integral39-AST19-real2-pair-full-final3-mapping-independent-foundations31-closed-peer-v1.json'
PINS = {CORE: '5fcbc943dfa418d3c0063b95626492db2d7474ebba77db94a8b9940d5d531a0a', FOUND: 'daa74af3374a3b7f59095faeff906b88fd7903874d1e19262737d8e7a71a3b29', MODULE: '84c43a14235502619310155020700e4a752a16343e06110f4e829dd7d049bff3'}
def sha(n): return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def ref(n): return {'file': n, 'sha256': sha(n), 'bytes': (ROOT/n).stat().st_size}
def read(n): return json.loads((ROOT/n).read_bytes())
assert not OUT.exists()
peers = {}
for n, h in PINS.items():
    assert sha(n) == h; d = read(n); assert d['status'].startswith('passed') and d['errors'] == []; peers[n] = d
rows = []
specs = [
 ('core', CORE, ['candidate_refs', 'core'], ['full_changed_Core15_NF_Applied21_proved_and_one_NF_rows_and_contexts_read', 'Core24_to_AST_candidate_and_AST_candidates_to_whole_original_owner30_inverses_verified', 'CoreEx16_whole_false_and_integral_curve_existence_gap_unchanged']),
 ('applied', CORE, ['candidate_refs', 'applied'], ['full_changed_Core15_NF_Applied21_proved_and_one_NF_rows_and_contexts_read', 'both_full_owner_forward_inverse_and_full_original_raw_SHA_refs_verified', 'two_specific_Applied_AST_children1531_359_still_pending_unchanged']),
 ('applied-promotions', CORE, ['promotions_candidate'], ['all22_promotions_exact_mirrors_and_every_other_entry_unchanged']),
 ('foundations', FOUND, ['candidate'], ['all_full_mapping_approved', 'independent_final_mapping_approved', 'full_forward_and_reverse_JSONpatch_checked', 'entire_original_owner30_UTF8_bytes_recovered']),
 ('modules', MODULE, ['candidate'], ['strict_full_forward_and_reverse_with_all_intermediate_test_assertions_verified', 'whole_original_owner30_byte_inverse_verified', 'current_full_Exercise19_and_four_literals_only_approved_in_exact_prior_peer_domains', 'all19_individual_NF_leaves_full_local_contexts_and_prior_exact_peer_decisions_read']),
]
for owner, peer_file, keys, true_fields in specs:
    d = peers[peer_file]; candidate = d
    for key in keys: candidate = candidate[key]
    assert sha(candidate['file']) == candidate['sha256']
    assert all(d[k] is True for k in true_fields)
    rows.append({'destination': f'book/coverage/{owner}.json', 'before_sha256': sha(f'book/coverage/{owner}.json'), 'candidate': candidate, 'independent_mapping_peer': ref(peer_file), 'expected_peer_status': d['status'], 'peer_candidate_pointer': keys, 'required_true_peer_fields': [[k] for k in true_fields]})
result = {'status': 'exact_source81_five_owner31_reviewed_candidate_byte_bindings_only', 'replacements': rows, 'helper': ref(str(Path(__file__).relative_to(ROOT))), 'coverage_complete': False}
OUT.parent.mkdir(parents=True, exist_ok=True)
with OUT.open('x') as f: f.write(json.dumps(result, indent=2)+'\n')
print(json.dumps({'status': result['status'], 'bindings': ref(str(OUT.relative_to(ROOT))), 'candidates': 5, 'coverage_complete': False}))

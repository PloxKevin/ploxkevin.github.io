#!/usr/bin/env python3
"""Fresh cumulative review extending the historical six packet candidate."""
from pathlib import Path
from datetime import datetime, timezone
import json
import re
import tempfile
from review_six_qualifier_cumulative_v1 import ROOT, OUT, INDEX, ref, exact, read_json, sha_bytes, literal_fields, run_inventory

SIX_PATH = OUT / 'independent-six-qualifier-cumulative-review-v1.json'
ROOT_PEER = ROOT / 'book/coverage/checks/checkpoint33-root/planar7-full-source-mathematical-review-v1.json'
ROOT_PEER_SHA = 'b3e0305ecaf40d8fa621e7fb339f8b927d44a203c65cb86c5b410e640c293b3b'


def main():
    destination = OUT / 'independent-seven-qualifier-cumulative-review-v1.json'
    assert not destination.exists()
    six = json.loads(SIX_PATH.read_bytes())
    index = json.loads(INDEX.read_bytes())
    offer = read_json(index['authoritative_indexes']['six_qualifier_offer'])
    planar = index['outstanding_correspondence'][0]
    root_peer = read_json({'file': str(ROOT_PEER), 'sha256': ROOT_PEER_SHA})
    assert root_peer['errors'] == [] and root_peer['prospective_whole529_mathematically_approved']
    assert root_peer['source'] == planar['source']
    request = read_json(planar['author_request'])
    source_text = exact(planar['source']).read_text()
    assert root_peer['exact_replacements'] == [planar['exact_planned_wording_substitution']]
    names = request['public_theorem_names']
    assert len(names) == 7
    for name in names:
        assert re.search(r'\btheorem\s+' + re.escape(name.rsplit('.', 1)[1]) + r'\b', source_text)
    assert 'Matrix (Fin 2) (Fin 2) ℝ' in source_text
    assert '(hP : P.PosSemidef) (hn : P≠0) (hd : P.det=0)' in source_text
    assert '0<a ∧ ∀ x : Fin 2 → ℝ' in source_text
    assert 'oneLevel 0=∅' in source_text
    before_inventory = read_json(offer['baseline_Source81_inventory'])
    original = {}
    cumulative = {}
    substitutions = []
    for packet in offer['packets']:
        source = packet['source']
        raw = exact(packet['immutable_current_source']).read_bytes()
        original[source] = raw
        cumulative.setdefault(source, raw)
        assert sha_bytes(cumulative[source]) == packet['cumulative_preview_before_sha256']
        for replacement in packet['raw_exact_replacements']:
            old, new = replacement['before'].encode(), replacement['after'].encode()
            assert cumulative[source].count(old) == 1
            cumulative[source] = cumulative[source].replace(old, new, 1)
            substitutions.append({'family': packet['family'], 'source': source, **replacement})
        assert sha_bytes(cumulative[source]) == packet['cumulative_preview_after_sha256']
    for source, raw in cumulative.items():
        assert raw == exact(six['exact_candidate_pages'][source]).read_bytes()
    linalg = 'SafeLearning/primer-linalg.html'
    replacement = planar['exact_planned_wording_substitution']
    old, new = replacement['before'].encode(), replacement['after'].encode()
    assert cumulative[linalg].count(old) == original[linalg].count(old) == 1
    planar_only = original[linalg].replace(old, new, 1)
    assert planar_only == exact(planar['prospective_page']).read_bytes()
    cumulative[linalg] = cumulative[linalg].replace(old, new, 1)
    substitutions.append({'family': 'PlanarQuadratic7', 'source': linalg, **replacement})
    assert len(substitutions) == 10
    inverse = dict(cumulative)
    for item in reversed(substitutions):
        source = item['source']
        old, new = item['before'].encode(), item['after'].encode()
        assert inverse[source].count(new) == 1
        inverse[source] = inverse[source].replace(new, old, 1)
    assert inverse == original
    candidates = {}
    physical_lines = {}
    for source, raw in cumulative.items():
        previous = original[source].decode()
        final = raw.decode()
        assert re.findall(r'<[^>]*>', previous) == re.findall(r'<[^>]*>', final)
        assert re.findall(r'<script\b[^>]*>.*?</script>', previous, re.S | re.I) == re.findall(r'<script\b[^>]*>.*?</script>', final, re.S | re.I)
        old_lines, new_lines = previous.splitlines(keepends=True), final.splitlines(keepends=True)
        assert len(old_lines) == len(new_lines)
        physical_lines[source] = [i + 1 for i, (a, b) in enumerate(zip(old_lines, new_lines)) if a != b]
        path = OUT / 'exact-seven-cumulative-candidate' / source
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        candidates[source] = ref(path)
    trees = {label: Path(tempfile.mkdtemp(prefix=f'checkpoint33-{label}-full29-', dir='/tmp'))
             for label in ('planar-only', 'seven-candidate')}
    for tree in trees.values():
        (tree / 'SafeLearning').mkdir()
        (tree / 'book').mkdir()
    current_inputs = []
    pages = sorted((ROOT / 'SafeLearning').glob('*.html'))
    assert len(pages) == 29
    for page in pages:
        source = str(page.relative_to(ROOT))
        raw = page.read_bytes()
        assert sha_bytes(raw) == before_inventory['source_sha256'][source]
        current_inputs.append(ref(page))
        (trees['planar-only'] / source).write_bytes(planar_only if source == linalg else raw)
        (trees['seven-candidate'] / source).write_bytes(cumulative.get(source, raw))
    for tree in trees.values():
        for name in ('inventory_claims.py', 'validate.py'):
            (tree / 'book' / name).write_bytes((ROOT / 'book' / name).read_bytes())
    isolated, isolated_native = run_inventory(trees['planar-only'], 'planar-only')
    candidate, candidate_native = run_inventory(trees['seven-candidate'], 'seven-candidate')
    assert isolated['counts'] == candidate['counts'] == before_inventory['counts']
    diffs = {}
    records = {}
    for kind in ('exercises', 'material_source_units'):
        base = {row['key']: row for row in before_inventory[kind]}
        one = {row['key']: row for row in isolated[kind]}
        full = {row['key']: row for row in candidate[kind]}
        assert base.keys() == one.keys() == full.keys()
        diffs[kind] = {
            'isolated_planar': sorted(k for k in base if literal_fields(base[k]) != literal_fields(one[k])),
            'cumulative_seven': sorted(k for k in base if literal_fields(base[k]) != literal_fields(full[k]))}
        for key in full:
            assert full[key]['source_sha256'] == candidate['source_sha256'][full[key]['source']]
        if kind == 'material_source_units':
            records = full
    expected_keys = sorted([*index['changed_literal_keys'], planar['target']['key']])
    assert diffs == {
        'exercises': {'isolated_planar': [], 'cumulative_seven': []},
        'material_source_units': {'isolated_planar': [planar['target']['key']], 'cumulative_seven': expected_keys}}
    current529 = next(row for row in before_inventory['material_source_units'] if row['key'] == planar['target']['key'])
    prospective529 = records[planar['target']['key']]
    assert current529 == request['entire_current_literal'] == root_peer['entire_current_literal']
    assert literal_fields(prospective529) == literal_fields(request['exact_planned_prospective_domain_qualified_literal']) == literal_fields(root_peer['entire_prospective_literal'])
    for key in index['changed_literal_keys']:
        old = offer['entire_current_and_cumulative_prospective_changed_literals'][key]['entire_cumulative_prospective']
        assert literal_fields(records[key]) == literal_fields(old)
    for source, fingerprint in before_inventory['source_sha256'].items():
        if source not in cumulative:
            assert candidate['source_sha256'][source] == fingerprint
    mappings = json.loads(json.dumps(six['whole_statement_mappings_conditional_on_exact_application_and_canonical_audit']))
    for mapping in mappings:
        mapping['entire_candidate_literal'] = records[mapping['key']]
    mappings.append({'key': planar['target']['key'], 'family': 'PlanarQuadratic7',
        'existing_pending_claim_ids': planar['target']['pending_claim_ids'],
        'entire_candidate_literal': prospective529,
        'source': planar['source'], 'public_theorem_names': names,
        'whole_mathematical_peer': ref(ROOT_PEER),
        'exact_replacement': replacement,
        'reused_diagonal_PSD_clause': root_peer['reused_diagonal_PSD_clause'],
        'hypotheses': root_peer['hypotheses'],
        'narrow_qualification_decision': 'approved',
        'conditional_on_exact_source_application_and_canonical_audit': True})
    assert len(mappings) == 10
    replacements_path = OUT / 'exact-ten-replacements-and-inverse-v1.json'
    replacements_path.write_text(json.dumps({'forward': substitutions,
        'inverse': [{'family': r['family'], 'source': r['source'], 'before': r['after'], 'after': r['before']}
                    for r in reversed(substitutions)], 'exact_byte_inverse': True}, indent=2) + '\n')
    report = {'schema_version': 1,
        'status': 'approved_independent_Planar7_narrow_qualification_and_seven_packet_ten_replacement_cumulative_composition',
        'errors': [], 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
        'historical_six_packet_review_preserved_exact': ref(SIX_PATH),
        'original_six_offer': index['authoritative_indexes']['six_qualifier_offer'],
        'additional_Planar_full_mathematical_peer': ref(ROOT_PEER),
        'additional_Planar_exact_source': planar['source'],
        'additional_Planar_original_request': planar['author_request'],
        'additional_Planar_individual_candidate': planar['prospective_page'],
        'full_current_and_proposed529_literals': {'current': current529, 'cumulative_prospective': prospective529},
        'narrow_mathematical_assessment': {
            'preceding_context': 'Real symmetric quadratic forms are explicitly established in the preceding definition. The qualifier restricts only the final conic-classification sentence to the plane; the generic finite diagonal PSD equivalence remains intact.',
            'plane': 'All conic classification theorems use actual Fin2 coordinates; invertible orthogonal spectral coordinates preserve the planar geometry.',
            'positive_definite': 'Both eigenvalues and semiaxes are strictly positive, yielding the all-input ellipse equation.',
            'nonzero_singular_PSD': 'det=0 and nonzero PSD imply exactly one zero and one positive eigenvalue. Positive a yields the two distinct parallel affine lines y_i=+a and y_i=-a.',
            'zero_exception': 'The zero quadratic form never equals1; oneLevel zero is empty. This excludes the rankzero matrix from the parallel-lines clause.',
            'indefinite': 'The primitive real symmetric indefinite predicate derives opposite-sign eigenvalues; normalized orthogonal coordinates yield the all-input hyperbola equation.',
            'exact_fixtures': 'The printed positive-entry indefinite example, rankone PSD example and diagonal equivalence clauses are unchanged.',
            'full_supporting_source': 'All7 public, all3 private bodies and all3 definitions inspected for this narrow domain correspondence; no new compilation asserted.',
            'decision': 'approved_exact_single_qualifier'},
        'exact_candidate_pages': candidates, 'exact_replacements': ref(replacements_path),
        'fresh_isolated_Planar_full29_parser': isolated_native,
        'fresh_seven_cumulative_full29_parser': candidate_native,
        'counts_unchanged': candidate['counts'], 'all29_current_Source81_inputs': current_inputs,
        'exact_changed_physical_inventory_records': diffs, 'changed_source_lines': physical_lines,
        'whole_two_page_exact_byte_inverse': True,
        'tags_attributes_script_bytes_and_line_counts_unchanged': True,
        'all_other27_page_bytes_and_unaffected_literal_fields_exact': True,
        'no_exercise_statement_changed': True,
        'whole_statement_mappings_conditional_on_exact_application_and_canonical_audit': mappings,
        'approved_prospective_whole_keys': sorted(m['key'] for m in mappings),
        'carried_18_Basics_component_rebase_authority': ref(OUT / 'independent-18-carried-basics-component-rebase-v1.json'),
        'node311_context': {**six['node311_context'], 'entire_candidate_literal': records['primer-linalg.html::node-311']},
        'node922': {**six['node922'], 'entire_candidate_literal': records['primer-basics.html::node-922']},
        'current_pages_owners_inventory_proof_selection_publication_mutated': False,
        'new_Lean_compile_or_aggregate_audit_claimed': False, 'coverage_complete': False}
    destination.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'decision': report['status'], 'report': ref(destination),
                     'candidates': candidates, 'wholes': report['approved_prospective_whole_keys']}))


if __name__ == '__main__':
    main()

from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, sys, re

R = Path('/home/oxrexkevin/SafetyBased')
D = R / 'book/coverage/checks/future29-foundations/reference3-independent-modules-v1'
Q = R / 'book/coverage/checks/future28-foundations/editorial-reference3-prospective29-v2/foundations-editorial-reference3-full-literal-classification-request29-v2.json'
sys.path.insert(0, str(R / 'book'))
from validate import Document, clean_text

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def checked(ref):
    p = R / ref['file']
    assert p.resolve().is_relative_to(R.resolve()), ref
    assert sha(p) == ref['sha256'], ref
    return p

def ref(p):
    return {'file': str(p.relative_to(R)), 'sha256': sha(p)}

assert sha(Q) == '8a8bf96f3af9311e1efcf5a2fbde19b05f61e8bbadf8fb2d57986a0aff248f85'
q = json.loads(Q.read_bytes())
context = json.loads(checked(q['guard_context']).read_bytes())
def guard():
    for field in ['pins_sha256', 'held_current_source_sha256', 'owners_sha256']:
        for name, h in context[field].items():
            assert sha(Path(name) if Path(name).is_absolute() else R / name) == h, name
    return {k: context[k] for k in ['pins_sha256', 'held_current_source_sha256', 'owners_sha256']}

before = guard()
for name, h in q['required_evidence_artifacts_sha256'].items():
    checked({'file': name, 'sha256': h})
for original, r in q['exact_original_byte_aliases'].items():
    checked(r)
inv = json.loads(checked(q['current_inventory']).read_bytes())
units = {u['key']: u for u in inv['material_source_units']}
owner = json.loads(checked(q['original_entire_owner28']).read_bytes())
contexts = json.loads(checked(q['all24_complete_linked_sections']).read_bytes())
assert len(contexts) == 3 and sum(len(c['links']) for c in contexts) == 24
expected = ['primer-basics.html::node-1179', 'primer-optimization.html::node-380', 'primer-optimization.html::node-738']
assert [r['source_unit_key'] for r in q['individual_full_literal_proposed_decisions']] == expected
decisions = []
for row, linked in zip(q['individual_full_literal_proposed_decisions'], contexts):
    u = units[row['source_unit_key']]
    assert row['entire_source_unit'] == linked['entire_literal'] == u
    assert owner['material_claims'][row['original_pending_owner_row_index']] == row['original_entire_pending_owner_row']
    assert row['original_entire_pending_owner_row']['status'] == 'pending'
    source = R / u['source']
    assert sha(source) == u['source_sha256']
    node = Document(source.read_text()).nodes[int(u['locator'].removeprefix('::node-')) - 1]
    assert node.text() == u['source_text']
    assert hashlib.sha256(node.text().encode()).hexdigest() == u['text_sha256']
    assert [n.attrs['href'] for n in node.descendants('a')] == [p['href'] for p in row['exact_linked_topic_passages']]
    assert len(linked['links']) == len(row['exact_linked_topic_passages'])
    for topic, full in zip(row['exact_linked_topic_passages'], linked['links']):
        assert topic['href'] == full['href']
        p = checked(topic['source'])
        assert str(p.relative_to(R)) == full['source']
        assert sha(p) == full['source_sha256'] == inv['source_sha256'][full['source']]
        assert (topic['complete_section_line_start'], topic['complete_section_line_end_inclusive']) == (full['line_start'], full['line_end'])
        fragment = ''.join(p.read_text().splitlines(keepends=True)[full['line_start'] - 1:full['line_end']])
        assert fragment == full['entire_linked_section_html']
        hits = []
        pat = topic['topic_regex_used_for_reader_index_only']
        for n in Document(fragment).nodes:
            if n.tag not in ['p', 'li', 'div'] or not re.search(pat, clean_text(n.text()), re.I):
                continue
            if any(k.tag in ['p', 'li', 'div', 'details', 'section', 'table'] and re.search(pat, clean_text(k.text()), re.I) for k in n.descendants()):
                continue
            hits.append({'tag': n.tag, 'line': full['line_start'] + n.line - 1, 'exact_text': n.text(), 'text_sha256': hashlib.sha256(n.text().encode()).hexdigest()})
        assert hits == topic['entire_matching_topic_nodes'], topic['href']
    assert row['proposed_classification'] == 'not_a_formal_claim'
    assert not row['formal_math_or_exercise_coverage_approval_claimed']
    decisions.append({'source_unit_key': row['source_unit_key'], 'entire_literal': u, 'classification': 'not_a_formal_claim', 'approved': True, 'missing_clauses': [], 'reason': row['individual_scope_reason'], 'exact_topic_passage_refs': row['exact_linked_topic_passages']})

b2 = q['parseval_exercise_B2_disambiguation']
assert b2['entire_existing_exercise_row'] == next(e for e in owner['exercises'] if e['inventory_key'] == 'primer-optimization.html::exercise-30')
assert b2['entire_existing_exercise_row']['status'] == 'complete_math'
for r in b2['selected_sources']:
    checked(r)
assert q['new_proof_or_exercise_or_whole_math_promotion_count'] == 0
assert guard() == before
result = {
    'status': 'passed_independent_three_exact_curricular_reference_full_literal_classification',
    'errors': [], 'reviewer': '/root/modules_finish28', 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
    'request': ref(Q), 'individual_full_literal_decisions': decisions,
    'all24_complete_linked_section_byte_bindings': q['all24_complete_linked_sections'],
    'all24_full_matched_topic_passages_read': True,
    'linked_section_complete_bytes_verified_without_whole_section_math_approval': True,
    'specific_scope_findings': [
        '1179 names topology and attainment topics; compactness, regularity and feasibility qualifications belong to the exact linked passages. No new theorem is asserted by this curricular row.',
        '380 names matrix-calculus applications. Its beta(WW^T-I)W identifies the independently inventoried Primer B Exercise B.2, not Module13 B.2. The original exercise status and proof bytes are retained without a fresh whole-exercise approval.',
        '738 names curvature and monotonicity topics. Its PSD-Hessian reference includes the explicit warning that coordinatewise second-derivative constraints do not imply multidimensional convexity; the row states no such implication.'
    ],
    'prior_true_author_preparation_failure_retained': q['prior_true_preparation1_failure'],
    'original_pending_rows_retained_by_exact_request_reference': True,
    'required_evidence_artifacts_sha256': q['required_evidence_artifacts_sha256'],
    'scope': 'Only three exact reference rows. No linked theorem, exercise, entire section, citation or temporal claim is promoted. Prospective classifications only; no live owner mutation.',
    'whole_math_or_exercise_promotion_count': 0, 'coverage_complete': False,
    'actual_finalizer': None
}
assert not D.exists()
D.mkdir(parents=True)
out = D / 'foundations-reference3-full-literal-independent-modules29-peer-v1.json'
out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
assert guard() == before
print(json.dumps({'peer': ref(out), 'individual_classifications': 3, 'topic_links': 24, 'errors': []}))

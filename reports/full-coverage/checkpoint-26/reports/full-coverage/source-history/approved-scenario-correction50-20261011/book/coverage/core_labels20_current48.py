"""Map the 78 individually reviewed nonformal literals through exact47 identities."""
import json
from core_identity48 import current_review, verify_identity

def integrate(root, inventory, sha, direct_material):
    original = 'book/coverage/checks/future20-core/core-instructional-label-material-batch2-source44-independent-applied-review20-v2.json'
    name = str(current_review(root, root/original, sha).relative_to(root))
    review = json.loads((root/name).read_text())
    verify_identity(root, review, root/name, sha)
    assert review['inventory_sha256'] == sha(review['inventory']) == sha('book/coverage/inventory.json')
    assert not review['proof_source_sha256'] and not review['actual_standalone_evidence'] and not review['missing_clauses']
    assert sha(review['candidate']) == review['candidate_sha256']
    candidate = json.loads((root/review['candidate']).read_text())
    rows = {r['source_unit_key']: r for r in candidate['material_units']}
    units = {r['key']: r for r in inventory['material_source_units']}
    assert len(review['material_units']) == len(rows) == 78
    assert {r['source_unit_key'] for r in review['material_units']} == set(rows)
    for row in review['material_units']:
        key = row['source_unit_key']
        unit = units[key]
        for field, actual in (('source', 'source'), ('source_sha256', 'source_sha256'), ('unit_text_sha256', 'text_sha256'), ('source_text', 'source_text'), ('line', 'line'), ('locator', 'locator')):
            assert row[field] == rows[key][field] == unit[actual], (key, field)
        assert row['material_status'] == 'not_a_formal_claim' and row['review_status'] == 'approved_nonformal_material'
        assert not row['lean_declarations'] and not row['hypotheses'] and not row['missing_clauses'] and row['per_unit_reason']
        assert row['individual_literal_and_html_context_independently_read'] and key not in direct_material
        direct_material[key] = dict(record=row, path=name, review_sha256=sha(name))

"""Map only the independently approved literals from the finite 57-unit review."""
import json


def integrate(root, inventory, sha, direct_material):
    name = 'book/coverage/checks/core-instructional-label-material-source-review19-foundations-batch1-v1.json'
    review = json.loads((root/name).read_text())
    assert review['inventory_sha256'] == sha(review['inventory']) == sha('book/coverage/inventory.json')
    assert not review['proof_source_sha256'] and not review['actual_standalone_evidence']
    assert sha(review['candidate_manifest']) == review['candidate_manifest_sha256']
    candidates = {r['source_unit_key']: r for r in json.loads((root/review['candidate_manifest']).read_text())['material_units']}
    units = {r['key']: r for r in inventory['material_source_units']}
    assert len(review['material_units']) == len(candidates) == 57
    approved = set()
    pending = set()
    for row in review['material_units']:
        key = row['source_unit_key']
        unit = units[key]
        for field, actual in [('source', 'source'), ('source_sha256', 'source_sha256'), ('unit_text_sha256', 'text_sha256'), ('source_text', 'source_text'), ('line', 'line'), ('locator', 'locator')]:
            assert row[field] == unit[actual] == candidates[key][field], key
        assert not row['lean_declarations'] and not row['hypotheses'] and row['per_unit_reason']
        if row['material_status'] == 'not_a_formal_claim':
            assert row['review_status'] == 'individually_reviewed_nonformal_literal' and not row['missing_clauses'] and key not in direct_material
            approved.add(key)
            direct_material[key] = dict(record=row, path=name, review_sha256=sha(name))
        else:
            assert row['material_status'] == 'pending' and row['missing_clauses']
            pending.add(key)
    assert len(approved) == 55 and pending == {'barriers.html::node-490', 'barriers.html::node-554'}

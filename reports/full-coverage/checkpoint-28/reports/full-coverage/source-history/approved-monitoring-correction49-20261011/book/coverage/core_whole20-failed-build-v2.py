"""Integrate fresh complete source47 reviews with actual fixed proof evidence."""
import hashlib
import json
from pathlib import Path
from lean_names import declarations

REVIEWS = (
    ('policy-focops93-current47-whole-source-review20-v1.json', '79e0ed5b35c2188ecaf8aaa205c25a3d7ded9c2cefab964cbb7454935484df55', 'independent_current47_focops93_full_literal_source_review_approved', 'policy-optimization.html::exercise-18', {'policy-optimization.html::node-1446', 'policy-optimization.html::node-1449'}, 8, 26, 70),
    ('cmdp-tailrisk85-current47-whole-source-review20-v1.json', 'f8db0082ed58f38d4c4dd986aebcbd794d541ebab4747bfd7521fc64b394a68e', 'independent_current47_cmdp85_full_literal_source_review_approved', 'cmdp.html::exercise-20', {'cmdp.html::node-1123', 'cmdp.html::node-1127', 'cmdp.html::node-1128', 'cmdp.html::node-1129'}, 2, 5, 17),
)

def integrate(root, inventory, sha, add, mapping, direct_material):
    aliases = json.loads((root/'book/coverage/checks/future20-core/whole-review-original-path-aliases20-v1.json').read_text())['aliases']
    def resolve(name):
        if name.startswith('/tmp/'):
            alias = aliases[name]
            assert sha(alias['file']) == alias['sha256']
            return root/alias['file']
        path = (root/name).resolve()
        assert path.is_relative_to(root.resolve())
        return path
    def digest(name):
        return hashlib.sha256(resolve(name).read_bytes()).hexdigest()
    units = {u['key']: u for u in inventory['material_source_units']}
    exercises = {e['key']: e for e in inventory['exercises']}
    proofs = {}
    for filename, expected_hash, status, exercise_key, material_keys, proof_count, group_count, name_count in REVIEWS:
        path = 'book/coverage/checks/' + filename
        assert sha(path) == expected_hash
        review = json.loads((root/path).read_text())
        assert review['status'] == status and review['reviewer'] == '/root/applied_next' and not review['missing_clauses']
        assert review['inventory_sha256'] == sha(review['inventory']) == sha('book/coverage/inventory.json')
        for source, expected in review['source_sha256'].items():
            assert sha(source) == inventory['source_sha256'][source] == expected
        assert len(review['proof_source_sha256']) == proof_count
        exported = set()
        for source, expected in review['proof_source_sha256'].items():
            assert sha(source) == expected
            exported.update(d['name'] for d in declarations((root/source).read_text()))
            proofs[source] = expected
        seen = set()
        for evidence in review['actual_standalone_and_named_evidence']:
            name = evidence['compiler_manifest']
            assert sha(name) == evidence['compiler_manifest_sha256']
            actual = json.loads((root/name).read_text())
            assert actual == evidence.get('raw_execution_record', evidence.get('record'))
            assert actual['exit_code'] == evidence['actual_exit_code'] == 0
            assert actual['source_sha256_before'] == actual['source_sha256_after'] == sha(actual['source']) == review['proof_source_sha256'][actual['source']]
            assert sha(actual['log']) == actual['log_sha256'] == evidence['raw_log_sha256']
            command = actual['command']
            kind = 'named' if command[:2] == ['lake', 'build'] else 'standalone'
            assert kind == 'named' or command[:3] == ['lake', 'env', 'lean']
            seen.add((actual['source'], kind))
        assert seen == {(source, kind) for source in review['proof_source_sha256'] for kind in ('standalone', 'named')}
        assert len(review['actual_standalone_and_named_evidence']) == 2*proof_count
        for old in review['preserved_original_reviews']:
            assert digest(old['file']) == old['sha256']
            if 'original_reviewed_at_utc' in old:
                assert json.loads(resolve(old['file']).read_text())['reviewed_at_utc'] == old['original_reviewed_at_utc']
        primary = review['primary_attribution_review']
        if 'source' in primary:
            assert sha(primary['source']) == primary['source_sha256']
            assert sha(primary['pdf']) == primary['pdf_sha256']
        else:
            for value in primary.values():
                if isinstance(value, dict) and 'path' in value:
                    assert sha(value['path']) == value['sha256']
        assert len(review['records']) == 1
        record = review['records'][0]
        exercise = exercises[exercise_key]
        assert record['exercise_key'] == exercise_key
        assert record['exercise_text'] == exercise['source_text'] and record['exercise_text_sha256'] == exercise['text_sha256']
        assert record['source_sha256'] == exercise['source_sha256']
        assert record['review_status'] == 'approved_complete_source' and record['whole_exercise_approved'] and record['independent_whole_source_review_passed'] and not record['missing_clauses']
        clauses = record['components']
        assert clauses == review['approved_mathematical_groups'] and len(clauses) == group_count
        group_ids = {c['id'] for c in clauses}
        assert record['reviewed_clauses']
        for literal_clause in record['reviewed_clauses']:
            assert literal_clause['source_clause'] and literal_clause['reason'] and literal_clause['groups']
            assert set(literal_clause['groups']) <= group_ids
        for clause in clauses:
            assert clause['review_status'] == 'approved_precise_source_component' and clause['per_clause_reason'] and clause['lean_declarations'] and not clause['missing_clauses'] and isinstance(clause['hypotheses'], list)
            assert set(clause['lean_declarations']) <= exported
        names = list(dict.fromkeys(name for clause in clauses for name in clause['lean_declarations']))
        hypotheses = list(dict.fromkeys(h for clause in clauses for h in clause['hypotheses']))
        assert len(names) == name_count and set(names) == set(record['lean_declarations'])
        hypotheses = list(dict.fromkeys(hypotheses + record['hypotheses']))
        add(exercise_key, names, record['per_exercise_reason'], hypotheses, [])
        mapping[exercise_key]['source_review'] = dict(file=path, sha256=sha(path), component_ids=[c['id'] for c in clauses], limits=review['limits'])
        assert {r['source_unit_key'] for r in review['material_units']} == material_keys
        for row in review['material_units']:
            key = row['source_unit_key']
            unit = units[key]
            assert row['entire_inventory_record'] == unit
            for field, actual in (('unit_text_sha256', 'text_sha256'), ('source_sha256', 'source_sha256'), ('source_text', 'source_text'), ('line', 'line'), ('locator', 'locator')):
                assert row[field] == unit[actual]
            assert row['review_status'] == 'approved_complete_source' and row['material_status'] == 'proved' and not row['missing_clauses'] and row['per_unit_reason']
            assert row['lean_declarations'] and set(row['lean_declarations']) <= exported and key not in direct_material
            direct_material[key] = dict(record=row, path=path, review_sha256=sha(path))
    return proofs

"""Integrate literal independent reviews retained during the source33 hold.

Original execution and review documents remain byte copies. This helper reads
explicit per-unit decisions; file tags and theorem counts never close a unit.
"""
import hashlib
import json
from pathlib import Path

BINDING = 'book/coverage/checks/foundations-held19-source44-evidence-review-identity-binding-v1.json'
BINDING_SHA256 = '9ea990b40967d6654b56c8ac9ad2ec97dc2ba6f7418f7775c481f32006f4859a'

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def apply(full, nonformal, partial):
    assert digest(BINDING) == BINDING_SHA256
    binding = json.loads(Path(BINDING).read_text())
    assert digest(binding['inventory']) == binding['inventory_sha256']
    assert digest('book/coverage/inventory.json') == binding['inventory_sha256']
    inventory = json.loads(Path(binding['inventory']).read_text())
    units = {unit['key']: unit for unit in inventory['material_source_units']}
    for source, expected in binding['source_sha256'].items():
        assert digest(source) == expected
    for proof in binding['proof_execution_bindings']:
        assert digest(proof['source']) == proof['source_sha256']
        assert digest(proof['canonical_execution_record_copy']) == proof['canonical_execution_record_copy_sha256']
        raw = json.loads(Path(proof['canonical_execution_record_copy']).read_text())
        assert raw['exit_code'] == proof['actual_exit_code'] == 0
        assert raw['source_sha256_before'] == raw['source_sha256_after'] == proof['source_sha256']
        assert digest(proof['canonical_log_copy']) == raw['log_sha256'] == proof['canonical_log_copy_sha256']
    # These four pending suprema units retain their literal missing clauses.
    # Only the explicitly matching original component is mapped here.
    supremum_components = {
        'primer-basics.html::node-988': ['real-bounds-completeness-finite-epsilon-and-image', 'extended-real-domain-empty-unbounded-values-and-partial-arithmetic'],
        'primer-basics.html::node-990': ['real-bounds-completeness-finite-epsilon-and-image', 'extended-real-domain-empty-unbounded-values-and-partial-arithmetic'],
        'primer-basics.html::node-1004': ['safeopt-actual-extended-initial-bands-and-truth-witness'],
        'primer-basics.html::node-1023': ['actual-maximizer-domain-and-approximate-choices'],
    }
    for row in binding['selected_independently_reviewed_material_units']:
        key = row['source_unit_key']
        unit = units[key]
        assert unit['text_sha256'] == row['unit_text_sha256']
        assert unit['source_sha256'] == row['source_sha256']
        assert unit['line'] == row['line'] and unit['locator'] == row['locator']
        assert digest(row['review']) == row['review_sha256']
        original = json.loads(Path(row['review']).read_text())
        assert original.get('reviewed_at_utc') == row['original_reviewed_at_utc']
        reviewed = next(u for u in original['material_units'] if u.get('source_unit_key', u.get('key')) == key)
        assert reviewed.get('unit_text_sha256', reviewed.get('text_sha256')) == unit['text_sha256']
        assert reviewed.get('missing_clauses', []) == row['missing_clauses']
        for source, expected in original.get('proof_source_sha256', {}).items():
            assert digest(source) == expected
        citation = ' Original independent review: ' + row['review'] + '. Exact current-source binding: ' + BINDING + '.'
        hypotheses = row['hypotheses'] or ['Exactly the mathematical domains stated in the original independent review and the cited genuine declarations.']
        if row['material_status'] == 'proved':
            assert not row['missing_clauses'] and row['lean_declarations']
            full[key] = [dict(statement_in_prose=unit['source_text'], lean_declarations=row['lean_declarations'], hypotheses=hypotheses, correspondence=row['reason'] + citation)]
        elif row['material_status'] == 'not_a_formal_claim':
            assert not row['missing_clauses'] and not row['lean_declarations']
            nonformal[key] = row['reason'] + citation
        else:
            assert row['material_status'] == 'pending' and row['missing_clauses']
            components = row['components']
            if key in supremum_components:
                components = [c for c in original['components'] if c['component_id'] in supremum_components[key]]
                assert len(components) == len(supremum_components[key])
            proved = []
            for component in components:
                assert component.get('review_status', component.get('status', '')).startswith('approved')
                assert not component.get('missing_clauses', [])
                refs = component['lean_declarations']
                assert refs
                reason = component.get('per_component_reason', component.get('per_clause_reason', component.get('reason', '')))
                statement = component.get('source_clause', reason)
                assert statement and reason
                proved.append(dict(statement_in_prose=statement, lean_declarations=refs,
                    hypotheses=component.get('hypotheses', hypotheses), correspondence=reason + citation))
            assert proved, key
            pending = [gap if isinstance(gap, str) else gap['source_clause'] + ' ' + gap['reason'] for gap in row['missing_clauses']]
            partial[key] = dict(proved=proved, pending=pending)

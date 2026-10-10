"""Read explicit literal future20 decisions against the released source47.

Historical source44 reviews stay byte-identical. The interface binding changes
only their current page/inventory identities and excludes changed literals.
"""
import hashlib
import json
from pathlib import Path

from lean_names import declarations

BINDING = 'book/coverage/checks/foundations-material20-source47-interface-binding-v1.json'
BINDING_SHA256 = 'a67dd06c02a41454afe691ec9f9dfbde49fe50de6528841dfe3b8499684e354f'
CONFIRMATION = 'book/coverage/checks/foundations-material20-source47-interface-independent-applied-confirmation-v1.json'
CONFIRMATION_SHA256 = 'f87b4377adee1d98b7aaeb1b6fac41e83d49958f1563056a25ad88b30457edff'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pending_keys():
    """Return only this batch's independently reviewed pending literal keys."""
    assert digest(BINDING) == BINDING_SHA256
    binding = json.loads(Path(BINDING).read_text())
    return frozenset(row['source_unit_key'] for row in binding['material_units']
                     if row['material_status'] == 'pending')


def apply(full, nonformal, partial):
    assert digest(BINDING) == BINDING_SHA256
    assert digest(CONFIRMATION) == CONFIRMATION_SHA256
    binding = json.loads(Path(BINDING).read_text())
    assert digest(binding['inventory']) == binding['inventory_sha256']
    assert digest('book/coverage/inventory.json') == binding['inventory_sha256']
    inventory = json.loads(Path(binding['inventory']).read_text())
    units = {unit['key']: unit for unit in inventory['material_source_units']}
    names = set()
    for source, expected in binding['proof_source_sha256'].items():
        assert digest(source) == expected
        names.update(row['name'] for row in declarations(Path(source).read_text()))
    for source, expected in binding['source_sha256'].items():
        assert digest(source) == expected
    originals = {}
    for reference in binding['original_review_byte_copies']:
        path = reference['canonical_byte_copy']
        assert digest(path) == reference['canonical_byte_copy_sha256']
        review = json.loads(Path(path).read_text())
        assert review['reviewed_at_utc'] == reference['original_reviewed_at_utc']
        originals[path] = review
    excluded = {row['source_unit_key'] for row in binding['changed5_units_excluded']}
    for row in binding['material_units']:
        key = row['source_unit_key']
        assert key not in excluded
        unit = units[key]
        assert unit['text_sha256'] == row['unit_text_sha256']
        assert unit['source_sha256'] == row['source_sha256']
        assert unit['line'] == row['line'] and unit['locator'] == row['locator']
        review = originals[row['original_review']]
        assert digest(row['original_review']) == row['original_review_sha256']
        original = next(u for u in review['material_units'] if u['source_unit_key'] == key)
        assert original == row['original_unit_row']
        assert original['source_text'] == unit['source_text']
        for field in ['material_status', 'per_unit_reason', 'hypotheses', 'lean_declarations', 'missing_clauses']:
            assert row[field] == original[field]
        assert set(row['lean_declarations']) <= names
        citation = (' Original complete literal review: ' + row['original_review']
                    + '. Exact released-source interface: ' + BINDING + '.')
        if row['material_status'] == 'proved':
            assert row['lean_declarations'] and not row['missing_clauses']
            full[key] = [dict(statement_in_prose=unit['source_text'],
                             lean_declarations=row['lean_declarations'],
                             hypotheses=row['hypotheses'] or ['Exactly the domains in the cited genuine declarations and the original literal review.'],
                             correspondence=row['per_unit_reason'] + citation)]
        elif row['material_status'] == 'not_a_formal_claim':
            assert not row['lean_declarations'] and not row['missing_clauses']
            nonformal[key] = row['per_unit_reason'] + citation
        else:
            assert row['material_status'] == 'pending' and row['missing_clauses']
            proved = []
            for component in row['approved_components']:
                assert component['review_status'].startswith('approved')
                assert component['lean_declarations'] and not component['missing_clauses']
                assert set(component['lean_declarations']) <= names
                reason = component['per_component_reason']
                proved.append(dict(statement_in_prose=component.get('source_clause', reason),
                                   lean_declarations=component['lean_declarations'],
                                   hypotheses=component['hypotheses'] or ['Exactly the domain of this separately approved component.'],
                                   correspondence=reason + citation))
            # A fresh complete literal read refines its remaining gaps while
            # retaining earlier separately approved mathematical components.
            prior_proved = partial.get(key, {}).get('proved', [])
            partial[key] = dict(proved=list(prior_proved) + proved,
                                pending=row['missing_clauses'])

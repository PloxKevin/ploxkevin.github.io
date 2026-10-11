"""Map individual full-literal reviews against unchanged current48 sources.

Original review bytes and times are fixed. Primary Mathlib route citations are
retained separately from the local declaration index. No HTML containment closes
a pending mathematical clause, and prior separately proved atoms are preserved.
"""
from pathlib import Path
import hashlib
import json

BINDING = 'book/coverage/checks/foundations-future21/foundations-material21-source48-interface-binding-v1.json'
BINDING_SHA256 = '3dee18bbda9d816ca827b1cc8305cb2397ed4c206d54128cf03221af98de82b1'

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def pending_keys():
    assert digest(BINDING) == BINDING_SHA256
    data = json.loads(Path(BINDING).read_text())
    return frozenset(r['source_unit_key'] for r in data['material_units']
                     if r['material_status'] == 'pending')

def apply(full, nonformal, partial):
    assert digest(BINDING) == BINDING_SHA256
    data = json.loads(Path(BINDING).read_text())
    assert digest(data['inventory']) == digest('book/coverage/inventory.json') == data['inventory_sha256']
    inventory = json.loads(Path(data['inventory']).read_text())
    units = {r['key']: r for r in inventory['material_source_units']}
    original = {}
    for ref in data['original_review_byte_copies']:
        path = ref['canonical_byte_copy']
        assert digest(path) == ref['canonical_byte_copy_sha256'] == ref['original_sha256']
        review = json.loads(Path(path).read_text())
        assert review['reviewed_at_utc'] == ref['original_reviewed_at_utc']
        original[path] = review
    for path, expected in data['proof_source_sha256'].items():
        assert digest(path) == expected
    for row in data['material_units']:
        key = row['source_unit_key']
        unit = units[key]
        assert unit == row['exact_current48_inventory_record']
        review = original[row['original_review']]
        assert digest(row['original_review']) == row['original_review_sha256']
        assert review['reviewed_at_utc'] == row['original_reviewed_at_utc']
        old = next(r for r in review['material_units'] if r.get('source_unit_key', r.get('key')) == key)
        assert old == row['original_unit_row']
        assert row['hypotheses'] == old.get('hypotheses', [])
        assert row['per_unit_reason'] == old['per_unit_reason']
        citation = (' Original complete literal review: ' + row['original_review']
                    + '. Exact unchanged current48 interface: ' + BINDING + '.')
        if row['primary_mathlib_declarations']:
            citation += (' Primary Mathlib routes, explicitly retained in that complete review: '
                         + ', '.join(row['primary_mathlib_declarations']) + '.')
        if row['material_status'] == 'proved':
            assert row['lean_declarations'] and not row['missing_clauses']
            full[key] = [dict(statement_in_prose=unit['source_text'],
                lean_declarations=row['lean_declarations'], hypotheses=row['hypotheses'],
                correspondence=row['per_unit_reason'] + citation)]
            # A new whole-literal decision also retains earlier independently
            # approved atoms, including stronger model specializations.
            for c in row['original_current20_claims']:
                if c['status'] == 'proved':
                    old_atom = {k: c[k] for k in ['statement_in_prose', 'lean_declarations', 'hypotheses', 'correspondence']}
                    if old_atom not in full[key]:
                        full[key].append(old_atom)
        elif row['material_status'] == 'not_a_formal_claim':
            assert not row['lean_declarations'] and not row['missing_clauses']
            nonformal[key] = row['per_unit_reason'] + citation
        else:
            assert row['material_status'] == 'pending' and row['missing_clauses']
            proved = list(partial.get(key, {}).get('proved', []))
            # Preserve every explicitly proved old ledger atom even when it
            # previously came from an ATOMS branch rather than this dictionary.
            for c in row['original_current20_claims']:
                if c['status'] == 'proved':
                    old_atom = {k: c[k] for k in ['statement_in_prose', 'lean_declarations', 'hypotheses', 'correspondence']}
                    if old_atom not in proved:
                        proved.append(old_atom)
            for c in row['approved_components']:
                assert c['review_status'].startswith('approved') and c['lean_declarations'] and not c['missing_clauses']
                reason = c['per_component_reason']
                primary = c.get('primary_mathlib_declarations', [])
                route = (' Primary Mathlib routes: ' + ', '.join(primary) + '.') if primary else ''
                proved.append(dict(statement_in_prose=c['source_clause'],
                    lean_declarations=c['lean_declarations'], hypotheses=c['hypotheses'],
                    correspondence=reason + route + citation))
            pending = [g if isinstance(g, str) else g['source_clause'] + ' ' + g['reason'] for g in row['missing_clauses']]
            partial[key] = dict(proved=proved, pending=pending)

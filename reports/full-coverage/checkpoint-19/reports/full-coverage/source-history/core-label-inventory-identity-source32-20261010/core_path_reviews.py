"""Check literal source reviews for constructed finite CMDP path measures.

Historical component approvals retain their original scope and evidence. Whole
source approvals below are separate reviews of the complete literal text.
"""
import json


def verify_inventory31_identity(root, review, review_path, sha):
    """Verify a new inventory identity without changing prior review provenance."""
    name = 'book/coverage/checks/core-cmdp-source31-inventory-identity-rebase-independent-foundations-confirmation.json'
    confirmation = json.loads((root/name).read_text())
    if (confirmation['status'] != 'independent_exact_inventory_identity_rebase_confirmation_passed'
            or sha(confirmation['rebase_manifest']) != confirmation['rebase_manifest_sha256']
            or sha(confirmation['immutable_inventory_after']) != confirmation['immutable_inventory_after_sha256']
            or review['inventory_sha256'] != confirmation['immutable_inventory_after_sha256']
            or sha('book/coverage/inventory.json') != review['inventory_sha256']):
        raise ValueError('Unconfirmed current CMDP inventory identity: '+str(review_path))
    manifest = json.loads((root/confirmation['rebase_manifest']).read_text())
    path = str(review_path.relative_to(root))
    row = next(r for r in manifest['records'] if r['rebased_review'] == path)
    if (sha(path) != row['rebased_review_sha256']
            or sha(row['original_review']) != row['original_review_sha256']
            or sha(row['preserved_original_review']) != row['original_review_sha256']
            or sha(row['original_inventory']) != row['original_inventory_sha256']):
        raise ValueError('Changed current CMDP identity provenance: '+path)
    old = json.loads((root/row['original_review']).read_text())
    normalized = {k: v for k, v in review.items() if k != 'inventory_identity_rebase_correction31'}
    normalized['inventory_sha256'] = old['inventory_sha256']
    if normalized != old:
        raise ValueError('Current CMDP identity rebase changed an original review field: '+path)
    provenance = review['inventory_identity_rebase_correction31']
    for field in ('original_review', 'original_review_sha256', 'original_inventory', 'original_inventory_sha256'):
        if provenance[field] != row[field]:
            raise ValueError('Current CMDP identity provenance mismatch: '+field)
    return name


def verify_actual_evidence(root, inventory, review, sha):
    for name, expected in review['source_sha256'].items():
        if inventory['source_sha256'][name] != expected or sha(name) != expected:
            raise ValueError('Changed literal path source: '+name)
    for family in ('proof_source_sha256', 'definition_dependency_source_sha256'):
        for name, expected in review.get(family, {}).items():
            if sha(name) != expected:
                raise ValueError('Changed path proof or definition dependency: '+name)
    seen = set()
    for evidence in review['actual_standalone_evidence']:
        name = evidence['compiler_manifest']
        if sha(name) != evidence['compiler_manifest_sha256']:
            raise ValueError('Changed actual path compiler record: '+name)
        actual = json.loads((root/name).read_text())
        source = actual['source']
        if (source not in review['proof_source_sha256']
                or actual['exit_code'] != evidence['actual_exit_code'] or actual['exit_code'] != 0
                or actual['source_sha256_before'] != actual['source_sha256_after']
                or sha(source) != actual['source_sha256_after']
                or actual['source_sha256_after'] != review['proof_source_sha256'][source]
                or actual.get('source_unchanged', True) is not True
                or actual['command'] != evidence['actual_command']
                or actual['actual_workdir'] != evidence['actual_workdir']
                or actual['log'] != evidence['raw_log']
                or actual['log_sha256'] != evidence['raw_log_sha256']
                or sha(actual['log']) != actual['log_sha256']):
            raise ValueError('Actual path compiler evidence disagrees: '+name)
        seen.add(source)
    if set(review['proof_source_sha256']) != seen:
        raise ValueError('A reviewed path proof lacks its actual standalone compiler evidence')


def integrate_literal_path_reviews(root, inventory, reviewed_path, sha, add, mapping, direct_material):
    names = ['finite-cmdp-occupancy-8-1-full-source-review-v1.json',
             'finite-cmdp-occupancy-definition-material-full-source-review-v1.json',
             'finite-controlled-history-measure-laws-source-components-review-v1.json']
    units = {u['key']: u for u in inventory['material_source_units']}
    exercises = {e['key']: e for e in inventory['exercises']}
    for name in names:
        path = reviewed_path(name)
        if not path.exists():
            continue
        review = json.loads(path.read_text())
        confirmation = verify_inventory31_identity(root, review, path, sha)
        verify_actual_evidence(root, inventory, review, sha)
        whole = name != names[-1]
        if whole and (review['status'] != 'approved_complete_source' or review['missing_clauses']):
            raise ValueError('Unapproved complete path review: '+name)
        primary = review.get('primary_attribution_evidence')
        if primary:
            for field in ('prior_check', 'primary_text', 'primary_pdf'):
                if sha(primary[field]) != primary[field+'_sha256']:
                    raise ValueError('Changed path primary attribution evidence: '+field)
        if whole:
            for record in review.get('records', []):
                key = record['exercise_key']
                clauses = record['components']
                declared = list(dict.fromkeys(n for c in clauses for n in c['lean_declarations']))
                if (exercises[key]['text_sha256'] != record['exercise_text_sha256']
                        or record['review_status'] != 'approved_complete_source'
                        or record['missing_clauses'] or not record['per_exercise_reason']
                        or clauses != review['reviewed_clauses']
                        or not clauses or set(declared) != set(record['lean_declarations'])
                        or any(c['status'] != 'approved_precise_component'
                               or c['missing_clauses'] or not c['lean_declarations']
                               or not c['per_clause_reason'] for c in clauses)):
                    raise ValueError('Incomplete literal path exercise correspondence: '+key)
                hypotheses = list(dict.fromkeys(h for c in clauses for h in c['hypotheses']))
                add(key, declared, record['per_exercise_reason'], hypotheses, [])
                mapping[key]['source_review'] = dict(
                    file=str(path.relative_to(root)), sha256=sha(str(path.relative_to(root))),
                    component_ids=[c['id'] for c in clauses], limits=review['limits'],
                    inventory_identity_confirmation=dict(file=confirmation, sha256=sha(confirmation)))
        for record in review['material_units']:
            key = record['source_unit_key']
            unit = units[key]
            if (unit['source_sha256'] != record['source_sha256']
                    or unit['text_sha256'] != record['unit_text_sha256']
                    or unit['source_text'] != record['source_text']
                    or record['review_status'] != 'approved_complete_source'
                    or record['material_status'] != 'proved' or record['missing_clauses']
                    or not record['lean_declarations'] or not record['per_unit_reason']):
                raise ValueError('Incomplete literal path material correspondence: '+key)
            if key in direct_material:
                raise ValueError('Duplicate complete literal path material approval: '+key)
            direct_material[key] = dict(record=record, path=str(path.relative_to(root)),
                                       review_sha256=sha(str(path.relative_to(root))))


def integrate_instructional_labels(root, inventory, sha, direct_material):
    name = 'book/coverage/checks/core-instructional-label-material-source-review-18-v1.json'
    path = root/name
    if not path.exists():
        return
    review = json.loads(path.read_text())
    if (review['status'] != 'independent_exact_nonformal_material_units_review_passed'
            or review['missing_clauses'] or review['proof_source_sha256']
            or review['actual_standalone_evidence']
            or sha(review['candidate_manifest']) != review['candidate_manifest_sha256']
            or sha(review['inventory']) != review['inventory_sha256']
            or sha('book/coverage/inventory.json') != review['inventory_sha256']):
        raise ValueError('Unapproved literal instructional-label review')
    candidate = json.loads((root/review['candidate_manifest']).read_text())
    candidates = {u['source_unit_key']: u for u in candidate['material_units']}
    units = {u['key']: u for u in inventory['material_source_units']}
    seen = set()
    for name, expected in review['source_sha256'].items():
        if sha(name) != expected or inventory['source_sha256'][name] != expected:
            raise ValueError('Changed instructional-label source: '+name)
    for record in review['material_units']:
        key = record['source_unit_key']
        unit = units[key]
        if (key in seen or key in direct_material or key not in candidates
                or record['review_status'] != 'approved_complete_source'
                or record['material_status'] != 'not_a_formal_claim' or record['missing_clauses']
                or record['lean_declarations'] or record['hypotheses']
                or not record['per_unit_reason']):
            raise ValueError('Invalid individual instructional-label classification: '+key)
        for field, source_field in [('source', 'source'), ('source_sha256', 'source_sha256'),
                                    ('unit_text_sha256', 'text_sha256'), ('source_text', 'source_text'),
                                    ('line', 'line'), ('locator', 'locator')]:
            if record[field] != unit[source_field] or record[field] != candidates[key][field]:
                raise ValueError('Changed individual instructional-label literal: '+key)
        seen.add(key)
        direct_material[key] = dict(record=record, path=str(path.relative_to(root)),
                                   review_sha256=sha(str(path.relative_to(root))))
    if seen != set(candidates) or len(seen) != 157:
        raise ValueError('Individual instructional-label review did not cover its exact candidate set')

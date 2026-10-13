"""Apply only the explicit independently reviewed Source90 mapping proposals.

Write candidates and exact reversible patches; keep original owner bytes intact.
The candidates still require separate independent installation reviews.
"""
from collections import Counter, defaultdict
import copy
import json
import os
import sys
from pathlib import Path
from prepare_runtime35 import ROOT, encode, exact, path, put, read, ref, sha

FOLDER = 'book/coverage/checks/checkpoint35-ledgers'
GAUSSIAN = 'book/coverage/checks/checkpoint35-review/adaptive-gaussian35-proposed-exact-mapping-v1.json'
DIAGONAL = 'book/coverage/checks/checkpoint35-review/diagonal35-exact-material-mapping-proposal-v1.json'
HISTORY = 'reports/full-coverage/source-history/owners34-before-checkpoint35-v1'


def counts(owners):
    exercises = Counter()
    materials = defaultdict(list)
    for owner in owners.values():
        for e in owner['exercises']:
            exercises[e['status']] += 1
        for claim in owner['material_claims'] + [c for e in owner['exercises'] for c in e['claims']]:
            for key in claim.get('source_unit_keys', []):
                materials[key].append(claim['status'])
        for key in owner.get('pending_source_units', []):
            if isinstance(key, dict):
                key = key.get('key', key.get('inventory_key'))
            materials[key].append('pending')
    return dict(exercises), dict(Counter('pending' if 'pending' in v else 'reviewed' for v in materials.values()))


def main():
    gaussian, diagonal = read(GAUSSIAN), read(DIAGONAL)
    proposals = [GAUSSIAN, DIAGONAL]
    for document in [gaussian, diagonal]:
        assert document['status'].startswith('approved') and document['errors'] == []
        assert document['inventory']['sha256'] == sha('book/coverage/inventory.json')
        exact(document['independent_source_review'])
    owners, originals, patches = {}, {}, {'modules': [], 'core': []}
    before_refs = {}
    for domain in ['foundations', 'applied', 'modules', 'core']:
        n = 'book/coverage/' + domain + '.json'
        history = HISTORY + '/' + domain + '.json'
        if domain in patches:
            path(history).parent.mkdir(parents=True, exist_ok=True)
            if not path(history).exists():
                os.link(path(n), path(history))
                path(history).chmod(0o444)
            source = history
        else:
            source = n
        originals[domain] = read(source)
        owners[domain] = copy.deepcopy(originals[domain])
        before_refs[domain] = {'file': n, 'sha256': sha(source)}
    before_exercises, before_material = counts(originals)
    assert before_exercises == {'complete_math': 538, 'pending': 11, 'partial': 7}
    assert before_material == {'reviewed': 4858, 'pending': 7916}
    inventory = read('book/coverage/inventory.json')
    units = {u['key']: u for u in inventory['material_source_units']}
    exercise_index = {e['key']: e for e in inventory['exercises']}
    changed_material = []
    refreshed = []

    def change(domain, pointer, value):
        parent = owners[domain]
        for part in pointer[:-1]:
            parent = parent[part]
        key = pointer[-1]
        exists = key < len(parent) if isinstance(parent, list) else key in parent
        before = copy.deepcopy(parent[key]) if exists else None
        if exists and before == value:
            return
        if isinstance(parent, list) and not exists:
            assert key == len(parent)
            parent.append(copy.deepcopy(value))
        else:
            parent[key] = copy.deepcopy(value)
        patches[domain].append({'pointer': pointer, 'before_exists': exists,
                               'before': before, 'after': copy.deepcopy(value)})

    for proposal_name, document in [(GAUSSIAN, gaussian), (DIAGONAL, diagonal)]:
        for mapping in document['material_mappings']:
            key = mapping['material_unit_key']
            unit = units[key]
            assert unit['source'] == mapping['source']
            assert unit['text_sha256'] == mapping.get('exact_text_sha256', mapping.get('text_sha256'))
            assert sha(unit['source']) == mapping['source_sha256']
            domain = mapping.get('owner', 'modules')
            rows = [(i, c) for i, c in enumerate(owners[domain]['material_claims'])
                    if c.get('source_unit_keys') == [key]
                    and c['id'].endswith(('::claim-review', '::semantic-review'))]
            assert len(rows) == 1, key
            i, claim = rows[0]
            if 'claim_id' in mapping:
                assert mapping['claim_id'] == claim['id']
            new = copy.deepcopy(claim)
            for field in ['status', 'lean_declarations', 'hypotheses', 'correspondence', 'remaining_gaps']:
                new[field] = copy.deepcopy(mapping[field])
            assert new['status'] != 'pending' and new['remaining_gaps'] == []
            new['independent_source_review35'] = document['independent_source_review']
            new['exact_source90_mapping_proposal35'] = ref(proposal_name)
            new['exact_source90_text_sha256'] = unit['text_sha256']
            change(domain, ['material_claims', i], new)
            (changed_material if claim['status'] == 'pending' else refreshed).append(key)
    whole = gaussian['whole_exercise']
    key = whole['inventory_key']
    assert whole['status'] == 'complete_math' and whole['remaining_gaps'] == []
    assert whole['exact_text_sha256'] == exercise_index[key]['text_sha256']
    i = next(i for i, e in enumerate(owners['modules']['exercises']) if e['inventory_key'] == key)
    exercise = owners['modules']['exercises'][i]
    assert exercise['status'] == 'partial'
    for mapping in gaussian['exercise_claim_mappings']:
        j = next(j for j, c in enumerate(exercise['claims']) if c['id'] == mapping['claim_id'])
        claim = exercise['claims'][j]
        assert claim['statement_in_prose'] == mapping['statement_in_prose']
        if claim['status'] != 'pending':
            # Preserve its proved declarations while closing the explicitly
            # reviewed historical Gaussian/source-correspondence gaps.
            assert set(claim['lean_declarations']) <= set(mapping['lean_declarations'])
        new = copy.deepcopy(claim)
        for field in ['status', 'lean_declarations', 'hypotheses', 'correspondence', 'remaining_gaps']:
            new[field] = copy.deepcopy(mapping[field])
        new['independent_source_review35'] = gaussian['independent_source_review']
        new['exact_source90_mapping_proposal35'] = ref(GAUSSIAN)
        change('modules', ['exercises', i, 'claims', j], new)
    assert all(c['status'] != 'pending' and c['remaining_gaps'] == [] for c in exercise['claims'])
    change('modules', ['exercises', i, 'status'], 'complete_math')
    change('modules', ['exercises', i, 'independent_whole_exercise_review35'], {
        'source_review': gaussian['independent_source_review'], 'exact_mapping': ref(GAUSSIAN),
        'text_sha256': whole['exact_text_sha256'], 'all_prompt_hint_and_solution_clauses_reviewed': True})
    sys.path.insert(0, str(path('book/coverage')))
    from lean_names import declarations
    sources = read('book/coverage/checks/checkpoint35-root/compiled-reviewed-additions-plan-v1.json')['sources']
    for row in sources:
        source = row['source']
        exact(source)
        domains = ['modules', 'core'] if 'Diagonal' in source['file'] else ['modules']
        for domain in domains:
            change(domain, ['proof_files', source['file']], source['sha256'])
        for declaration in declarations(path(source['file']).read_text()):
            if declaration['kind'] in {'theorem', 'lemma'}:
                change('modules', ['declarations', len(owners['modules']['declarations'])],
                       {**declaration, 'file': source['file']})
    for domain in ['modules', 'core']:
        identity = {'status': 'prepared_exact_Source90_reviewed_owner_candidate',
                    'baseline_owner': before_refs[domain], 'inventory': ref('book/coverage/inventory.json'),
                    'mapping_proposals': [ref(n) for n in proposals],
                    'unchanged_site_sources': True, 'coverage_complete': False}
        change(domain, ['current_checkpoint35_identity'], identity)
        current = copy.deepcopy(owners[domain]['counts'])
        if domain == 'modules':
            current['exercise_status'] = dict(Counter(e['status'] for e in owners[domain]['exercises']))
            current['exercise_claim_status'] = dict(Counter(c['status'] for e in owners[domain]['exercises'] for c in e['claims']))
            current['material_claim_status'] = dict(Counter(c['status'] for c in owners[domain]['material_claims']))
            current['new_declarations'] = len(owners[domain]['declarations'])
        else:
            current['exercise_statuses'] = dict(Counter(e['status'] for e in owners[domain]['exercises']))
            current['proof_files'] = len(owners[domain]['proof_files'])
        change(domain, ['counts'], current)
    after_exercises, after_material = counts(owners)
    assert after_exercises == {'complete_math': 539, 'pending': 11, 'partial': 6}
    assert after_material == {'reviewed': 4878, 'pending': 7896}
    replacements = []
    for domain in ['modules', 'core']:
        candidate = FOLDER + '/' + domain + '-candidate-v1.json'
        put(candidate, encode(owners[domain]))
        inverse = FOLDER + '/' + domain + '-exact-inverse-v1.json'
        put(inverse, encode({'baseline': before_refs[domain], 'candidate': ref(candidate),
                            'patches': patches[domain], 'preserved_original': ref(HISTORY + '/' + domain + '.json')}))
        replacements.append({'destination': before_refs[domain]['file'], 'before': before_refs[domain],
            'candidate': ref(candidate), 'exact_inverse': ref(inverse),
            'preserved_original': ref(HISTORY + '/' + domain + '.json')})
    protected = {n: h for n, h in read('reports/full-coverage/checkpoint35-runtime-preparation-v1.json')['source_hashes'].items()
                 if n != 'verification/lean/SafeLearning.lean'}
    protected.update({n: sha(n) for n in ['book/coverage/inventory.json',
        'book/coverage/foundations.json', 'book/coverage/applied.json',
        'reports/full-coverage/checkpoint-34-selection.json', 'reports/full-coverage/checkpoint-35-selection.json']})
    binding = {'status': 'exact_reviewed_mapping_candidates_ready_for_independent_installation_review',
        'inventory': ref('book/coverage/inventory.json'), 'mapping_proposals': [ref(n) for n in proposals],
        'replacements': replacements, 'protected_input_sha256': protected,
        'changed_whole_material_units': changed_material, 'refreshed_material_units': refreshed,
        'whole_material_units_completed': len(changed_material), 'refreshed_existing_material_units': len(refreshed),
        'exercises_completed': 1, 'closed_exercises': [key], 'exercise_counts': after_exercises,
        'material_counts': after_material, 'historical_evidence_rewritten': 0,
        'coverage_complete': False, 'owner_installation_claimed': False}
    n = FOLDER + '/owner-candidate-binding-v1.json'
    put(n, encode(binding))
    print(json.dumps({'status': binding['status'], 'binding': ref(n),
        'exercise_counts': after_exercises, 'material_counts': after_material}))


if __name__ == '__main__':
    main()

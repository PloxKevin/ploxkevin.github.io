"""Prepare four exact owner34 candidates and reversible patches for review.

Current Source90 must already equal the independently reviewed two-page
qualification and fresh full29 inventory. No owner/site/inventory/proof/PUB or
aggregate is installed by this helper. Only the nine specified material rows
and the two specified exercises are closed; all other pending work is retained.
"""
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import argparse, copy, hashlib, importlib.util, json, re, subprocess, sys, time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(BASE))
from correspondence_routes34_v1 import assemble, IQC_EXERCISE, NN_EXERCISE, CONDITIONAL, IQC_KEYS, NN_KEYS

OLD_INVENTORY = 'book/coverage/inventory-after-correction88.json'
OLD_INVENTORY_SHA = '87b8457614b7a9a127c171e1a95adf43bd94d05de6d63921b5e69493e3822202'
INDEX = 'book/coverage/checks/checkpoint33-review/next-unselected-work-index-v1.json'
UTILITIES = 'book/coverage/checks/checkpoint33-ledgers/prepare_seven_owner_candidates_v2.py'
IQC_SUMMARY = 'book/coverage/checks/checkpoint34-iqc-preparation/IQC21-current-Exercise14_6-four-literal-correspondence-summary-v1.json'
NN_SUMMARY = 'book/coverage/checks/checkpoint34-nn-preparation/NN65-prospective-Exercise14_3-four-literal-correspondence-summary-v1.json'
OWNERS = ['foundations', 'applied', 'modules', 'core']

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def encode(data):
    return (json.dumps(data, indent=2, ensure_ascii=False)+'\n').encode()
def path(n):
    p = Path(n)
    assert not p.is_absolute() and '..' not in p.parts and p.as_posix() == n
    p = ROOT / p
    assert not p.is_symlink() and p.resolve().is_relative_to(ROOT)
    return p
def ref(p):
    p = path(p) if isinstance(p, str) else p
    return {'file': str(p.relative_to(ROOT)), 'sha256': sha(p), 'bytes': p.stat().st_size}
def read(n, h=None):
    p = path(n)
    if h is not None:
        assert sha(p) == h, n
    return json.loads(p.read_bytes())
def exact(r):
    p = path(r['file'])
    assert sha(p) == r['sha256'], r['file']
    if 'bytes' in r:
        assert p.stat().st_size == r['bytes']
    return p
def new(p, data):
    assert p.is_relative_to(BASE) and not p.exists() and not p.is_symlink(), str(p)
    with p.open('xb') as out:
        out.write(encode(data))
    p.chmod(0o444)
def load_module(name, p):
    spec = importlib.util.spec_from_file_location(name, p)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module
def flatten(routes):
    return sorted({n for r in routes for n in r['lean_declarations']})
def assumptions(routes):
    return list(dict.fromkeys(h for r in routes for h in r['hypotheses']))
def same_literal(a, b):
    return {k:v for k,v in a.items() if k != 'source_sha256'} == {k:v for k,v in b.items() if k != 'source_sha256'}
def without_timestamp(data):
    return {k:v for k,v in data.items() if k not in {'generated_at_utc'}}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for key in ['inventory', 'composition-review', 'component-review', 'readiness']:
        ap.add_argument('--'+key, required=True)
        ap.add_argument('--'+key+'-sha256', required=True)
    ap.add_argument('--tag', default='v1')
    args = ap.parse_args()
    assert re.fullmatch('[A-Za-z0-9-]+', args.tag)
    helper_ref = ref(Path(__file__))
    route_helper_ref = ref(BASE/'correspondence_routes34_v1.py')
    utility_ref = ref(UTILITIES)
    utilities = load_module('owner34_exact_patch_utilities', exact(utility_ref))
    index_ref = ref(INDEX)
    index = read(INDEX)
    old = read(OLD_INVENTORY, OLD_INVENTORY_SHA)
    inventory_ref = {'file': args.inventory, 'sha256': args.inventory_sha256}
    inventory = read(args.inventory, args.inventory_sha256)
    composition_ref = {'file': args.composition_review, 'sha256': args.composition_review_sha256}
    whole_approval = read(args.composition_review, args.composition_review_sha256)
    composition_data_ref = whole_approval['cumulative_candidate_review']
    composition = json.loads(exact(composition_data_ref).read_bytes())
    impact_ref = {'file': args.component_review, 'sha256': args.component_review_sha256}
    impact = read(args.component_review, args.component_review_sha256)
    ready_ref = {'file': args.readiness, 'sha256': args.readiness_sha256}
    ready = read(args.readiness, args.readiness_sha256)
    assert composition['status'].startswith('passed_') and composition['errors'] == [] and composition['protection_errors'] == []
    assert whole_approval['status'] == 'approved_exact_two_page_six_replacement_source_qualification_and_six_whole_candidate_correspondences'
    assert whole_approval['errors'] == []
    assert impact['status'].startswith('passed_') and impact['errors'] == []
    assert impact['existing_changed_proved_row_count'] == 0 and impact['additional_changed_ancestor_inventory_keys'] == []
    assert impact['carry_counts']['total'] == len(impact['existing_proved_unchanged_literal_carry_rows']) == 578
    assert ready['status'] == 'passed_three_actual_source88_future34_compiler_packets_unselected' and ready['errors'] == []
    assert len(ready['sources']) == 3 and sum(r['public_theorem_count'] for r in ready['sources']) == 114
    proposed = json.loads(exact(composition['fresh_candidate_inventory']).read_bytes())
    assert without_timestamp(inventory) == without_timestamp(proposed)
    assert inventory['counts'] == old['counts'] and set(inventory['source_sha256']) == set(old['source_sha256'])
    changed_pages = {n for n,h in inventory['source_sha256'].items() if h != old['source_sha256'][n]}
    assert changed_pages == {'SafeLearning/nn-in-the-loop.html', 'SafeLearning/primer-probability.html'}
    for n,h in inventory['source_sha256'].items():
        assert sha(path(n)) == h, (n, 'current Source90 must be actually applied')
    for page in composition['pages']:
        assert inventory['source_sha256'][page['source']] == page['candidate']['sha256']
        assert path(page['source']).read_bytes() == exact(page['candidate']).read_bytes()
    material = {r['key']:r for r in inventory['material_source_units']}
    old_material = {r['key']:r for r in old['material_source_units']}
    exercises = {r['key']:r for r in inventory['exercises']}
    old_exercises = {r['key']:r for r in old['exercises']}
    changed_material = {k for k in material if not same_literal(material[k], old_material[k])}
    changed_exercises = {k for k in exercises if not same_literal(exercises[k], old_exercises[k])}
    assert changed_material == set(NN_KEYS+[CONDITIONAL]) and changed_exercises == {NN_EXERCISE}
    assert composition['additional_changed_ancestor_inventory_literals'] == []
    assert set(composition['changed_physical_literal_keys']['material_source_units']) == changed_material
    assert set(composition['changed_physical_literal_keys']['exercises']) == changed_exercises
    iqc_ref, nn_ref = ref(IQC_SUMMARY), ref(NN_SUMMARY)
    iqc, nn = read(IQC_SUMMARY), read(NN_SUMMARY)
    approved_by_key = whole_approval['whole_correspondence_by_exact_candidate_key']
    assert set(approved_by_key) == set(NN_KEYS+[CONDITIONAL, NN_EXERCISE])
    assert all(r['whole_exact_candidate_literal_approved'] is True for r in approved_by_key.values())
    materials_routes, exercise_routes = assemble(iqc, nn, approved_by_key[CONDITIONAL]['precise_clause_routes'])
    assert set(materials_routes) == set(IQC_KEYS+NN_KEYS+[CONDITIONAL])
    for key in NN_KEYS:
        assert set(flatten(materials_routes[key])) == set(approved_by_key[key]['declarations'])
    tasks = {t['priority']:t for t in index['next_tasks'][:3]}
    family_peer = {'IQC21': tasks[1]['packet'], 'NN65': tasks[2]['packet'], 'Conditional28': tasks[3]['packet']}
    iqc_peer = json.loads(exact(family_peer['IQC21']).read_bytes())
    nn_peer = json.loads(exact(family_peer['NN65']).read_bytes())
    conditional_peer = json.loads(exact(family_peer['Conditional28']).read_bytes())
    assert iqc_peer['whole_exercise_decision']['entire_current_exercise_approved'] is True
    assert nn_peer['whole_exercise_decision']['prospective_whole_semantic_approved'] is True
    assert conditional_peer['prospective_whole_decision']['approved'] is True
    for key in IQC_KEYS:
        assert same_literal(material[key], iqc_peer['whole_literal_decisions'][key]['entire_literal'])
    assert same_literal(exercises[IQC_EXERCISE], iqc_peer['entire_current_exercise'])
    for t in tasks.values():
        exact(t['packet'])
        if 'narrow_peer' in t:
            exact(t['narrow_peer'])
    sources = {r['canonical_source']['file']:r for r in ready['sources']}
    protected = {r['file']:r['sha256'] for r in [helper_ref, route_helper_ref, utility_ref, index_ref,
                 ref(OLD_INVENTORY), inventory_ref, composition_ref, composition_data_ref, impact_ref, ready_ref, iqc_ref, nn_ref]}
    protected.update(inventory['source_sha256'])
    selected_ref = index['current_selected33']
    selected = json.loads(exact(selected_ref).read_bytes())
    protected[selected_ref['file']] = selected_ref['sha256']
    protected.update({n:r['sha256'] for n,r in selected['proof_files'].items()})
    assert len(selected['proof_files']) == 1261
    for n in ['verification/lean/SafeLearning.lean', 'verification/lean/AxiomAudit.lean',
              'book/coverage/applied-promotions.json', 'book/coverage/lean_names.py']:
        protected[n] = sha(path(n))
    for r in index['current_owner_refs'].values():
        exact(r)
        protected[r['file']] = r['sha256']
    for n,row in sources.items():
        exact(row['canonical_source'])
        protected[n] = row['canonical_source']['sha256']
        exact(row['readiness'])
        protected[row['readiness']['file']] = row['readiness']['sha256']
        assert {p['kind'] for p in row['actual_paired_records']} == {'standalone', 'named'}
        for pair in row['actual_paired_records']:
            assert pair['actual_exit_code'] == 0
            for key in ['actual_record', 'raw_log', 'source_snapshot']:
                exact(pair[key])
    def guard():
        for n,h in protected.items():
            assert sha(path(n)) == h, n
    guard()
    names = load_module('owner34_names', ROOT/'book/coverage/lean_names.py')
    declarations = {}
    for n,h in {**{n:r['sha256'] for n,r in selected['proof_files'].items()},
                **{n:r['canonical_source']['sha256'] for n,r in sources.items()}}.items():
        for d in names.declarations(exact({'file': n, 'sha256': h}).read_text()):
            assert d['name'] not in declarations
            declarations[d['name']] = {'source': {'file': n, 'sha256': h}, 'kind': d['kind']}
    used = {n for routes in materials_routes.values() for n in flatten(routes)}
    assert used <= set(declarations)
    mapping_path = BASE/('exact-subclaim-and-assumption-mapping-'+args.tag+'.json')
    new(mapping_path, {'status': 'prepared_exact_nine_whole_material_two_exercise_all_subclaim_routes_for_independent_review',
         'whole_material': [{'key': key, 'entire_current_literal': material[key], 'all_subclaim_correspondence': routes}
                            for key,routes in materials_routes.items()],
         'whole_exercises': [{'key': key, 'entire_current_literal': exercises[key],
                             'requirement_routes': routes} for key,routes in exercise_routes.items()],
         'independent_whole_mathematical_peers': family_peer,
         'qualification_current_source_composition_review': composition_ref,
         'existing_component_rebase_review': impact_ref,
         'canonical_readiness': ready_ref, 'route_helper': route_helper_ref,
         'used_declarations': {n:declarations[n] for n in sorted(used)},
         'finite_simulation_is_bounded_observation_not_all_time_proof': True,
         'overlapping_source_units_do_not_add_theorems': True, 'coverage_complete': False})
    replacements, owner_reports = [], []
    for domain in OWNERS:
        original_path = path('book/coverage/'+domain+'.json')
        raw = original_path.read_bytes()
        original = json.loads(raw)
        assert encode(original) == raw, (domain, 'original serialization must have an exact inverse')
        assert utilities.active_binding_errors(original, old_material, old_exercises, old) == []
        candidate = copy.deepcopy(original)
        rebased_material, rebased_exercises, promoted_material, promoted_exercises = [], [], [], []
        for page in candidate['scope_pages']:
            candidate['source_sha256'][page] = inventory['source_sha256'][page]
        for i,e in enumerate(candidate['exercises']):
            key = e['inventory_key']
            for k,target in [('source_sha256','source_sha256'), ('source_text_sha256','text_sha256'),
                             ('text_sha256','text_sha256'), ('source_text','source_text')]:
                if k in e:
                    e[k] = exercises[key][target]
            if e != original['exercises'][i]:
                rebased_exercises.append(key)
            if key not in exercise_routes:
                assert same_literal(exercises[key], old_exercises[key])
                continue
            assert domain == 'modules'
            route_map = exercise_routes[key]
            pending_indices = {j for j,c in enumerate(e['claims']) if c['status'] == 'pending'}
            assert pending_indices == set(route_map)
            for j,routes in route_map.items():
                c = e['claims'][j]
                previous = copy.deepcopy(c)
                if key == NN_EXERCISE and j == 1:
                    before = 'find the largest interval certified with local sectors and check it by simulation.'
                    after = 'find the supremal open interval obtained as the union of strict local-sector certificates, and check representative trajectories by simulation.'
                    assert c['statement_in_prose'].count(before) == 1 and after in exercises[key]['source_text']
                    c['statement_in_prose'] = c['statement_in_prose'].replace(before, after)
                c.update(status='definition_encoded' if key == IQC_EXERCISE and j == 0 else 'proved',
                         kind='reviewed_exact_current_mathematical_requirement',
                         lean_declarations=flatten(routes), hypotheses=assumptions(routes), remaining_gaps=[],
                         correspondence='This exact existing requirement is covered by its explicit current all_subclaim_correspondence and actual theorem domains. The complete independent exercise peer and exact current source qualification/composition are separate authorities. Any finite scalar simulation is an observational check, with all-time properties supplied by separate genuine proofs.',
                         all_subclaim_correspondence=copy.deepcopy(routes),
                         independent_whole_exercise_peer=family_peer['IQC21' if key == IQC_EXERCISE else 'NN65'],
                         qualification_and_current_source_review=composition_ref,
                         actual_canonical_readiness=ready_ref, original_pending_record=previous)
            e['status'] = 'complete_math'
            e['current_checkpoint34_whole_correspondence'] = {'exact_literal': exercises[key],
                   'mapping': ref(mapping_path), 'independent_whole_peer': family_peer['IQC21' if key == IQC_EXERCISE else 'NN65'],
                   'historical_component_decisions_preserved': True, 'remaining_mathematical_gaps': []}
            promoted_exercises.append(key)
        for i,c in enumerate(candidate['material_claims']):
            keys = c.get('source_unit_keys', [])
            if len(keys) != 1:
                assert not set(keys).intersection(changed_material), (domain,c['id'],'changed ancestor needs independent authority')
                continue
            key = keys[0]
            u = material[key]
            previous = original['material_claims'][i]
            for k,target in [('source_text','source_text'), ('source_text_sha256','text_sha256'),
                             ('text_sha256','text_sha256'), ('source_sha256','source_sha256')]:
                if k in c:
                    c[k] = u[target]
            if c != previous:
                rebased_material.append(c['id'])
            if key in changed_material:
                assert previous['status'] == 'pending', (domain,c['id'])
            if key not in materials_routes or c['status'] != 'pending':
                continue
            assert domain == ('applied' if key == CONDITIONAL else 'modules')
            routes = materials_routes[key]
            family = 'Conditional28' if key == CONDITIONAL else 'NN65' if key in NN_KEYS else 'IQC21'
            c.update(status='proved', kind='reviewed_entire_exact_current_mathematical_literal',
                     statement_in_prose=u['source_text'], source=u['source'], locator=u['locator'],
                     source_text=u['source_text'], source_text_sha256=u['text_sha256'], text_sha256=u['text_sha256'],
                     source_sha256=u['source_sha256'], lean_declarations=flatten(routes),
                     hypotheses=assumptions(routes), remaining_gaps=[],
                     correspondence='Every clause of this exact current literal is matched by the explicit all_subclaim_correspondence on its actual domain and the existing independent complete mathematical peer. Qualification/current-page and inventory identities have separate fresh review. Neighboring and parent units retain their existing status; overlapping literals share genuine proofs and add no theorem count.',
                     all_subclaim_correspondence=copy.deepcopy(routes),
                     independent_whole_literal_peer=family_peer[family],
                     qualification_and_current_source_review=composition_ref,
                     actual_canonical_readiness=ready_ref,
                     original_pending_record=copy.deepcopy(previous))
            if 'source_clauses' in c:
                c['source_clauses'] = [u['source_text']]
                c['source_clauses_scope'] = 'The exact complete current literal; the granular mathematical routes are all_subclaim_correspondence. Original pending split is preserved unchanged in original_pending_record.'
            promoted_material.append({'key': key, 'claim_id': c['id'], 'index': i, 'family': family})
        assert len(promoted_material) == {'foundations': 0, 'applied': 1, 'modules': 8, 'core': 0}[domain]
        assert set(promoted_exercises) == ({IQC_EXERCISE, NN_EXERCISE} if domain == 'modules' else set())
        for n,row in sources.items():
            applicable = domain == ('applied' if row['public_theorem_count'] == 28 else 'modules')
            if not applicable:
                continue
            assert n not in candidate['proof_files']
            if isinstance(candidate['proof_files'], list):
                candidate['proof_files'].append(n)
                candidate.setdefault('proof_sha256', {})[n] = row['canonical_source']['sha256']
            else:
                candidate['proof_files'][n] = row['canonical_source']['sha256']
                if 'proof_sha256' in candidate:
                    candidate['proof_sha256'][n] = row['canonical_source']['sha256']
        if 'current_inventory' in candidate:
            candidate['current_inventory'] = args.inventory
            candidate['current_inventory_sha256'] = args.inventory_sha256
        counts = candidate.get('counts', {})
        for key in ['exercise_status', 'exercise_statuses']:
            if key in counts:
                counts[key] = dict(Counter(e['status'] for e in candidate['exercises']))
        for key in ['material_claim_status', 'material_claim_statuses']:
            if key in counts:
                counts[key] = dict(Counter(c['status'] for c in candidate['material_claims']))
        if 'exercise_claim_status' in counts:
            counts['exercise_claim_status'] = dict(Counter(c['status'] for e in candidate['exercises'] for c in e['claims']))
        candidate['current_checkpoint34_identity'] = {'status': 'prepared_exact_Source90_reviewed_owner_candidate',
            'inventory': inventory_ref, 'baseline_Source88_inventory': ref(OLD_INVENTORY),
            'original_owner33': ref(original_path), 'qualification_composition_review': composition_ref,
            'existing_component_rebase_review': impact_ref, 'exact_mapping': ref(mapping_path),
            'whole_material_promotions': promoted_material, 'whole_exercises': promoted_exercises,
            'old_checkpoint33_identity_and_all_historical_evidence_preserved': True,
            'owner_installation_and_selected_aggregate_kernel_axiom_audit_pending': True, 'coverage_complete': False}
        assert utilities.active_binding_errors(candidate, material, exercises, inventory) == []
        assert len(candidate['exercises']) == len(original['exercises']) and len(candidate['material_claims']) == len(original['material_claims'])
        for a,b in zip(original['exercises'],candidate['exercises']):
            if a['inventory_key'] not in exercise_routes:
                assert {k:v for k,v in a.items() if k != 'source_sha256'} == {k:v for k,v in b.items() if k != 'source_sha256'}
        patches = utilities.difference_patches(original, candidate)
        restored = utilities.reverse_patches(candidate, patches)
        assert restored == original and hashlib.sha256(encode(restored)).hexdigest() == sha(original_path)
        output = BASE/(domain+'-candidate-'+args.tag+'.json')
        new(output, candidate)
        inverse = BASE/(domain+'-exact-inverse-'+args.tag+'.json')
        new(inverse, {'baseline': ref(original_path), 'candidate': ref(output), 'patches': patches,
                     'encoding': 'json indent2 ensure_asciiFalse plus newline; original bytes verified',
                     'inverse_restores_original_data_and_byte_sha256': True, 'inverse_restored_sha256': sha(original_path)})
        replacements.append({'destination': 'book/coverage/'+domain+'.json', 'before': ref(original_path),
                             'candidate': ref(output), 'exact_inverse': ref(inverse),
                             'approved_whole_promotions': promoted_material, 'approved_whole_exercises': promoted_exercises})
        owner_reports.append({'owner': domain, 'row_source_rebases': rebased_material,
                              'exercise_source_rebases': rebased_exercises, 'whole_material': promoted_material,
                              'whole_exercises': promoted_exercises, 'non_target_pending_and_historical_rows_preserved': True})
        del original, candidate, raw, restored
    guard()
    binding_path = BASE/('owner-candidate-binding-'+args.tag+'.json')
    new(binding_path, {'status': 'prepared_four_Source90_owner34_candidates_for_independent_review',
        'inventory': inventory_ref, 'baseline_inventory': ref(OLD_INVENTORY),
        'qualification_review': composition_ref, 'component_rebase_review': impact_ref,
        'canonical_readiness': ready_ref, 'exact_subclaims_and_assumptions': ref(mapping_path),
        'builder': helper_ref, 'route_helper': route_helper_ref, 'unchanged_original_patch_utility': utility_ref,
        'replacements': replacements, 'owner_rebases': owner_reports,
        'whole_material_promotions': 9, 'exercise_status_changes': 2, 'component_row_additions': 0,
        'changed_ancestors_without_independent_approval': [], 'historical_evidence_rewritten': 0,
        'candidate_installation_performed': False, 'old_owner_tree_or_runtime_cache_copied': False,
        'protected_input_sha256': protected, 'coverage_complete': False})
    worker = BASE/'validate_candidates34_v1.py'
    guard()
    log = BASE/('isolated-validator-'+args.tag+'.log')
    receipt = BASE/('isolated-validator-execution-'+args.tag+'.json')
    command = [sys.executable, '-B', str(worker), '--binding', str(binding_path), '--binding-sha256', sha(binding_path), '--tag', args.tag]
    start = time.monotonic(); started = datetime.now(timezone.utc).isoformat()
    with log.open('xb') as raw:
        result = subprocess.run(command, cwd=ROOT, stdout=raw, stderr=subprocess.STDOUT, check=False)
    elapsed = time.monotonic()-start
    finished = datetime.now(timezone.utc).isoformat()
    log.chmod(0o444)
    new(receipt, {'status': 'passed' if result.returncode == 0 else 'failed', 'actual_exit_code': result.returncode,
        'actual_command': command, 'actual_workdir': str(ROOT), 'started_at_utc': started,
        'finished_at_utc': finished, 'elapsed_seconds': elapsed, 'raw_log': ref(log),
        'validator_worker': ref(worker), 'candidate_binding': ref(binding_path),
        'validator_source': ref('book/coverage/validate.py'), 'coverage_complete': False})
    guard()
    assert result.returncode == 0, str(receipt)
    audit = read('book/coverage/checks/checkpoint34-ledgers/isolated-ledger-audit-'+args.tag+'.json')
    print(json.dumps({'status': 'passed', 'binding': ref(binding_path), 'execution': ref(receipt),
                      'actual_counts': audit['counts'], 'coverage_complete': False}), flush=True)

if __name__ == '__main__':
    main()

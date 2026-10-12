#!/usr/bin/env python3
"""Prepare isolated owner33 candidates with exact inverse and active identity checks.

The input must be Root's actually applied complete inventory. This helper never
installs an owner, mutates the site/inventory, or asserts aggregate readiness.
Only active source-unit fields and genuine current inventory identities are
rebased. Historical evidence, embedded prior source bytes and review times are
preserved. Candidate output paths are new and exclusive.
"""
from pathlib import Path
from collections import Counter
from datetime import datetime, timezone
import argparse
import contextlib
import copy
import hashlib
import importlib.util
import json
import sys
import tempfile
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(BASE))
from correspondence_routes_v2 import ROUTES, NODE922_COMPONENT

OWNERS = ['foundations', 'applied', 'modules', 'core']
REVIEW = ROOT/'book/coverage/checks/checkpoint33-review/independent-seven-qualifier-cumulative-review-v1.json'
COMPONENT_REVIEW = ROOT/'book/coverage/checks/checkpoint33-review/independent-18-carried-basics-component-rebase-v1.json'
OLD_INVENTORY = ROOT/'book/coverage/inventory-after-correction81.json'
NODE922 = 'primer-basics.html::node-922'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def ref(path):
    path = path.resolve()
    name = path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else str(path)
    return {'file': name, 'sha256': sha(path), 'bytes': path.stat().st_size}


def load(path):
    return json.loads(path.read_bytes())


def encode(data):
    return (json.dumps(data, indent=2, ensure_ascii=False)+'\n').encode()


def new(path, data):
    assert path.is_relative_to(BASE) and not path.exists() and not path.is_symlink(), path
    with path.open('xb') as out:
        out.write(encode(data))


def resolve_reference(value):
    path = Path(value['file'])
    return path if path.is_absolute() else ROOT/path


def verify_reference(value):
    path = resolve_reference(value)
    assert sha(path) == value['sha256'], value
    if 'bytes' in value:
        assert path.stat().st_size == value['bytes'], value
    return path


def current_records_equal(a, b):
    return {k:v for k,v in a.items() if k != 'source_sha256'} == {
        k:v for k,v in b.items() if k != 'source_sha256'}


def flattened_declarations(routes):
    return sorted({n for entry in routes for n in entry['lean_declarations']})


def flattened_hypotheses(routes):
    return list(dict.fromkeys(h for entry in routes for h in entry['hypotheses']))


def whole_peer(mapping):
    return mapping.get('whole_peer', mapping.get('whole_mathematical_peer'))


def active_binding_errors(data, material_index, exercise_index, inventory):
    errors = []
    for p in data['scope_pages']:
        if data['source_sha256'][p] != inventory['source_sha256'][p]:
            errors.append('stale owner page: '+p)
    for e in data['exercises']:
        original = exercise_index[e['inventory_key']]
        for k, target in [('source_text','source_text'), ('source_text_sha256','text_sha256'),
                          ('text_sha256','text_sha256'), ('source_sha256','source_sha256')]:
            if k in e and e[k] != original[target]:
                errors.append(e['inventory_key']+': stale active '+k)
    for c in data['material_claims']:
        keys = c.get('source_unit_keys', [])
        if len(keys) != 1:
            continue
        original = material_index[keys[0]]
        for k, target in [('source_text','source_text'), ('source_text_sha256','text_sha256'),
                          ('text_sha256','text_sha256'), ('source_sha256','source_sha256'),
                          ('source','source'), ('locator','locator')]:
            if k in c and c[k] != original[target]:
                errors.append(c['id']+': stale active '+k)
    return errors


def difference_patches(before, after, pointer=()):
    """Minimal exact forward/inverse patches; never copy entire archive trees."""
    patches = []
    if isinstance(before, dict) and isinstance(after, dict):
        for key in before:
            if key not in after:
                patches.append({'pointer': list(pointer+(key,)), 'before_exists': True,
                                'before': before[key], 'after_exists': False})
            else:
                patches.extend(difference_patches(before[key], after[key], pointer+(key,)))
        for key in after:
            if key not in before:
                patches.append({'pointer': list(pointer+(key,)), 'before_exists': False,
                                'after_exists': True, 'after': after[key]})
    elif isinstance(before, list) and isinstance(after, list) and len(before) == len(after):
        for i, (a,b) in enumerate(zip(before,after)):
            patches.extend(difference_patches(a,b,pointer+(i,)))
    elif before != after:
        # Appended component rows are represented without copying every old row.
        if isinstance(before,list) and isinstance(after,list) and after[:len(before)] == before:
            for i in range(len(before), len(after)):
                patches.append({'pointer':list(pointer+(i,)), 'before_exists':False,
                                'after_exists':True, 'after':after[i]})
        elif isinstance(before,list) and isinstance(after,list) and len(after)>len(before):
            for i, (a,b) in enumerate(zip(before,after)):
                patches.extend(difference_patches(a,b,pointer+(i,)))
            for i in range(len(before),len(after)):
                patches.append({'pointer':list(pointer+(i,)), 'before_exists':False,
                                'after_exists':True, 'after':after[i]})
        else:
            patches.append({'pointer':list(pointer), 'before_exists':True,
                            'before':before, 'after_exists':True, 'after':after})
    return patches


def reverse_patches(candidate, patches):
    restored = copy.deepcopy(candidate)
    for patch in reversed(patches):
        parent = restored
        for key in patch['pointer'][:-1]:
            parent = parent[key]
        key = patch['pointer'][-1]
        if patch['after_exists']:
            assert parent[key] == patch['after']
        else:
            assert key not in parent
        if patch['before_exists']:
            parent[key] = copy.deepcopy(patch['before'])
        elif isinstance(parent,list):
            assert key == len(parent)-1
            parent.pop()
        else:
            del parent[key]
    return restored


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inventory', type=Path, required=True)
    parser.add_argument('--readiness', type=Path, required=True)
    parser.add_argument('--tag', default='v2')
    args = parser.parse_args()
    assert args.tag.replace('-', '').isalnum(), args.tag
    tick = time.monotonic(); started = datetime.now(timezone.utc).isoformat()
    inventory_path = args.inventory.resolve(); readiness_path = args.readiness.resolve()
    assert inventory_path.is_relative_to(ROOT)
    inventory = load(inventory_path); old_inventory = load(OLD_INVENTORY)
    review = load(REVIEW); components = load(COMPONENT_REVIEW); ready = load(readiness_path)
    assert review['errors'] == [] and components['errors'] == [] and ready['errors'] == []
    assert ready['source_count'] == 7 and ready['public_theorem_count'] == 78
    assert ready['public_name_count'] == 93 and ready['actual_compiler_command_count'] == 14
    assert components['node922_whole_still_pending'] is True
    assert len(components['components']) == 18
    verify_reference(review['carried_18_Basics_component_rebase_authority'])
    source_rows = {r['family']:r for r in ready['sources']}
    assert len(source_rows) == 7
    scope_plan = review['whole_statement_mappings_conditional_on_exact_application_and_canonical_audit']
    approved = review['approved_prospective_whole_keys']
    assert len(approved) == 10 and set(approved) == set(ROUTES)
    assert {m['key'] for m in scope_plan} == set(approved)
    changed = review['exact_changed_physical_inventory_records']['material_source_units']['cumulative_seven']
    assert len(changed) == 10 and NODE922 in changed
    assert review['exact_changed_physical_inventory_records']['exercises']['cumulative_seven'] == []
    assert inventory['counts'] == old_inventory['counts']
    assert set(inventory['source_sha256']) == set(old_inventory['source_sha256'])
    changed_pages = {k for k in inventory['source_sha256'] if inventory['source_sha256'][k] != old_inventory['source_sha256'][k]}
    assert changed_pages == {'SafeLearning/primer-basics.html','SafeLearning/primer-linalg.html'}
    for page, r in review['exact_candidate_pages'].items():
        assert inventory['source_sha256'][page] == r['sha256']
        assert (ROOT/page).read_bytes() == verify_reference(r).read_bytes()
    for page, h in inventory['source_sha256'].items():
        assert sha(ROOT/page) == h
    old_material = {u['key']:u for u in old_inventory['material_source_units']}
    material = {u['key']:u for u in inventory['material_source_units']}
    old_exercises = {u['key']:u for u in old_inventory['exercises']}
    exercises = {u['key']:u for u in inventory['exercises']}
    assert set(material) == set(old_material) and set(exercises) == set(old_exercises)
    actual_changed = {k for k in material if not current_records_equal(material[k],old_material[k])}
    assert actual_changed == set(changed), sorted(actual_changed)
    assert all(current_records_equal(exercises[k],old_exercises[k]) for k in exercises)
    for m in scope_plan:
        assert material[m['key']] == m['entire_candidate_literal'], m['key']
        family = source_rows[m['family']]
        assert family['original_tmp_source']['sha256'] == m['source']['sha256']
        for authority in ['whole_peer', 'whole_mathematical_peer', 'distinct_narrow_peer', 'exact_proposal']:
            if authority in m:
                verify_reference(m[authority])

    # Guard live authorized inputs throughout this isolated preparation.
    protected_paths = [ROOT/('book/coverage/'+o+'.json') for o in OWNERS]
    protected_paths += [ROOT/'book/coverage/applied-promotions.json', ROOT/'book/coverage/inventory.json',
                        inventory_path, OLD_INVENTORY, REVIEW, COMPONENT_REVIEW, readiness_path]
    protected_paths += [ROOT/p for p in inventory['source_sha256']]
    canonical_refs = []
    for row in ready['sources']:
        canonical = ROOT/row['canonical_source']
        assert sha(canonical) == row['original_tmp_source']['sha256']
        canonical_refs.append(ref(canonical)); protected_paths.append(canonical)
    protected = {ref(p)['file']:sha(p) for p in protected_paths}

    def guard():
        for name, h in protected.items():
            p=Path(name); p=p if p.is_absolute() else ROOT/p
            assert sha(p) == h, name

    guard()
    sys.path.insert(0, str(ROOT/'book/coverage'))
    from lean_names import declarations
    declaration_index = {}
    for path in sorted((ROOT/'verification/lean/SafeLearning').glob('*.lean')):
        if path.name == 'Smoke.lean':
            continue
        for d in declarations(path.read_text()):
            assert d['name'] not in declaration_index, d['name']
            declaration_index[d['name']] = {'source':ref(path), 'kind':d['kind']}
    for key, routes in ROUTES.items():
        for n in flattened_declarations(routes):
            assert n in declaration_index, (key,n)
    for n in flattened_declarations(NODE922_COMPONENT):
        assert n in declaration_index, n
    route_report = {
        'status':'prepared_exact_ten_whole_literal_clause_and_assumption_mapping_for_independent_root_review',
        'review':ref(REVIEW), 'canonical_readiness':ref(readiness_path),
        'source':ref(BASE/'correspondence_routes_v2.py'),
        'whole_units':[{'key':m['key'], 'family':m['family'],
                       'entire_current_literal':material[m['key']],
                       'all_subclaim_correspondence':ROUTES[m['key']],
                       'source_context_support':m.get('definitions_and_support_statement_scope',{}),
                       'independent_whole_peer':whole_peer(m),
                       'independent_narrow_and_cumulative_review':ref(REVIEW)} for m in scope_plan],
        'node922_component_routes':NODE922_COMPONENT,
        'used_declarations':{n:declaration_index[n] for n in sorted({n for r in list(ROUTES.values())+[NODE922_COMPONENT] for n in flattened_declarations(r)})},
        'overlapping_units_are_not_distinct_proof_counts':True,
        'coverage_complete':False,
    }
    route_path = BASE/('exact-subclaim-and-assumption-mapping-'+args.tag+'.json')
    new(route_path,route_report)
    candidates = {}; replacements=[]; owner_reports=[]
    for owner in OWNERS:
        original_path=ROOT/('book/coverage/'+owner+'.json')
        raw=original_path.read_bytes(); original=json.loads(raw)
        assert encode(original) == raw, (owner,'inverse serialization')
        assert active_binding_errors(original,old_material,old_exercises,old_inventory) == [], owner
        candidate=copy.deepcopy(original)
        row_rebases=[]; exercise_rebases=[]; carried_components=[]
        for page in candidate['scope_pages']:
            candidate['source_sha256'][page] = inventory['source_sha256'][page]
        for e in candidate['exercises']:
            if 'source_sha256' in e:
                before=e['source_sha256']; e['source_sha256']=exercises[e['inventory_key']]['source_sha256']
                if e['source_sha256'] != before:
                    exercise_rebases.append(e['inventory_key'])
        for i,c in enumerate(candidate['material_claims']):
            keys=c.get('source_unit_keys',[])
            if len(keys) != 1:
                assert not set(keys)&set(changed), (owner,c['id'],'unreviewed changed multi-source ancestor')
                continue
            key=keys[0]; u=material[key]; before=original['material_claims'][i]
            for k,target in [('source_text','source_text'),('source_text_sha256','text_sha256'),
                             ('text_sha256','text_sha256'),('source_sha256','source_sha256')]:
                if k in c:
                    c[k]=u[target]
            if before != c:
                row_rebases.append({'claim_id':c['id'],'material_key':key,'index':i,
                                    'literal_changed':key in changed,'status_unchanged':True})
            if key in changed and before['status'] != 'pending':
                assert owner=='foundations' and before['status']=='proved'
                approved_components=[r for r in components['components'] if r['claim_id']==c['id']]
                assert len(approved_components)==1, (owner,c['id'],'changed closed ancestor has no independent rebase')
                decision=approved_components[0]
                assert decision['original_row']==before and decision['candidate_row']==c
                assert decision['statements_hypotheses_declarations_status_and_original_correspondence_unchanged']
                carried_components.append(c['id'])
        promoted=[]
        if owner=='foundations':
            assert len(carried_components)==18
            for mapping in scope_plan:
                key=mapping['key']; routes=ROUTES[key]
                pending=[(i,c) for i,c in enumerate(candidate['material_claims'])
                         if c.get('source_unit_keys')==[key] and c['status']=='pending']
                assert len(pending)==1, (key,len(pending))
                i,c=pending[0]
                assert c['id'] in mapping['existing_pending_claim_ids']
                c.update(status='proved', kind='reviewed_entire_current_mathematical_literal',
                         statement_in_prose=material[key]['source_text'],
                         lean_declarations=flattened_declarations(routes),
                         hypotheses=flattened_hypotheses(routes), remaining_gaps=[],
                         correspondence='Every mathematical clause of this exact qualified current literal is covered by the explicit all_subclaim_correspondence with its actual domains. The original independent whole peer and new cumulative parser review are preserved. Overlapping excerpt rows share clauses and do not count as independent theorems. Contextual source attribution and pedagogical instructions retain their separately reviewed factual scope. No neighboring unit or parent exercise is promoted.',
                         all_subclaim_correspondence=copy.deepcopy(routes),
                         independent_whole_literal_peer=whole_peer(mapping),
                         qualification_and_current_source_review=ref(REVIEW),
                         actual_canonical_readiness=ref(readiness_path),
                         original_pending_record=copy.deepcopy(original['material_claims'][i]))
                support=mapping.get('definitions_and_support_statement_scope',{})
                if support:
                    c['reviewed_source_context_support']=copy.deepcopy(support)
                promoted.append({'key':key,'claim_id':c['id'],'index':i,'family':mapping['family']})
            pending922=[c for c in candidate['material_claims'] if c.get('source_unit_keys')==[NODE922] and c['status']=='pending']
            assert len(pending922)==1
            remaining=review['node922']['remaining']
            pending922[0].update(statement_in_prose='The qualified exact-envelope, numerical cutoff, asymptotic and logarithmic-curve clauses have explicit proved components. The linked algorithm and application-domain clauses still require their own reviewed correspondence.',
                                 remaining_gaps=remaining,
                                 correspondence='Only the bounded exact-envelope and logarithmic-curve components are established here. The unchanged linked Module2 interior-point complexity, Module8 algorithm-rate domain and PrimerB gradient-descent associations keep this entire unit pending.',
                                 qualification_and_current_source_review=ref(REVIEW))
            component=dict(source_unit_keys=[NODE922],source=material[NODE922]['source'],
                           locator=material[NODE922]['locator'],source_text=material[NODE922]['source_text'],
                           source_text_sha256=material[NODE922]['text_sha256'],
                           source_sha256=material[NODE922]['source_sha256'],
                           id=NODE922+'::qualified-envelope-and-log-curve-component33',
                           statement_in_prose='The exact positive geometric and reciprocal-power envelopes have the stated tolerance certificates, numerical first indices and logarithmic plot properties on their explicit domains.',
                           kind='reviewed_mathematical_subclaim',status='proved',
                           lean_declarations=flattened_declarations(NODE922_COMPONENT),
                           hypotheses=flattened_hypotheses(NODE922_COMPONENT),
                           correspondence='Only the explicit all_subclaim_correspondence of the qualified envelopes and their logarithmic curves is proved. The entire enclosing literal remains pending for its linked actual algorithm/application statements.',
                           remaining_gaps=[],all_subclaim_correspondence=copy.deepcopy(NODE922_COMPONENT),
                           independent_whole_and_component_peer=next(whole_peer(m) for m in scope_plan if m['family']=='Basics12'),
                           qualification_and_current_source_review=ref(REVIEW),
                           actual_canonical_readiness=ref(readiness_path))
            assert component['id'] not in {c['id'] for c in candidate['material_claims']}
            candidate['material_claims'].append(component)
            for row,r in zip(ready['sources'],canonical_refs):
                path=row['canonical_source']
                if isinstance(candidate['proof_files'],list):
                    assert path not in candidate['proof_files']
                    candidate['proof_files'].append(path); candidate['proof_sha256'][path]=r['sha256']
                else:
                    assert path not in candidate['proof_files']; candidate['proof_files'][path]=r['sha256']
            candidate['counts']['material_claim_statuses']=dict(Counter(c['status'] for c in candidate['material_claims']))
        # Historical identity manifests, decisions, native commands and times
        # are deliberately not traversed or relabeled.
        if 'current_inventory' in candidate:
            candidate['current_inventory']=ref(inventory_path)['file']
            candidate['current_inventory_sha256']=sha(inventory_path)
        candidate['current_checkpoint33_identity']={
            'status':'prepared_exact_actual_source_inventory_and_reviewed_owner_candidate',
            'inventory':ref(inventory_path), 'baseline_inventory':ref(OLD_INVENTORY),
            'original_owner':ref(original_path), 'qualification_review':ref(REVIEW),
            'exact_mapping':ref(route_path),
            'changed_source_unit_keys':sorted(set(changed)&{u['key'] for u in material.values() if u['source'] in candidate['scope_pages']}),
            'unchanged_owned_exercise_statements':len(candidate['exercises']),
            'independently_rebased_existing_component_ids':carried_components,
            'approved_whole_promotions':promoted,
            'node922_whole_pending':True,
            'historical_reviews_source_bytes_native_times_and_evidence_preserved':True,
            'actual_selected_aggregate_and_owner_installation_pending':True,
            'coverage_complete':False,
        }
        assert active_binding_errors(candidate,material,exercises,inventory)==[], owner
        assert len(candidate['exercises'])==len(original['exercises'])
        for a,b in zip(original['exercises'],candidate['exercises']):
            assert {k:v for k,v in a.items() if k!='source_sha256'} == {k:v for k,v in b.items() if k!='source_sha256'}
        patches=difference_patches(original,candidate)
        restored=reverse_patches(candidate,patches)
        assert restored == original and digest(encode(restored))==digest(raw)
        output=BASE/(owner+'-candidate-'+args.tag+'.json')
        new(output,candidate);candidates[owner]=output
        inverse=BASE/(owner+'-exact-inverse-'+args.tag+'.json')
        new(inverse,{'baseline':ref(original_path),'candidate':ref(output),
                     'encoding':'json indent2 ensure_asciiFalse plus one newline; exact original bytes verified',
                     'patches':patches,'inverse_restores_original_data_and_byte_sha256':True,
                     'inverse_restored_sha256':digest(encode(restored))})
        replacements.append({'destination':'book/coverage/'+owner+'.json','before':ref(original_path),
                             'candidate':ref(output),'exact_inverse':ref(inverse),
                             'approved_whole_promotions':promoted})
        owner_reports.append({'owner':owner,'row_source_rebases':row_rebases,
                              'exercise_source_fingerprint_rebases':exercise_rebases,
                              'existing_closed_components_rebased':carried_components,
                              'whole_promotions':promoted,
                              'appended_component_count':1 if owner=='foundations' else 0,
                              'unchanged_exercise_statements_and_claims':True,
                              'exact_inverse':ref(inverse)})
        del original,candidate,restored,raw
    # Applied promotions has no active current inventory identity and owns only
    # unchanged pages. Its old inventory-bearing fields are historical records.
    promotions=load(ROOT/'book/coverage/applied-promotions.json')
    assert 'current_inventory' not in promotions and 'current_inventory_sha256' not in promotions
    assert all(not k.startswith(('primer-basics.html','primer-linalg.html')) for k in promotions['exercises'])
    assert all(not k.startswith(('primer-basics.html','primer-linalg.html')) for k in promotions['material'])
    binding_path=BASE/('owner-candidate-binding-'+args.tag+'.json')
    new(binding_path,{'status':'prepared_isolated_four_owner_candidates_for_root_independent_review',
                      'inventory':ref(inventory_path),'qualification_review':ref(REVIEW),
                      'component_rebase_review':ref(COMPONENT_REVIEW),
                      'canonical_readiness':ref(readiness_path),'exact_subclaims_and_assumptions':ref(route_path),
                      'replacements':replacements,'owner_rebases':owner_reports,
                      'whole_material_promotions':10,'component_row_additions':1,
                      'exercise_status_or_statement_changes':0,
                      'mathematical_correspondence_broken_by_changed_ancestors':[],
                      'applied_promotions_unchanged':ref(ROOT/'book/coverage/applied-promotions.json'),
                      'applied_promotions_reason':'No active current inventory identity; all owned source/exercise/material bytes exact. Embedded historical inventory references are preserved.',
                      'historical_review_and_native_artifact_bytes_rewritten':0,
                      'candidate_installation_performed':False,'coverage_complete':False})
    guard()
    spec=importlib.util.spec_from_file_location('checkpoint33_isolated_validator',ROOT/'book/coverage/validate.py')
    validator=importlib.util.module_from_spec(spec);spec.loader.exec_module(validator)
    raw_log=BASE/('isolated-validator-'+args.tag+'.log')
    with raw_log.open('x') as out, contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
        with tempfile.TemporaryDirectory(prefix='safetybased-checkpoint33-seven-owner-preflight-') as directory:
            isolated=Path(directory);(isolated/'book/coverage').mkdir(parents=True);(isolated/'verification').mkdir()
            (isolated/'SafeLearning').symlink_to(ROOT/'SafeLearning',target_is_directory=True)
            (isolated/'verification/lean').symlink_to(ROOT/'verification/lean',target_is_directory=True)
            (isolated/'book/coverage/inventory.json').symlink_to(inventory_path)
            for owner in OWNERS:
                (isolated/'book/coverage'/(owner+'.json')).symlink_to(candidates[owner])
            validator.ROOT=isolated;report=validator.validate()
            print(json.dumps({k:report[k] for k in ['integrity_status','mathematical_coverage_complete','counts','errors']},indent=2))
    audit=BASE/('isolated-ledger-audit-'+args.tag+'.json');new(audit,report)
    passed=report['integrity_status']=='passed' and report['errors']==[] and not report['mathematical_coverage_complete']
    assert report['counts']['material_review_statuses']=={'reviewed':4851,'pending':7923}
    assert report['counts']['statuses']['exercise:complete_math']==536
    assert report['counts']['statuses']['exercise:partial']==8
    assert report['counts']['statuses']['exercise:pending']==12
    guard()
    execution=BASE/('isolated-validator-execution-'+args.tag+'.json')
    new(execution,{'status':'passed' if passed else 'failed','actual_exit_code':0 if passed else 1,
                   'command':[sys.executable,'-B',str(Path(__file__).relative_to(ROOT)),*sys.argv[1:]],
                   'actual_workdir':str(ROOT),'started_at_utc':started,
                   'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,
                   'actual_helper':ref(Path(__file__)),'mapping_helper':ref(BASE/'correspondence_routes_v2.py'),
                   'validator_source':ref(ROOT/'book/coverage/validate.py'),
                   'actual_validator_invocation':'Unchanged repository validator invoked with ROOT set to a disposable symlink tree containing exactly four candidates and the actually applied inventory/site/canonical Lean sources.',
                   'raw_log':ref(raw_log),'audit':ref(audit),'binding':ref(binding_path),
                   'all_active_source_text_and_fingerprint_checks_passed':True,
                   'exact_inverse_each_owner_restores_original_bytes':True,
                   'protected_inputs_unchanged':True,'candidate_installation_performed':False,
                   'source_or_inventory_or_historical_artifact_edits_performed':False,
                   'counts':report['counts'],'coverage_complete':False})
    print(json.dumps({'status':'passed' if passed else 'failed','binding':ref(binding_path),
                      'execution':ref(execution),'counts':report['counts']},indent=2))
    assert passed


if __name__ == '__main__':
    main()

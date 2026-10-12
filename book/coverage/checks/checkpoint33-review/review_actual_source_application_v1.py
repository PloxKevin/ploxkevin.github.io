#!/usr/bin/env python3
from pathlib import Path
from datetime import datetime, timezone
import json
import tempfile
from review_six_qualifier_cumulative_v1 import ROOT, OUT, ref, exact, read_json, sha_bytes, literal_fields, run_inventory

APPLICATION = ROOT / 'reports/full-coverage/checkpoint33-source-corrections82-88-v1.json'
MANIFEST = ROOT / 'reports/full-coverage/checkpoint-32-manifest.json'
SELECTION = ROOT / 'reports/full-coverage/checkpoint-32-selection.json'
REGISTRY = ROOT / 'book/coverage/material-corrections.json'
HISTORY = ROOT / 'reports/full-coverage/source-history/checkpoint33-before-corrections82-88-v1'
HELPER = ROOT / 'book/coverage/checks/checkpoint33-root/apply_sources33_v2.py'


def main():
    result_path = OUT / 'independent-actual-source82-88-application-review-v1.json'
    assert not result_path.exists()
    application = json.loads(APPLICATION.read_bytes())
    review = read_json(application['independent_cumulative_review'])
    manifest = json.loads(MANIFEST.read_bytes())
    selection = json.loads(SELECTION.read_bytes())
    registry = json.loads(REGISTRY.read_bytes())
    original_registry_path = HISTORY / 'book/coverage/material-corrections.json'
    original_registry = json.loads(original_registry_path.read_bytes())
    assert ref(original_registry_path)['sha256'] == manifest['working_inputs_sha256']['book/coverage/material-corrections.json']
    assert registry['corrections'][:81] == original_registry['corrections']
    assert len(registry['corrections']) == 88 and len(application['applications']) == 7
    assert registry['corrections'][81:] == application['applications']
    assert [c['correction_id'] for c in application['applications']] == list(range(82, 89))
    helper = HELPER.read_text()
    for marker in ('old_owners_and_selected32_proofs_preserved=True',
                   'corrections[\'corrections\'][:81] == original_corrections',
                   'assert inverse.encode() == before',
                   'assert all(sha(ROOT / n) == h for n, h in held.items())',
                   'tempfile.TemporaryDirectory'):
        assert marker in helper
    execution_path = ROOT / 'reports/full-coverage/apply-source33-execution-v2.json'
    execution = json.loads(execution_path.read_bytes())
    assert execution['actual_exit_code'] == 0
    execution_refs = []
    for field, value in execution.items():
        if isinstance(value, dict) and 'file' in value and 'sha256' in value:
            exact(value)
            execution_refs.append({'role': field, 'reference': value})
    steps = []
    previous_inventory = None
    for correction in application['applications']:
        ordinal = correction['correction_id']
        before_page = exact(correction['historical_source']).read_bytes()
        assert sha_bytes(before_page) == correction['before_sha256']
        page = before_page
        for replacement in correction['replacements']:
            old, new = replacement['before'].encode(), replacement['after'].encode()
            assert page.count(old) == 1 and page.count(new) == 0
            page = page.replace(old, new, 1)
        assert sha_bytes(page) == correction['after_sha256']
        inverse = page
        for replacement in reversed(correction['replacements']):
            old, new = replacement['before'].encode(), replacement['after'].encode()
            assert inverse.count(new) == 1
            inverse = inverse.replace(new, old, 1)
        assert inverse == before_page
        before_inventory = read_json(correction['inventory_before'])
        after_inventory = read_json(correction['inventory_after'])
        if previous_inventory is not None:
            assert before_inventory == previous_inventory
        else:
            assert correction['inventory_before']['sha256'] == manifest['working_inputs_sha256']['book/coverage/inventory.json']
        assert before_inventory['counts'] == after_inventory['counts']
        source = correction['source']
        assert before_inventory['source_sha256'][source] == correction['before_sha256']
        assert after_inventory['source_sha256'] == {**before_inventory['source_sha256'], source: correction['after_sha256']}
        changed = {}
        for kind in ('exercises', 'material_source_units'):
            before = {r['key']: r for r in before_inventory[kind]}
            after = {r['key']: r for r in after_inventory[kind]}
            assert before.keys() == after.keys()
            changed[kind] = sorted(k for k in before if literal_fields(before[k]) != literal_fields(after[k]))
            assert all(after[k]['source_sha256'] == after_inventory['source_sha256'][after[k]['source']] for k in after)
        assert changed['exercises'] == []
        assert all(next(r for r in after_inventory['material_source_units'] if r['key'] == key)['source'] == source
                   for key in changed['material_source_units'])
        native = read_json(correction['actual_fresh_parser'])
        assert native['actual_exit_code'] == 0 and native['parser_ROOT_and_OUT_isolated']
        assert native['candidate_page_sha256'] == correction['after_sha256']
        assert Path(native['actual_workdir']).is_relative_to('/tmp')
        assert Path(native['actual_command'][-1]).parent.parent == Path(native['actual_workdir'])
        assert exact(native['raw_log']).read_text().strip() == 'Inventoried 556 exercises and 12774 mathematical source units on 29 pages.'
        exact(native['parser'])
        for field in ('source_proposal', 'independent_semantic_review', 'cumulative_independent_review'):
            exact(correction[field])
        previous_inventory = after_inventory
        steps.append({'correction_id': ordinal, 'source': source,
            'before_sha256': correction['before_sha256'], 'after_sha256': correction['after_sha256'],
            'changed_literal_keys': changed, 'historical_page': correction['historical_source'],
            'fresh_parser': correction['actual_fresh_parser'], 'exact_inverse': True})
    final_inventory = read_json(application['final_inventory'])
    assert final_inventory == previous_inventory
    assert application['final_inventory']['sha256'] == '87b8457614b7a9a127c171e1a95adf43bd94d05de6d63921b5e69493e3822202'
    for source, record in review['exact_candidate_pages'].items():
        assert (ROOT / source).read_bytes() == exact(record).read_bytes()
        assert final_inventory['source_sha256'][source] == record['sha256']
    current_pages = {name: (ROOT / name).read_bytes() for name in final_inventory['source_sha256']}
    historical_chain = []
    for position in range(88, 0, -1):
        correction = registry['corrections'][position - 1]
        source = correction['source']
        page = current_pages[source]
        assert sha_bytes(page) == correction['after_sha256'], (position, source)
        substitutions = correction.get('replacements', [{'before': correction.get('before'), 'after': correction.get('after')}])
        for substitution in reversed(substitutions):
            old, new = substitution['before'].encode(), substitution['after'].encode()
            assert page.count(new) == 1, (position, source)
            page = page.replace(new, old, 1)
        assert sha_bytes(page) == correction['before_sha256'], (position, source)
        current_pages[source] = page
        historical_chain.append({'correction_ordinal': position, 'source': source,
                                 'after_sha256': correction['after_sha256'],
                                 'restored_before_sha256': correction['before_sha256']})
        if position == 82:
            assert {k: sha_bytes(v) for k, v in current_pages.items()} == {
                k: v for k, v in manifest['working_inputs_sha256'].items()
                if k in final_inventory['source_sha256']}
    old_owners = {}
    for owner in ('foundations', 'applied', 'modules', 'core', 'applied-promotions'):
        path = ROOT / f'book/coverage/{owner}.json'
        assert ref(path)['sha256'] == manifest['working_inputs_sha256'][str(path.relative_to(ROOT))]
        old_owners[owner] = ref(path)
    for name, record in selection['proof_files'].items():
        assert sha_bytes((ROOT / name).read_bytes()) == record['sha256'], name
    unaffected_assets = {}
    for name, fingerprint in manifest['working_inputs_sha256'].items():
        if name.startswith('SafeLearning/') and name not in review['exact_candidate_pages']:
            assert sha_bytes((ROOT / name).read_bytes()) == fingerprint
            unaffected_assets[name] = fingerprint
    tree = Path(tempfile.mkdtemp(prefix='checkpoint33-postapplication-independent-full29-', dir='/tmp'))
    (tree / 'SafeLearning').mkdir()
    (tree / 'book').mkdir()
    for name in final_inventory['source_sha256']:
        (tree / name).write_bytes((ROOT / name).read_bytes())
    for name in ('inventory_claims.py', 'validate.py'):
        (tree / 'book' / name).write_bytes((ROOT / 'book' / name).read_bytes())
    parsed, parser_native = run_inventory(tree, 'actual-live-postapplication')
    for field in ('counts', 'source_sha256', 'exercises', 'material_source_units'):
        assert parsed[field] == final_inventory[field]
    changed_union = sorted({k for step in steps for k in step['changed_literal_keys']['material_source_units']})
    assert changed_union == application['changed_physical_keys'] == review['exact_changed_physical_inventory_records']['material_source_units']['cumulative_seven']
    report = {'status': 'passed_independent_actual_source82_88_application_full_registry88_chain_and_protected_inputs',
        'errors': [], 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
        'application': ref(APPLICATION), 'actual_application_helper_read': ref(HELPER),
        'actual_application_execution': ref(execution_path), 'execution_references_checked': execution_refs,
        'preapplication_registry_preserved_exact': ref(original_registry_path),
        'current_registry': ref(REGISTRY), 'all88_full_page_inverse_hash_steps': historical_chain,
        'Source82_88_stages': steps, 'independent_cumulative_review': application['independent_cumulative_review'],
        'live_pages_equal_exact_reviewed_candidates': application['source_pages'],
        'final_inventory': application['final_inventory'], 'fresh_live_full29_parser': parser_native,
        'final_inventory_every_record_matches_fresh_parse': True,
        'all_old81_registry_records_unchanged': True, 'exercise_literal_changes': [],
        'physical_changed_material_keys': changed_union,
        'old_owners_preserved': old_owners, 'old1254_selected_proof_bytes_preserved': ref(SELECTION),
        'unaffected29_site_assets_preserved': unaffected_assets,
        'original_failed_application_v1_preserved': {
            'execution': ref(ROOT / 'reports/full-coverage/apply-source33-execution-v1.json'),
            'raw_log': ref(ROOT / 'reports/full-coverage/apply-source33-execution-v1.log'),
            'helper': ref(ROOT / 'book/coverage/checks/checkpoint33-root/apply_sources33.py')},
        'new_owner_installation_or_aggregate_audit_claimed': False,
        'current_inputs_mutated_by_review': False, 'coverage_complete': False}
    result_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(ref(result_path)))


if __name__ == '__main__':
    main()

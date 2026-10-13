#!/usr/bin/env python3
"""Read-only independent audit of actual Source89/90 application and all90 inverse hashes."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
APPLICATION = ROOT / 'reports/full-coverage/checkpoint34-source-corrections89-90-v1.json'
HISTORY = ROOT / 'reports/full-coverage/source-history/checkpoint34-before-corrections89-90-v1'
REGISTRY = ROOT / 'book/coverage/material-corrections.json'
SELECTION = ROOT / 'reports/full-coverage/checkpoint-33-selection.json'
HELPER = ROOT / 'book/coverage/checks/checkpoint34-root/apply_sources34_v2.py'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def ref(path):
    return {'file': str(path.relative_to(ROOT)), 'sha256': sha(path), 'bytes': path.stat().st_size}


def exact(row):
    path = Path(row['file'])
    if not path.is_absolute():
        path = ROOT / path
    assert sha(path) == row['sha256'], row['file']
    if 'bytes' in row:
        assert path.stat().st_size == row['bytes']
    return path


def read(row):
    return json.loads(exact(row).read_bytes())


def write_new(path, value):
    assert not path.exists() and path.is_relative_to(OUT)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def literal(row):
    return {key: value for key, value in row.items() if key != 'source_sha256'}


def main():
    output = OUT / 'independent-actual-source89-90-application-review-v1.json'
    assert not output.exists()
    assert sha(APPLICATION) == 'bf895fec06fe205407ad9f24248fb365992e4fcbbe80d9a799e49d47f2a66dd4'
    application = json.loads(APPLICATION.read_bytes())
    candidate = read(application['independent_cumulative_review'])
    assert candidate['errors'] == [] and application['old_owners_and_selected33_proofs_preserved']
    registry = json.loads(REGISTRY.read_bytes())
    original_registry_path = HISTORY / 'book/coverage/material-corrections.json'
    original_registry = json.loads(original_registry_path.read_bytes())
    assert len(original_registry['corrections']) == 88 and len(registry['corrections']) == 90
    assert registry['corrections'][:88] == original_registry['corrections']
    assert registry['corrections'][88:] == application['applications']
    assert [row['correction_id'] for row in application['applications']] == [89, 90]
    helper_text = HELPER.read_text()
    for marker in ["corrections['corrections'][:88] == original_corrections", 'assert inverse.encode() == before',
                   'assert all(sha(ROOT / n) == h for n, h in held.items())', 'tempfile.TemporaryDirectory',
                   "old_owners_and_selected33_proofs_preserved=True", "['/usr/bin/python', '-B', '-E'"]:
        assert marker in helper_text
    execution_path = ROOT / 'reports/full-coverage/apply-source34-execution-v2.json'
    execution = json.loads(execution_path.read_bytes())
    assert execution['actual_exit_code'] == 0
    execution_refs = []
    for key, value in execution.items():
        if isinstance(value, dict) and 'file' in value and 'sha256' in value:
            exact(value)
            execution_refs.append({'role': key, 'reference': value})
    initial_inventory_path = HISTORY / 'book/coverage/inventory.json'
    assert sha(initial_inventory_path) == '87b8457614b7a9a127c171e1a95adf43bd94d05de6d63921b5e69493e3822202'
    initial = json.loads(initial_inventory_path.read_bytes())
    prior = initial
    stages = []
    for position, correction in enumerate(application['applications']):
        before_page = exact(correction['historical_source']).read_bytes()
        expected_offer = candidate['two_offer_six_exact_replacements'][position]
        assert correction['source'] == expected_offer['source']
        assert correction['replacements'] == [{key: value for key, value in row.items() if key in ('before', 'after')}
                                               for row in expected_offer['exact_replacements']]
        assert digest(before_page) == correction['before_sha256']
        page = before_page
        for row in correction['replacements']:
            old, new = row['before'].encode(), row['after'].encode()
            assert page.count(old) == 1 and page.count(new) == 0
            page = page.replace(old, new, 1)
        assert digest(page) == correction['after_sha256']
        inverse = page
        for row in reversed(correction['replacements']):
            assert inverse.count(row['after'].encode()) == 1
            inverse = inverse.replace(row['after'].encode(), row['before'].encode(), 1)
        assert inverse == before_page
        before, after = read(correction['inventory_before']), read(correction['inventory_after'])
        assert before == prior and before['counts'] == after['counts']
        assert after['source_sha256'] == {**before['source_sha256'], correction['source']: correction['after_sha256']}
        changed = {}
        for collection in ('exercises', 'material_source_units'):
            old_rows, new_rows = [{row['key']: row for row in inventory[collection]} for inventory in (before, after)]
            assert old_rows.keys() == new_rows.keys()
            changed[collection] = sorted(key for key in old_rows if literal(old_rows[key]) != literal(new_rows[key]))
            for key, old in old_rows.items():
                new = new_rows[key]
                assert new['source_sha256'] == after['source_sha256'][new['source']]
                assert {k: v for k, v in old.items() if k not in ('source_sha256', 'source_text', 'text_sha256')} == {k: v for k, v in new.items() if k not in ('source_sha256', 'source_text', 'text_sha256')}
        assert changed == ({'exercises': ['nn-in-the-loop.html::exercise-17'], 'material_source_units': [
                            'nn-in-the-loop.html::node-1210', 'nn-in-the-loop.html::node-1217', 'nn-in-the-loop.html::node-1218', 'nn-in-the-loop.html::node-1220']}
                           if position == 0 else {'exercises': [], 'material_source_units': ['primer-probability.html::node-387']})
        native = read(correction['actual_fresh_parser'])
        assert native['status'] == 'passed' and native['actual_exit_code'] == 0 and native['parser_ROOT_and_OUT_isolated']
        assert native['candidate_page_sha256'] == correction['after_sha256']
        assert native['actual_command'][:3] == ['/usr/bin/python', '-B', '-E']
        assert Path(native['actual_workdir']).is_relative_to('/tmp')
        assert Path(native['actual_command'][-1]).parent.parent == Path(native['actual_workdir'])
        assert exact(native['raw_log']).read_text().strip() == 'Inventoried 556 exercises and 12774 mathematical source units on 29 pages.'
        exact(native['parser'])
        for field in ('source_proposal', 'independent_semantic_review', 'cumulative_independent_review'):
            exact(correction[field])
        stages.append({'correction_id': correction['correction_id'], 'source': correction['source'],
                       'before_sha256': correction['before_sha256'], 'after_sha256': correction['after_sha256'],
                       'exact_reviewed_replacement_count': len(correction['replacements']), 'changed_literal_keys': changed,
                       'historical_page': correction['historical_source'], 'inventory_before': correction['inventory_before'],
                       'inventory_after': correction['inventory_after'], 'actual_fresh_parser': correction['actual_fresh_parser'],
                       'exact_whole_page_inverse_passed': True})
        prior = after
    final = read(application['final_inventory'])
    assert final == prior
    assert application['final_inventory']['sha256'] == 'fa3edbc297c59878db2226a04dc91e66493f5bf9adb67535c05b60429e1ac254'
    assert (ROOT / 'book/coverage/inventory-after-correction90.json').read_bytes() == (ROOT / 'book/coverage/inventory.json').read_bytes()
    proposed = read(candidate['fresh_candidate_inventory'])
    for key in ('schema_version', 'status', 'source_sha256', 'counts', 'exercises', 'material_source_units', 'limits'):
        assert final[key] == proposed[key]
    for page in candidate['pages']:
        assert (ROOT / page['source']).read_bytes() == exact(page['candidate']).read_bytes()
    current_pages = {name: (ROOT / name).read_bytes() for name in final['source_sha256']}
    inverse_chain = []
    for number in range(90, 0, -1):
        correction = registry['corrections'][number - 1]
        source = correction['source']
        page = current_pages[source]
        assert digest(page) == correction['after_sha256'], (number, source)
        substitutions = correction.get('replacements', [{'before': correction.get('before'), 'after': correction.get('after')}])
        for row in reversed(substitutions):
            assert page.count(row['after'].encode()) == 1, (number, source)
            page = page.replace(row['after'].encode(), row['before'].encode(), 1)
        assert digest(page) == correction['before_sha256'], (number, source)
        current_pages[source] = page
        inverse_chain.append({'correction_id': number, 'source': source, 'restored_before_sha256': correction['before_sha256'],
                              'actual_prior_after_sha256': correction['after_sha256']})
        if number == 89:
            assert {name: digest(data) for name, data in current_pages.items()} == initial['source_sha256']
    old_baseline = read(candidate['protected_baseline'])['protected_sha256']
    old_owners = {}
    for owner in ('foundations', 'applied', 'modules', 'core'):
        path = ROOT / f'book/coverage/{owner}.json'
        assert sha(path) == old_baseline[str(path.relative_to(ROOT))]
        old_owners[owner] = ref(path)
    selection = json.loads(SELECTION.read_bytes())
    for name, row in selection['proof_files'].items():
        assert sha(ROOT / name) == row['sha256']
    unaffected_assets = {name: fingerprint for name, fingerprint in old_baseline.items()
                         if name.startswith('SafeLearning/') and name not in application['source_pages']}
    assert len(unaffected_assets) == 29
    assert all(sha(ROOT / name) == fingerprint for name, fingerprint in unaffected_assets.items())
    protected = {name: row['sha256'] for name, row in selection['proof_files'].items()}
    protected.update({name: sha(ROOT / name) for name in [*final['source_sha256'], 'SafeLearning/style.css', 'SafeLearning/components.js',
                      'book/coverage/inventory.json', 'book/coverage/material-corrections.json', 'book/inventory_claims.py', 'book/validate.py']})
    protected.update({r['file']: r['sha256'] for r in old_owners.values()})
    parser_log = OUT / 'actual-source90-independent-postapplication-full29-parser-v1.log'
    parsed_path = OUT / 'actual-source90-independent-postapplication-full29-inventory-v1.json'
    assert not parser_log.exists() and not parsed_path.exists()
    with tempfile.TemporaryDirectory(prefix='independent-Source90-current-full29-') as directory:
        tree = Path(directory)
        for name in final['source_sha256']:
            path = tree / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((ROOT / name).read_bytes())
        for name in ('book/inventory_claims.py', 'book/validate.py'):
            path = tree / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((ROOT / name).read_bytes())
        command = ['/usr/bin/python', '-E', '-B', str(tree / 'book/inventory_claims.py')]
        started, tick = datetime.now(timezone.utc).isoformat(), time.monotonic()
        with parser_log.open('xb') as stream:
            actual = subprocess.run(command, cwd=tree, stdout=stream, stderr=subprocess.STDOUT)
        finished, elapsed = datetime.now(timezone.utc).isoformat(), time.monotonic() - tick
        assert actual.returncode == 0
        parsed_data = (tree / 'book/coverage/inventory.json').read_bytes()
        parsed_path.write_bytes(parsed_data)
        actual_workdir = str(tree)
    parsed = json.loads(parsed_data)
    for key in ('schema_version', 'status', 'source_sha256', 'counts', 'exercises', 'material_source_units', 'limits'):
        assert parsed[key] == final[key]
    changes = [name for name, fingerprint in protected.items() if sha(ROOT / name) != fingerprint]
    assert changes == []
    parser_native_path = OUT / 'actual-source90-independent-postapplication-full29-parser-native-v1.json'
    write_new(parser_native_path, {'status': 'passed', 'actual_command': command, 'actual_workdir': actual_workdir,
        'actual_exit_code': actual.returncode, 'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': elapsed,
        'raw_log': ref(parser_log), 'fresh_parsed_inventory': ref(parsed_path), 'parser': ref(ROOT / 'book/inventory_claims.py'),
        'validate_provider': ref(ROOT / 'book/validate.py'), 'input_site_sha256': final['source_sha256'],
        'both_ROOT_and_OUT_isolated_ephemeral_input_tree_removed_after_exact_output_retained': True,
        'protected_file_changes': changes, 'coverage_complete': False})
    failed_path = ROOT / 'reports/full-coverage/apply-source34-execution-v1.json'
    failed = json.loads(failed_path.read_bytes())
    assert failed['actual_exit_code'] != 0
    failure_refs = {'native': ref(failed_path), 'raw_log': ref(ROOT / 'reports/full-coverage/apply-source34-execution-v1.log'),
                    'helper': ref(ROOT / 'book/coverage/checks/checkpoint34-root/apply_sources34.py')}
    write_new(output, {'status': 'passed_independent_actual_Source89_90_application_full90_inverse_chain_and_old_owner33_proof_protection',
        'errors': [], 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(), 'application': ref(APPLICATION),
        'actual_application_helper_full_code_read': ref(HELPER), 'actual_application_execution': ref(execution_path),
        'actual_execution_exact_reference_leaves_checked': execution_refs, 'preserved_preapplication_registry': ref(original_registry_path),
        'current_registry': ref(REGISTRY), 'all_old88_registry_objects_exact': True, 'all90_full_page_inverse_hash_steps': inverse_chain,
        'actual_Source89_90_stages': stages, 'live_Source90_pages_equal_exact_independently_reviewed_candidates': application['source_pages'],
        'final_inventory': application['final_inventory'], 'final_inventory_every_record_matches_independent_candidate_and_fresh_live_parse': True,
        'independent_fresh_postapplication_all29_parser': ref(parser_native_path), 'old_four_owner33_bytes_preserved': old_owners,
        'all1261_old_selected33_proof_bytes_preserved': ref(SELECTION), 'unaffected29_site_assets_preserved': unaffected_assets,
        'protected_file_changes': changes, 'genuine_failed_preflight_v1_preserved': failure_refs,
        'new_owner_installation_aggregate_kernel_axiom_browser_or_publication_success_claimed': False,
        'review_source_owner_registry_aggregate_or_proof_mutations': False, 'coverage_complete': False})
    print(json.dumps({'application_review': ref(output), 'Source90_inventory': application['final_inventory'],
                      'fresh_all29_parser': ref(parser_native_path)}), flush=True)


if __name__ == '__main__':
    main()

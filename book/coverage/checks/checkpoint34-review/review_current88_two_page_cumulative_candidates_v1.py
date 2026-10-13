#!/usr/bin/env python3
"""Independently reconstruct only reviewed NN/Conditional wording in a fresh source tree."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
TREE = OUT / 'isolated-current88-cumulative-candidate-v1'
INDEX = ROOT / 'book/coverage/checks/checkpoint33-review/next-unselected-work-index-v1.json'
SELECTION = ROOT / 'reports/full-coverage/checkpoint-33-selection.json'
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'book'))
from validate import Document


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
        assert path.stat().st_size == row['bytes'], row['file']
    return path


def new_json(path, value):
    assert path.is_relative_to(OUT) and not path.exists(), path
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def without_source_fingerprint(row):
    return {key: value for key, value in row.items() if key != 'source_sha256'}


def main():
    assert not TREE.exists()
    assert not (OUT / 'independent-current88-two-page-cumulative-candidate-review-v1.json').exists()
    index = json.loads(INDEX.read_bytes())
    nn, conditional = index['next_tasks'][1:3]
    assert nn['id'] == 'apply_exact_NN14_3_precision_and_select_NN65'
    assert conditional['id'] == 'apply_Conditional28_node387_exact_domain_qualifiers'
    nn_peer_path, nn_narrow_path = exact(nn['packet']), exact(nn['narrow_peer'])
    conditional_peer_path, conditional_narrow_path = exact(conditional['packet']), exact(conditional['narrow_peer'])
    nn_peer = json.loads(nn_peer_path.read_bytes())
    conditional_peer = json.loads(conditional_peer_path.read_bytes())
    narrow_peers = [json.loads(path.read_bytes()) for path in (nn_narrow_path, conditional_narrow_path)]
    assert all(peer['errors'] == [] for peer in [nn_peer, conditional_peer, *narrow_peers])
    assert nn_peer['whole_exercise_decision']['prospective_whole_semantic_approved']
    assert not nn_peer['whole_exercise_decision']['current_whole_semantic_approved']
    assert conditional_peer['prospective_whole_decision']['approved']
    assert not conditional_peer['current_whole_decision']['approved']
    assert len(conditional_peer['all28_complete_public_body_assessments']) == 28
    assert all(row['entire_body_and_actual_all_input_predicates_read'] and row['independently_approved_exact_component']
               for row in conditional_peer['all28_complete_public_body_assessments'])
    readiness_paths = [ROOT / 'book/coverage/checks/checkpoint34-iqc-preparation/iqc21-future34-paired-readiness-v1.json',
                       ROOT / 'book/coverage/checks/checkpoint34-nn-preparation/nn65-future34-paired-readiness-v1.json',
                       ROOT / 'book/coverage/checks/checkpoint34-conditional-preparation/actual-conditional28-canonical34-paired-readiness-v1.json']
    readiness_records = []
    readiness_inputs = []
    for path in readiness_paths:
        readiness = json.loads(path.read_bytes())
        assert readiness['errors'] == [] and len(readiness['actual_paired_records']) == 2
        source_record = readiness.get('canonical_source_ref', readiness['canonical_source'])
        source = exact(source_record)
        assert source.read_bytes() == exact(readiness['original_source']).read_bytes()
        inputs = [path, source, exact(readiness['original_source'])]
        if 'context' in readiness:
            context_path = exact(readiness['context'])
            context = json.loads(context_path.read_bytes())
            assert readiness['site_inventory_four_owners_selected33_proofs_and_main_aggregates_preserved']
            for name, fingerprint in context['protected_current_inputs_sha256'].items():
                assert sha(ROOT / name) == fingerprint, name
            inputs.append(context_path)
        pairs = []
        for pair in readiness['actual_paired_records']:
            native_path = exact(pair['actual_record'])
            native = json.loads(native_path.read_bytes())
            assert native['status'] == 'passed' and native['actual_exit_code'] == 0
            if 'protection_errors' in native:
                assert native['protection_errors'] == []
            else:
                assert 'context' in readiness and native['context'] == readiness['context']
            snapshot, log = exact(pair['source_snapshot']), exact(pair['raw_log'])
            assert snapshot.read_bytes() == source.read_bytes()
            inputs.extend([native_path, snapshot, log])
            pairs.append({'actual_record': ref(native_path), 'actual_command': native['actual_command'],
                          'actual_workdir': native['actual_workdir'], 'actual_exit_code': native['actual_exit_code'],
                          'started_at_utc': native['started_at_utc'], 'finished_at_utc': native['finished_at_utc'],
                          'elapsed_seconds': native['elapsed_seconds'], 'raw_log': ref(log), 'source_snapshot': ref(snapshot)})
        readiness_inputs.extend(inputs)
        readiness_records.append({'readiness': ref(path), 'canonical_source': ref(source), 'original_source': readiness['original_source'],
                                  'public_theorem_count': readiness['public_theorem_count'], 'actual_paired_records': pairs})
    selection = json.loads(SELECTION.read_bytes())
    selected_paths = []
    for name, row in selection['proof_files'].items():
        path = ROOT / name
        assert sha(path) == row['sha256']
        selected_paths.append(path)
    assets = [path for path in (ROOT / 'SafeLearning').iterdir() if path.is_file() and path.suffix in {'.html', '.css', '.js'}]
    assert len(assets) == 31
    html = sorted(path for path in assets if path.suffix == '.html')
    assert len(html) == 29
    inventory_path = ROOT / 'book/coverage/inventory.json'
    current = json.loads(inventory_path.read_bytes())
    assert sha(inventory_path) == '87b8457614b7a9a127c171e1a95adf43bd94d05de6d63921b5e69493e3822202'
    protected_paths = [*selected_paths, *assets, inventory_path, *(ROOT / f'book/coverage/{owner}.json' for owner in ('foundations', 'applied', 'modules', 'core')),
                       ROOT / 'verification/lean/SafeLearning.lean', ROOT / 'verification/lean/AxiomAudit.lean',
                       ROOT / 'book/inventory_claims.py', ROOT / 'book/validate.py', INDEX, SELECTION, Path(__file__),
                       nn_peer_path, nn_narrow_path, conditional_peer_path, conditional_narrow_path,
                       exact(nn['proposal']), exact(conditional['proposal']), *readiness_inputs]
    protected = {str(path.relative_to(ROOT)): sha(path) for path in protected_paths}

    def guard():
        return [name for name, fingerprint in protected.items() if sha(ROOT / name) != fingerprint]

    assert guard() == []
    guard_path = OUT / 'current88-selected33-owner33-site31-protected-baseline-v1.json'
    new_json(guard_path, {'protected_sha256': protected, 'selected33_proof_source_count': len(selected_paths),
                         'site_asset_count': 31, 'current_inventory': ref(inventory_path),
                         'progress_and_publicationrepo_not_written_and_concurrent_delivery_excluded_from_guard': True})
    (TREE / 'SafeLearning').mkdir(parents=True)
    (TREE / 'book').mkdir()
    original_dir = OUT / 'original-current88-two-pages'
    original_dir.mkdir()
    for path in html:
        (TREE / 'SafeLearning' / path.name).write_bytes(path.read_bytes())
    for name in ('inventory_claims.py', 'validate.py'):
        (TREE / 'book' / name).write_bytes((ROOT / 'book' / name).read_bytes())
    page_records = []
    whole_replacements = []
    raw_dom_impacts = {}
    for task, name, expected_candidate in [(nn, 'nn-in-the-loop.html', '22b785e46001e4e5d73166d05503f9beb5454634cfa6b929df24f6bbe33e7e4b'),
                                           (conditional, 'primer-probability.html', '19891bd487ec19b67cbda477809a3a273242c6d4b0647e93c01b94f75108519f')]:
        live = ROOT / 'SafeLearning' / name
        original = live.read_bytes()
        assert digest(original) == task['source_qualification']['current_page_sha256']
        original_path = original_dir / name
        original_path.write_bytes(original)
        before = original.decode()
        after = before
        rows = task['source_qualification'].get('exact_four_entire_line_changes', task['source_qualification'].get('exact_replacements'))
        normalized = []
        for number, row in enumerate(rows):
            old, new = row.get('exact_before_utf8', row.get('before')), row.get('exact_after_utf8', row.get('after'))
            assert after.count(old) == 1
            if 'line_1_based' in row:
                assert after.splitlines(keepends=True)[row['line_1_based'] - 1] == old
            after = after.replace(old, new, 1)
            normalized.append({'before': old, 'after': new, **({'line_1_based': row['line_1_based']} if 'line_1_based' in row else {})})
        candidate_path = TREE / 'SafeLearning' / name
        candidate_path.write_bytes(after.encode())
        assert sha(candidate_path) == expected_candidate
        inverse = after
        for row in reversed(normalized):
            assert inverse.count(row['after']) == 1
            inverse = inverse.replace(row['after'], row['before'], 1)
        assert inverse.encode() == original
        original_masked, candidate_masked = before, after
        for number, row in enumerate(normalized):
            marker = f'EXACT_REVIEWED_WORDING_SPAN_{number}'
            original_masked = original_masked.replace(row['before'], marker, 1)
            candidate_masked = candidate_masked.replace(row['after'], marker, 1)
        assert original_masked == candidate_masked
        a, b = Document(before), Document(after)
        assert len(a.nodes) == len(b.nodes)
        assert [(n.tag, n.attrs, n.line) for n in a.nodes] == [(n.tag, n.attrs, n.line) for n in b.nodes]
        assert [n.text() for n in a.nodes if n.tag == 'script'] == [n.text() for n in b.nodes if n.tag == 'script']
        assert re.findall(r'<[^>]+>', before) == re.findall(r'<[^>]+>', after)
        assert before.count('\n') == after.count('\n')
        raw_dom_impacts[name] = [{'node_ordinal_1_based': i, 'tag': old.tag, 'line': old.line, 'attrs': old.attrs,
                                  'old_text_sha256': digest(old.text().encode()), 'candidate_text_sha256': digest(new.text().encode())}
                                 for i, (old, new) in enumerate(zip(a.nodes, b.nodes), 1) if old.text() != new.text()]
        page_records.append({'source': str(live.relative_to(ROOT)), 'original': ref(original_path), 'candidate': ref(candidate_path),
                             'exact_replacements': normalized, 'whole_page_forward_and_inverse_exact': True,
                             'all_raw_tags_DOM_attributes_lines_and_inline_scripts_exact': True, 'outside_reviewed_wording_exact': True})
        whole_replacements.append({'task': task['id'], 'original_proposal': task['proposal'], 'source': str(live.relative_to(ROOT)), 'exact_replacements': normalized})
    for path in html:
        if path.name not in {'nn-in-the-loop.html', 'primer-probability.html'}:
            assert (TREE / 'SafeLearning' / path.name).read_bytes() == path.read_bytes()
    assert guard() == []
    started = datetime.now(timezone.utc).isoformat()
    tick = time.monotonic()
    command = ['/usr/bin/python', '-E', '-B', str(TREE / 'book/inventory_claims.py')]
    parser_log = OUT / 'fresh-isolated-current88-cumulative-full29-parser-v1.log'
    with parser_log.open('xb') as stream:
        actual = subprocess.run(command, cwd=TREE, stdout=stream, stderr=subprocess.STDOUT)
    finished = datetime.now(timezone.utc).isoformat()
    elapsed = time.monotonic() - tick
    errors = guard()
    native_path = OUT / 'fresh-isolated-current88-cumulative-full29-parser-actual-v1.json'
    new_json(native_path, {'status': 'passed' if actual.returncode == 0 and not errors else 'failed',
                          'actual_command': command, 'actual_workdir': str(TREE), 'actual_exit_code': actual.returncode,
                          'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': elapsed,
                          'parser': ref(TREE / 'book/inventory_claims.py'), 'validate_provider': ref(TREE / 'book/validate.py'),
                          'raw_log': ref(parser_log), 'recorder': ref(Path(__file__)), 'protected_baseline': ref(guard_path),
                          'protection_errors': errors, 'both_ROOT_and_OUT_isolated_from_live_site_and_owners': True,
                          'coverage_complete': False})
    assert actual.returncode == 0 and errors == []
    candidate_inventory_path = TREE / 'book/coverage/inventory.json'
    proposed = json.loads(candidate_inventory_path.read_bytes())
    assert proposed['counts'] == current['counts'] and len(proposed['source_sha256']) == 29
    assert proposed['schema_version'] == current['schema_version'] and proposed['status'] == current['status'] and proposed['limits'] == current['limits']
    changed = {}
    changed_whole_rows = {}
    page_fingerprint_rebases = {}
    for collection in ('material_source_units', 'exercises'):
        old_rows = {row['key']: row for row in current[collection]}
        new_rows = {row['key']: row for row in proposed[collection]}
        assert old_rows.keys() == new_rows.keys()
        changed[collection] = []
        changed_whole_rows[collection] = {}
        page_fingerprint_rebases[collection] = []
        for key, old in old_rows.items():
            new = new_rows[key]
            if old['source_text'] != new['source_text']:
                assert old['text_sha256'] != new['text_sha256']
                assert {k: v for k, v in old.items() if k not in {'source_text', 'text_sha256', 'source_sha256'}} == {k: v for k, v in new.items() if k not in {'source_text', 'text_sha256', 'source_sha256'}}
                changed[collection].append(key)
                changed_whole_rows[collection][key] = {'entire_current': old, 'entire_candidate': new}
            else:
                assert without_source_fingerprint(old) == without_source_fingerprint(new)
                if old != new:
                    page_fingerprint_rebases[collection].append(key)
    assert changed == {'material_source_units': ['nn-in-the-loop.html::node-1210', 'nn-in-the-loop.html::node-1217',
                                                'nn-in-the-loop.html::node-1218', 'nn-in-the-loop.html::node-1220', 'primer-probability.html::node-387'],
                       'exercises': ['nn-in-the-loop.html::exercise-17']}
    for key, rows in nn_peer['entire_current_and_prospective_changed_inventory_literals'].items():
        collection = 'exercises' if '::exercise-' in key else 'material_source_units'
        assert changed_whole_rows[collection][key] == {'entire_current': rows['entire_current'], 'entire_candidate': rows['entire_proposed']}
    assert changed_whole_rows['material_source_units']['primer-probability.html::node-387'] == {
        'entire_current': conditional_peer['current_whole_decision']['entire_current_literal'],
        'entire_candidate': conditional_peer['prospective_whole_decision']['entire_prospective_literal']}
    iqc_summary_path = ROOT / 'book/coverage/checks/checkpoint34-iqc-preparation/IQC21-current-Exercise14_6-four-literal-correspondence-summary-v1.json'
    iqc = json.loads(iqc_summary_path.read_bytes())
    iqc_unchanged = {}
    for key in [iqc['entire_current_exercise']['key'], *iqc['whole_four_literal_peer_decisions']]:
        collection = 'exercises' if '::exercise-' in key else 'material_source_units'
        old = next(row for row in current[collection] if row['key'] == key)
        new = next(row for row in proposed[collection] if row['key'] == key)
        assert without_source_fingerprint(old) == without_source_fingerprint(new)
        iqc_unchanged[key] = {'unchanged_literal_text_sha256': old['text_sha256'], 'old_page_sha256': old['source_sha256'],
                              'candidate_page_sha256': new['source_sha256'], 'whole_literal_decision_retained': True}
    assert guard() == []
    report_path = OUT / 'independent-current88-two-page-cumulative-candidate-review-v1.json'
    new_json(report_path, {'status': 'passed_independent_current88_exact_NN14_3_and_Conditional387_cumulative_candidate_source_qualification_review_only',
        'errors': [], 'completed_at_utc': datetime.now(timezone.utc).isoformat(), 'source_corrections_reserved_or_applied': False,
        'live_site_owner_inventory_or_selected_proof_edits': False, 'old_runtime_snapshot_or_cache_trees_copied': False,
        'current_inventory_input': ref(inventory_path), 'current_Source88_site_sha256': current['source_sha256'],
        'candidate_Source88_plus_two_reviewed_offers_site_sha256': proposed['source_sha256'],
        'pages': page_records, 'two_offer_six_exact_replacements': whole_replacements,
        'fresh_all29_parser': ref(native_path), 'fresh_candidate_inventory': ref(candidate_inventory_path),
        'changed_physical_literal_keys': changed, 'changed_whole_inventory_rows': changed_whole_rows,
        'additional_changed_ancestor_inventory_literals': [], 'raw_DOM_changed_text_ancestor_nodes_without_automatic_proof_promotion': raw_dom_impacts,
        'all_other27_pages_and_all_other_literal_records_exact_except_required_current_page_fingerprints': True,
        'unchanged_literal_page_fingerprint_rebase_keys': page_fingerprint_rebases,
        'unchanged_IQC14_6_current_whole_literal_approvals_retained': iqc_unchanged,
        'full_independent_mathematical_peers': [ref(nn_peer_path), ref(conditional_peer_path)],
        'distinct_narrow_qualification_peers': [ref(nn_narrow_path), ref(conditional_narrow_path)],
        'all_three_fresh_source_readiness_packets_and_actual_native_records_checked': readiness_records,
        'NN14_3_whole_exercise_and_four_material_decisions_conditional_on_exact_application': {
            'exercise': nn_peer['whole_exercise_decision'], 'materials': nn_peer['whole_four_changed_material_unit_decisions'],
            'precise_clauses': nn_peer['clause_to_genuine_public_theorem_correspondence'], 'actual_domains': nn_peer['actual_scope_domains'],
            'finite_simulation_scope': nn_peer['simulation_scope']},
        'Conditional387_whole_decision_conditional_on_exact_application': conditional_peer['prospective_whole_decision'],
        'Conditional387_complete_definition_domain_assessment': conditional_peer['independent_mathematical_assessment'],
        'current_NN14_3_and_Conditional387_whole_approved_before_source_application': False,
        'NN14_4_default2D_explorer_neighbor390_environment_wide_performance_lemma_or_other_literal_promoted': False,
        'protected_baseline': ref(guard_path), 'protection_errors': guard(),
        'aggregate_owner_selection_fresh_kernel_axiom_or_publication_work_performed': False, 'coverage_complete': False})
    print(json.dumps({'candidate_review': ref(report_path), 'fresh_candidate_inventory': ref(candidate_inventory_path),
                      'changed_physical_literal_keys': changed, 'pages': [r['candidate'] for r in page_records]}), flush=True)


if __name__ == '__main__':
    main()

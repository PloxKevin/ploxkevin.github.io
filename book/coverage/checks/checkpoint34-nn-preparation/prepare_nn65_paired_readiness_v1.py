#!/usr/bin/env python3
"""Prepare exact, unselected NN65 bytes and record two genuine compiler commands."""
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
LEAN = ROOT / 'verification/lean'
CANONICAL = LEAN / 'SafeLearning/CompleteModulesNNScalarOriginLinearization34.lean'
INDEX = ROOT / 'book/coverage/checks/checkpoint33-review/next-unselected-work-index-v1.json'
SELECTION = ROOT / 'reports/full-coverage/checkpoint-33-selection.json'
IQC = LEAN / 'SafeLearning/CompleteModulesShiftedTemporalIQC34.lean'
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'book/coverage'))
from lean_names import declarations


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ref(path):
    return {'file': str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path),
            'sha256': sha(path), 'bytes': path.stat().st_size}


def exact(record):
    path = Path(record['file'])
    if not path.is_absolute():
        path = ROOT / path
    assert sha(path) == record['sha256'], record['file']
    if 'bytes' in record:
        assert path.stat().st_size == record['bytes'], record['file']
    return path


def new_json(path, value):
    assert path.is_relative_to(OUT) and not path.exists(), path
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def typed_refs(value):
    if isinstance(value, dict):
        if isinstance(value.get('file'), str) and isinstance(value.get('sha256'), str):
            yield value
        for child in value.values():
            yield from typed_refs(child)
    elif isinstance(value, list):
        for child in value:
            yield from typed_refs(child)


def delivery_observation():
    progress = ROOT / 'book/coverage/progress.json'
    result = subprocess.run(['git', '-C', str(ROOT / 'reports/book/publication-repo'), 'rev-parse', 'HEAD'],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    return {'observed_at_utc': datetime.now(timezone.utc).isoformat(),
            'progress': ref(progress) if progress.exists() else None,
            'publication_HEAD': result.stdout.strip() if result.returncode == 0 else None,
            'git_read_exit_code': result.returncode,
            'scope': 'Read-only; concurrent authorized Root checkpoint33 delivery is outside the stability guard.'}


def main():
    assert not CANONICAL.exists()
    assert not (OUT / 'nn65-future34-paired-readiness-v1.json').exists()
    index = json.loads(INDEX.read_bytes())
    task = index['next_tasks'][1]
    assert task['id'] == 'apply_exact_NN14_3_precision_and_select_NN65'
    source = exact(task['source'])
    peer_path = exact(task['packet'])
    narrow_path = exact(task['narrow_peer'])
    proposal_path = exact(task['proposal'])
    candidate_path = exact(task['individual_candidate'])
    simulation_path = exact(task['finite_simulation_receipt'])
    assert sha(source) == '57dd88f43d890086c2edcd187afc07a85d8e4b89a3fd3a3bc372dfc48f01381c'
    assert sha(peer_path) == '186b264fdede7f8b5e392a02130164094c85e08d16f77809bcf425de7d0cac03'
    peer = json.loads(peer_path.read_bytes())
    narrow = json.loads(narrow_path.read_bytes())
    proposal = json.loads(proposal_path.read_bytes())
    assert peer['errors'] == [] and narrow['errors'] == []
    decision = peer['whole_exercise_decision']
    assert not decision['current_whole_semantic_approved']
    assert decision['prospective_whole_semantic_approved'] and decision['prospective_missing_requirements'] == []
    assert decision['conditional_on_later_exact59d_four_line_application_and_current_literal_identity']
    assert all(peer['all_three_requested_part_requirements_satisfied_for_the_exact_prospective_exercise'].values())
    source_bytes = source.read_bytes()
    source_text = source_bytes.decode()
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b|#eval', source_text)
    public = declarations(source_text)
    names = {d['name'] for d in public}
    theorems = [d['name'] for d in public if d['kind'] == 'theorem']
    assert len(public) == len(names) == 95 and len(theorems) == 65
    assert [{'name': d['name'], 'kind': d['kind']} for d in public] == peer['all95_public_names']
    assert re.findall(r'^import\s+(\S+)\s*$', source_text, re.M) == ['Mathlib']
    for route in peer['clause_to_genuine_public_theorem_correspondence'].values():
        assert set(route) <= set(theorems)
    selection = json.loads(SELECTION.read_bytes())
    selected_names = set()
    for name, selected_record in selection['proof_files'].items():
        path = ROOT / name
        assert sha(path) == selected_record['sha256']
        selected_names.update(d['name'] for d in declarations(path.read_text()))
    assert names.isdisjoint(selected_names)
    assert sha(source) not in {r['sha256'] for r in selection['proof_files'].values()}
    assert sha(IQC) == '35a5f818c483645ad8bf66821900417e9dcb709458d5552599d5c480571de249'
    iqc_names = {d['name'] for d in declarations(IQC.read_text())}
    assert len(iqc_names) == 26 and names.isdisjoint(iqc_names)

    # Reconstruct only in memory. The original page and the four exact changed lines stay untouched.
    page = ROOT / 'SafeLearning/nn-in-the-loop.html'
    assert sha(page) == '1765038a05b93faa80ea9668281ec8cb24f0e56ff5c96853b70dc23dabc10a13'
    replacements = proposal['all_four_entire_current_and_proposed_changed_literals']
    assert replacements == task['source_qualification']['exact_four_entire_line_changes']
    assert [r['line_1_based'] for r in replacements] == [982, 988, 989, 990]
    lines = page.read_bytes().decode().splitlines(keepends=True)
    original_lines = lines[:]
    for row in replacements:
        i = row['line_1_based'] - 1
        assert lines[i] == row['exact_before_utf8']
        lines[i] = row['exact_after_utf8']
    candidate = ''.join(lines).encode()
    assert candidate == candidate_path.read_bytes()
    assert hashlib.sha256(candidate).hexdigest() == '22b785e46001e4e5d73166d05503f9beb5454634cfa6b929df24f6bbe33e7e4b'
    for row in reversed(replacements):
        i = row['line_1_based'] - 1
        assert lines[i] == row['exact_after_utf8']
        lines[i] = row['exact_before_utf8']
    assert lines == original_lines and ''.join(lines).encode() == page.read_bytes()
    inventory_path = ROOT / 'book/coverage/inventory.json'
    inventory = json.loads(inventory_path.read_bytes())
    exercise = next(row for row in inventory['exercises'] if row['key'] == decision['key'])
    current_material = {}
    for key, literals in peer['entire_current_and_prospective_changed_inventory_literals'].items():
        collection = inventory['exercises'] if '::exercise-' in key else inventory['material_source_units']
        current = next(row for row in collection if row['key'] == key)
        assert current == literals['entire_current']
        if collection is inventory['material_source_units']:
            current_material[key] = current
    assert len(current_material) == 4
    modules_path = ROOT / 'book/coverage/modules.json'
    modules = json.loads(modules_path.read_bytes())
    owner_exercise = next(row for row in modules['exercises'] if row['inventory_key'] == exercise['key'])
    assert owner_exercise['status'] == 'pending'

    # Retain the original six component authorities and every native metadata field verbatim.
    authority_records = peer['prior_six_original_component_authorities']
    authority_peers = [(exact(row['original_peer']), json.loads(exact(row['original_peer']).read_bytes())) for row in authority_records]
    alias_pool = []
    for document in [peer, narrow, *(v for _, v in authority_peers)]:
        for key in ('exact_original_aliases', 'bounded_original_ref_aliases', 'actual_finalizer_original_byte_aliases'):
            alias_pool.extend(typed_refs(document.get(key, {})))

    def durable(original):
        initial = Path(original['file'])
        if not initial.is_absolute():
            initial = ROOT / initial
        choices = [a for a in alias_pool if a['sha256'] == original['sha256']]
        choices.sort(key=lambda a: (Path(a['file']).is_absolute(), Path(a['file']).name != Path(original['file']).name))
        for candidate in choices:
            candidate_path = Path(candidate['file'])
            if not candidate_path.is_absolute():
                candidate_path = ROOT / candidate_path
            if candidate_path.is_relative_to(ROOT) and candidate_path.exists() and sha(candidate_path) == original['sha256']:
                return ref(exact(candidate))
        if initial.is_relative_to(ROOT) and initial.exists() and sha(initial) == original['sha256']:
            return ref(exact(original))
        raise AssertionError(('Missing durable original byte reference', original))

    histories = []
    historical_leaves = []
    for authority_path, document in authority_peers:
        fields = {k: v for k, v in document.items() if k.startswith('original_') and any(t in k.lower() for t in ('native', 'histori', 'axiom'))}
        leaves = [durable(r) for r in typed_refs(fields)]
        historical_leaves.extend(leaves)
        histories.append({'original_component_peer': ref(authority_path),
                          'original_native_history_and_axiom_metadata_unchanged': fields,
                          'durable_exact_original_leaf_refs': leaves})
    origin_originals = [narrow['additional_origin3_original_genuine_first_failure_preserved']['native'],
                        narrow['additional_origin3_complete_component_bodies_read_and_approved']['actual_source_native'],
                        narrow['additional_origin3_complete_component_bodies_read_and_approved']['actual_all3_standard_axioms_native']]
    origin_histories = []
    for original in origin_originals:
        original_ref = durable(original)
        native = json.loads(exact(original_ref).read_bytes())
        leaves = {'native': original_ref}
        for field, fingerprint in [('source', 'source_sha256_before'), ('source_snapshot', 'source_snapshot_sha256'), ('raw_log', 'raw_log_sha256')]:
            leaves[field] = durable({'file': native[field], 'sha256': native[fingerprint]})
        historical_leaves.extend(leaves.values())
        origin_histories.append({'original_native_metadata_unchanged': native, 'durable_exact_original_leaf_refs': leaves})
    assert [row['original_native_metadata_unchanged']['actual_exit_code'] for row in origin_histories] == [1, 0, 0]
    assert [row['original_native_metadata_unchanged']['elapsed_seconds'] for row in origin_histories] == [19.43804136000108, 44.194565020967275, 29.01780759799294]

    protected = {name: row['sha256'] for name, row in selection['proof_files'].items()}
    site = [p for p in (ROOT / 'SafeLearning').iterdir() if p.is_file() and p.suffix in {'.html', '.css', '.js'}]
    assert len(site) == 31
    for path in [*site, inventory_path, *(ROOT / f'book/coverage/{owner}.json' for owner in ('foundations', 'applied', 'modules', 'core')),
                 LEAN / 'SafeLearning.lean', LEAN / 'AxiomAudit.lean', LEAN / 'lakefile.toml', LEAN / 'lake-manifest.json', LEAN / 'lean-toolchain',
                 source, peer_path, narrow_path, proposal_path, candidate_path, simulation_path, INDEX, SELECTION, IQC, Path(__file__),
                 *(exact(r) for r in historical_leaves), *(p for p, _ in authority_peers)]:
        protected[str(path.relative_to(ROOT))] = sha(path)
    for name, fingerprint in peer['required_evidence_artifacts_sha256'].items():
        assert sha(ROOT / name) == fingerprint
        protected[name] = fingerprint

    def guard():
        return [name for name, fingerprint in protected.items() if sha(ROOT / name) != fingerprint]

    assert guard() == []
    baseline_path = OUT / 'protected-selected33-Source88-owner33-mainaggregate-baseline-v1.json'
    new_json(baseline_path, {'protected_sha256': protected, 'selected33_proof_count': len(selection['proof_files']),
                            'site_asset_count': 31, 'current_aggregate_protected': ['verification/lean/SafeLearning.lean', 'verification/lean/AxiomAudit.lean'],
                            'concurrent_progress_and_publication_delivery_excluded_from_stability_assertions': True})
    delivery_before = delivery_observation()
    CANONICAL.write_bytes(source_bytes)
    snapshots = OUT / 'source-snapshots'
    snapshots.mkdir()
    snapshot = snapshots / CANONICAL.name
    snapshot.write_bytes(source_bytes)
    assert CANONICAL.read_bytes() == source.read_bytes() == snapshot.read_bytes()
    records = []
    for kind, command in [('standalone', ['lake', 'env', 'lean', 'SafeLearning/' + CANONICAL.name]),
                          ('named', ['lake', 'build', 'SafeLearning.' + CANONICAL.stem])]:
        assert guard() == []
        fingerprint = sha(CANONICAL)
        started = datetime.now(timezone.utc).isoformat()
        tick = time.monotonic()
        log = OUT / f'NN65-{kind}-actual-v1.log'
        with log.open('xb') as stream:
            actual = subprocess.run(command, cwd=LEAN, stdout=stream, stderr=subprocess.STDOUT)
        finished = datetime.now(timezone.utc).isoformat()
        elapsed = time.monotonic() - tick
        errors = guard()
        assert sha(CANONICAL) == fingerprint
        record = {'status': 'passed' if actual.returncode == 0 and not errors else 'failed',
                  'kind': kind, 'actual_command': command, 'actual_workdir': str(LEAN),
                  'actual_exit_code': actual.returncode, 'started_at_utc': started, 'finished_at_utc': finished,
                  'elapsed_seconds': elapsed, 'source': ref(CANONICAL), 'source_sha256_before': fingerprint,
                  'source_sha256_after': sha(CANONICAL), 'source_snapshot': ref(snapshot), 'raw_log': ref(log),
                  'compiler_recorder': ref(Path(__file__)), 'protected_baseline': ref(baseline_path), 'protection_errors': errors,
                  'no_eval_native_shortcut_or_substituted_source': True,
                  'aggregate_kernel_owner_selection_or_publication_claimed': False, 'coverage_complete': False}
        record_path = OUT / f'NN65-{kind}-actual-v1.json'
        new_json(record_path, record)
        records.append({'kind': kind, 'actual_record': ref(record_path), 'raw_log': ref(log),
                        'source_snapshot': ref(snapshot), 'actual_exit_code': actual.returncode})
        print(json.dumps({'phase': kind, 'actual_exit_code': actual.returncode, 'elapsed_seconds': elapsed, 'protection_errors': errors}), flush=True)
        assert actual.returncode == 0 and errors == []
    assert guard() == []
    summary_path = OUT / 'NN65-prospective-Exercise14_3-four-literal-correspondence-summary-v1.json'
    new_json(summary_path, {'status': 'prepared_exact_prospective_Exercise14_3_and_four_literals_only_current_source_unqualified_unpromoted',
        'whole_mathematical_peer': ref(peer_path), 'narrow_full29_parser_and_Origin3_peer': ref(narrow_path),
        'source': ref(CANONICAL), 'original_source': ref(source), 'all65_complete_public_proof_bodies_all30_definitions_and_used_private_providers_read': True,
        'exact_current_NN_page': ref(page), 'exact_unapplied_prospective_NN_page': ref(candidate_path),
        'exact_proposal': ref(proposal_path), 'remaining_exact_four_whole_line_replacements': replacements,
        'prospective_page_reconstructed_only_in_memory_and_exact_inverse_passed': True,
        'exact_current_and_prospective_whole_inventory_literals': peer['entire_current_and_prospective_changed_inventory_literals'],
        'whole_exercise_peer_decision': decision, 'whole_four_material_peer_decisions': peer['whole_four_changed_material_unit_decisions'],
        'all_three_requested_prospective_part_decisions': peer['all_three_requested_part_requirements_satisfied_for_the_exact_prospective_exercise'],
        'precise_clause_to_public_theorem_routes': peer['clause_to_genuine_public_theorem_correspondence'],
        'precise_actual_scope_domains': peer['actual_scope_domains'], 'finite_scalar_simulation_receipt': ref(simulation_path),
        'finite_scalar_simulation_scope': peer['simulation_scope'], 'current_owner_exercise': owner_exercise,
        'current_inventory': ref(inventory_path), 'current_modules_owner': ref(modules_path),
        'current_whole_exercise_approved': False, 'source_qualification_required_and_not_applied': True,
        'broader_Exercise14_4_default2D_JS_and_generic_walkthrough_neighbors_approved': False,
        'next_actions': task['remaining_actions'], 'scope_limits': task['scope_limits'], 'coverage_complete': False})
    readiness_path = OUT / 'nn65-future34-paired-readiness-v1.json'
    new_json(readiness_path, {'status': 'passed_actual_exact_NN65_future34_canonical_standalone_named_pairs_unselected_only',
        'errors': [], 'completed_at_utc': datetime.now(timezone.utc).isoformat(), 'source_count': 1,
        'public_theorem_count': 65, 'definition_count': 30, 'public_name_count': 95, 'actual_compiler_command_count': 2,
        'canonical_source': ref(CANONICAL), 'original_source': ref(source),
        'original_namespace_preserved': 'SafeLearning.CompleteModulesNNWalkthroughLocal31',
        'original_historical_uncompiled_comments_preserved_verbatim_not_current_readiness_claims': True,
        'public_declarations': public, 'public_theorem_names': theorems, 'actual_paired_records': records,
        'correspondence_summary': ref(summary_path), 'original_whole_mathematical_peer': ref(peer_path),
        'original_narrow_full29_parser_and_Origin3_peer': ref(narrow_path), 'retained_original_six_component_authorities': authority_records,
        'retained_original_six_component_native_histories': histories, 'retained_original_NN65_failure_pass_and_Origin3_axiom_histories': origin_histories,
        'original_failures_passes_sources_logs_snapshots_body_times_and_peer_verdicts_not_rewritten': True,
        'selected33_public_name_overlap': [], 'IQC34_public_name_overlap': [], 'IQC34_source': ref(IQC),
        'imports': ['Mathlib'], 'redundant_NN26_or_other_prefix_source_added': False,
        'protected_baseline': ref(baseline_path), 'protection_errors': guard(),
        'all1261_selected33_proof_bytes_all31_site_assets_Source88_inventory_fourowner33_and_mainaggregate_preserved': True,
        'concurrent_Root33_delivery_outside_guard': {'before': delivery_before, 'after': delivery_observation(),
            'progress_or_publicationrepo_written_by_this_preparation': False},
        'selected33_selection': ref(SELECTION), 'currently_selected_in33': False, 'in_owner33_proof_metadata': False,
        'current_aggregate_modified': False, 'source_qualification_or_owner_promotion_or_publication_performed': False,
        'fresh_standard_axiom_probe_or_aggregate_kernel_audit_performed': False,
        'requires_next_checkpoint_exact_four_line_qualification_owner_mapping_selection_aggregate_kernel_axiom_ledger_and_delivery': True,
        'not_part_of_checkpoint33_evidence_plan': True, 'coverage_complete': False})
    print(json.dumps({'readiness': ref(readiness_path), 'canonical_source': ref(CANONICAL), 'unselected_future34': True}), flush=True)


if __name__ == '__main__':
    main()

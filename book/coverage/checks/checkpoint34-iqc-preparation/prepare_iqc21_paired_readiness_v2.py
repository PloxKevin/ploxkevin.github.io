#!/usr/bin/env python3
"""Compile one future IQC source without selecting it or changing owner33."""
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
CANONICAL = LEAN / 'SafeLearning/CompleteModulesShiftedTemporalIQC34.lean'
SOURCE = ROOT / 'book/coverage/checks/future32-core/IQC21-full-independent-foundations-v1/exact-original-by-sha256/35a5f818c483645ad8bf66821900417e9dcb709458d5552599d5c480571de249/CompleteModulesShiftedTemporalIQC31-draft-v14.lean'
PEER = ROOT / 'book/coverage/checks/future32-core/IQC21-full-independent-foundations-v1/modules-IQC21-entire-current-Exercise14_6-four-literals-full-mathematical-independent-foundations32-closed-peer-v1.json'
INDEX = ROOT / 'book/coverage/checks/checkpoint33-review/next-unselected-work-index-v1.json'
SELECTION = ROOT / 'reports/full-coverage/checkpoint-33-selection.json'
READY33 = ROOT / 'book/coverage/checks/checkpoint33-proofs/actual-reviewed33-seven-canonical-paired-readiness-v1.json'
AUDIT32 = ROOT / 'reports/full-coverage/lean-checkpoint-32-source81-recovery-v1/verification-original.json'
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
        assert path.stat().st_size == record['bytes']
    return path


def new_json(path, value):
    assert path.is_relative_to(OUT) and not path.exists()
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def original_alias(record, peer):
    if not Path(record['file']).is_absolute():
        exact(record)
        return record
    for alias in peer['bounded_original_ref_aliases'].values():
        candidate = alias['original_byte_copy']
        if candidate['sha256'] == record['sha256'] and Path(candidate['file']).name == Path(record['file']).name:
            exact(candidate)
            return candidate
    raise AssertionError(('Original leaf alias missing', record))


def delivery_observation():
    progress = ROOT / 'book/coverage/progress.json'
    repository = ROOT / 'reports/book/publication-repo'
    result = subprocess.run(['git', '-C', str(repository), 'rev-parse', 'HEAD'],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    return {'observed_at_utc': datetime.now(timezone.utc).isoformat(),
            'progress': ref(progress) if progress.exists() else None,
            'publication_HEAD': result.stdout.strip() if result.returncode == 0 else None,
            'git_read_exit_code': result.returncode,
            'scope': 'Read-only observation; concurrent authorized Root checkpoint33 delivery is outside this guard.'}


def main():
    assert not CANONICAL.exists()
    assert not (OUT / 'iqc21-future34-paired-readiness-v1.json').exists()
    source_bytes = SOURCE.read_bytes()
    assert sha(SOURCE) == '35a5f818c483645ad8bf66821900417e9dcb709458d5552599d5c480571de249'
    index = json.loads(INDEX.read_bytes())
    task = index['next_tasks'][0]
    assert task['id'] == 'close_shifted_temporal_IQC_Exercise14_6'
    assert exact(task['source']) == SOURCE
    assert exact(task['packet']) == PEER
    peer = json.loads(PEER.read_bytes())
    request = json.loads(exact(peer['original_full_request']).read_bytes())
    assert peer['errors'] == [] and peer['whole_exercise_decision']['entire_current_exercise_approved']
    assert len(peer['all21_complete_public_body_assessments']) == 21
    assert all(a['entire_body_read'] and a['approved'] for a in peer['all21_complete_public_body_assessments'])
    source_text = source_bytes.decode()
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b|#eval', source_text)
    public = declarations(source_text)
    theorem_names = [d['name'] for d in public if d['kind'] == 'theorem']
    assert len(public) == 26 and len(theorem_names) == 21
    assert theorem_names == request['public_theorem_names']
    assert {a['declaration'] for a in peer['all21_complete_public_body_assessments']} == set(theorem_names)
    selection = json.loads(SELECTION.read_bytes())
    ready33 = json.loads(READY33.read_bytes())
    selected_names = set()
    for name, selected_record in selection['proof_files'].items():
        selected_path = ROOT / name
        assert sha(selected_path) == selected_record['sha256']
        selected_names.update(d['name'] for d in declarations(selected_path.read_text()))
    assert set(d['name'] for d in public).isdisjoint(selected_names)
    assert sha(SOURCE) not in {r['sha256'] for r in selection['proof_files'].values()}
    imported = re.findall(r'^import\s+(\S+)\s*$', source_text, re.M)
    assert imported == ['SafeLearning.CompleteModulesNNTemporalDiagonal25', 'SafeLearning.CompleteModulesNNTanhOffset24']
    import_checks = []
    for module in imported:
        path = LEAN / (module.replace('.', '/') + '.lean')
        name = str(path.relative_to(ROOT))
        assert name in selection['proof_files'] and sha(path) == selection['proof_files'][name]['sha256']
        imported_names = {d['name'] for d in declarations(path.read_text())}
        assert imported_names <= selected_names and imported_names.isdisjoint({d['name'] for d in public})
        import_checks.append({'module': module, 'actual_selected_source': ref(path),
                              'public_name_count': len(imported_names), 'new_namespace_name_conflicts': []})
    inventory_path = ROOT / 'book/coverage/inventory.json'
    inventory = json.loads(inventory_path.read_bytes())
    exercise = next(row for row in inventory['exercises'] if row['key'] == 'nn-in-the-loop.html::exercise-20')
    assert exercise == peer['entire_current_exercise']
    literals = {}
    for key, decision in peer['whole_literal_decisions'].items():
        row = next(row for row in inventory['material_source_units'] if row['key'] == key)
        assert row == decision['entire_literal'] and decision['entire_current_literal_approved']
        literals[key] = row
    owner = json.loads((ROOT / 'book/coverage/modules.json').read_bytes())
    current_owner_exercise = next(row for row in owner['exercises'] if row['inventory_key'] == exercise['key'])
    assert current_owner_exercise['status'] == 'partial'
    protected = {name: row['sha256'] for name, row in selection['proof_files'].items()}
    protected.update({str(path.relative_to(ROOT)): sha(path) for path in (ROOT / 'SafeLearning').iterdir() if path.is_file() and path.suffix in {'.html', '.css', '.js'}})
    assert len([name for name in protected if name.startswith('SafeLearning/')]) == 31
    for path in [inventory_path, *(ROOT / f'book/coverage/{owner}.json' for owner in ('foundations', 'applied', 'modules', 'core')),
                 LEAN / 'SafeLearning.lean', LEAN / 'AxiomAudit.lean', LEAN / 'lakefile.toml', LEAN / 'lake-manifest.json', LEAN / 'lean-toolchain',
                 PEER, SOURCE, INDEX, SELECTION, READY33, AUDIT32, Path(__file__)]:
        protected[str(path.relative_to(ROOT))] = sha(path)

    def guard():
        return [name for name, fingerprint in protected.items() if sha(ROOT / name) != fingerprint]

    assert guard() == []
    baseline_path = OUT / 'protected-selected33-Source88-owner33-mainaggregate-baseline-v1.json'
    new_json(baseline_path, {'protected_sha256': protected, 'selected33_proof_count': selection['proof_file_count'],
                           'site_asset_count': 31, 'current_aggregate_protected': ['verification/lean/SafeLearning.lean', 'verification/lean/AxiomAudit.lean'],
                           'concurrent_progress_and_publication_delivery_excluded_from_stability_assertions': True})
    delivery_before = delivery_observation()
    CANONICAL.write_bytes(source_bytes)
    snapshots = OUT / 'source-snapshots'
    snapshots.mkdir()
    snapshot = snapshots / CANONICAL.name
    snapshot.write_bytes(source_bytes)
    assert CANONICAL.read_bytes() == SOURCE.read_bytes() == snapshot.read_bytes()
    records = []
    for kind, command in [('standalone', ['lake', 'env', 'lean', 'SafeLearning/' + CANONICAL.name]),
                          ('named', ['lake', 'build', 'SafeLearning.' + CANONICAL.stem])]:
        assert guard() == []
        source_before = sha(CANONICAL)
        started = datetime.now(timezone.utc).isoformat()
        tick = time.monotonic()
        log = OUT / f'IQC21-{kind}-actual-v1.log'
        with log.open('xb') as stream:
            native = subprocess.run(command, cwd=LEAN, stdout=stream, stderr=subprocess.STDOUT)
        errors = guard()
        record = {'status': 'passed' if native.returncode == 0 and not errors else 'failed',
            'kind': kind, 'actual_command': command, 'actual_workdir': str(LEAN),
            'actual_exit_code': native.returncode, 'started_at_utc': started,
            'finished_at_utc': datetime.now(timezone.utc).isoformat(), 'elapsed_seconds': time.monotonic() - tick,
            'source': ref(CANONICAL), 'source_sha256_before': source_before, 'source_sha256_after': sha(CANONICAL),
            'source_snapshot': ref(snapshot), 'raw_log': ref(log), 'compiler_recorder': ref(Path(__file__)),
            'protected_baseline': ref(baseline_path), 'protection_errors': errors,
            'selected33_and_current_Source88_owner33_mainaggregate_unchanged': not errors,
            'no_eval_native_shortcut_or_substituted_source': True,
            'aggregate_kernel_owner_selection_or_publication_claimed': False, 'coverage_complete': False}
        record_path = OUT / f'IQC21-{kind}-actual-v1.json'
        new_json(record_path, record)
        records.append({'kind': kind, 'actual_record': ref(record_path), 'raw_log': ref(log),
                        'source_snapshot': ref(snapshot), 'actual_exit_code': native.returncode})
        print(json.dumps({'phase': kind, 'actual_exit_code': native.returncode, 'protection_errors': errors}), flush=True)
        assert native.returncode == 0 and errors == []
    assert guard() == []
    delivery_after = delivery_observation()
    histories = []
    for history in peer['all_original14_genuine_native_histories']:
        row = {'trial': history['trial'], 'actual_exit_code': history['actual_exit_code'],
               'original_elapsed_seconds': history['original_elapsed_seconds']}
        for field in ('native', 'source', 'source_snapshot', 'raw_log'):
            if field in history:
                row[field] = original_alias(history[field], peer)
        histories.append(row)
    support = []
    for original in peer['all9_complete_selected_sources_read']:
        source = original_alias(original, peer)
        matches = [name for name, row in selection['proof_files'].items() if row['sha256'] == source['sha256']]
        assert len(matches) == 1
        support.append({'original_physical_source': source, 'retained_selected33_source': ref(ROOT / matches[0])})
    summary_path = OUT / 'IQC21-current-Exercise14_6-four-literal-correspondence-summary-v1.json'
    clause_routes = [
        {'clause': 'Exact two shifted tanh functions, zero origin and inherited zero-one chord slopes.',
         'hypotheses': 'Actual centers0 and2; every real chord; shifted(center,s)=tanh(s+center)-tanh(center).',
         'reused_selected_declarations': ['SafeLearning.CompleteModulesNNTanhOffset24.actual_both_literal_shifted_functions', 'SafeLearning.CompleteModulesNNTanhOffset24.actual_every_shifted_channel_vanishes_and_has_own_valid_sector']},
        {'clause': 'Doubly hyperdominant coupling has the printed difference-product form and a genuinely negative shifted-input counterexample; its decimal values are rounded.',
         'hypotheses': 'Actual real2x2 matrix[[1,-1],[-1,1]] and exact input(-1,-3/2); admission of the repeated class uses its off-diagonal/row/column conditions.',
         'reused_selected_declarations': ['SafeLearning.CompleteModulesNNTanhOffset24.actual_source_matrix_qc_is_the_difference_product', 'SafeLearning.CompleteModulesNNTanhOffset24.actual_literal_unequal_tanh_offsets_violate_the_printed_coupled_qc', 'SafeLearning.CompleteModulesNNTanhOffset24.actual_literal_numbers_are_rounded_with_strict_non_equalities', 'SafeLearning.CompleteModulesNNDoublyHyperdominant25.actual_repeated_monotone_map_satisfies_every_doubly_hyperdominant_qc'],
         'future_declarations': ['SafeLearning.CompleteModulesShiftedTemporalIQC31.actual_printed_offset_counterexample_refutes_the_uniform_qc_premise'],
         'limit': 'Invalid uniform QC premise does not imply a false final stability conclusion.'},
        {'clause': 'Bias-free origin equilibrium gives shared unshifted functions; equal centers also suffice, and coupling requires common slope bounds.',
         'hypotheses': 'Actual all-depth bias-free tanh network at zero, or common equilibrium centers; a common scalar slope interval for coupled neurons.',
         'reused_selected_declarations': ['SafeLearning.CompleteModulesNNTanhSectorClass24.actual_bias_free_tanh_network_at_zero_has_zero_outputs_and_preactivations_at_every_depth', 'SafeLearning.CompleteModulesNNTwoLayerLFT23.actual_equal_offsets_share_the_same_shifted_nonlinearity', 'SafeLearning.CompleteModulesNNTwoLayerLFT23.actual_equal_offset_common_slope_group_keeps_the_repeated_qc'],
         'future_declarations': ['SafeLearning.CompleteModulesShiftedTemporalIQC31.actual_loop_transformed_slope_channel_has_the_full_monovary_qc', 'SafeLearning.CompleteModulesShiftedTemporalIQC31.actual_different_local_slope_pairs_can_break_coupling_of_one_shared_activation']},
        {'clause': 'Independent shifted channels retain diagonal and robust full-block sector-box choices.',
         'hypotheses': 'Each channel has its own zero-one sector; full-block matrix is robustly nonnegative for every diagonal gain in the sector box.',
         'reused_selected_declarations': ['SafeLearning.CompleteModulesNNTanhOffset24.actual_every_shifted_channel_has_valid_nonnegative_diagonal_sector_weights', 'SafeLearning.CompleteModulesNNTanhOffsetConsequences24.actual_literal_diagonal_products_are_nonnegative_rounded_and_not_equal', 'SafeLearning.CompleteModulesNNTanhSectorClass24.actual_robust_full_block_psd_condition_applies_to_independent_scalar_sector_channels']},
        {'clause': 'Diagonal temporal coefficients give genuine finite-horizon hard IQCs through the actual zero-state causal filter and full middle matrix.',
         'hypotheses': 'Finite FIR lag band, coefficient c(d)<=0 away from zero and nonnegative retained coefficient sum per channel; actual channel time invariance, slope bounds, origin zero and zero initial delay state.',
         'future_declarations': theorem_names[:5] + theorem_names[6:19],
         'limit': 'No generic spectral-factor, arbitrary infinite filter or general stability lemma is claimed.'},
        {'clause': 'The enlarged odd class needs actual oddness; a shifted tanh channel is odd iff its center is zero.',
         'hypotheses': 'Actual shifted tanh for every real input; no enlarged odd multiplier theorem is asserted.',
         'future_declarations': ['SafeLearning.CompleteModulesShiftedTemporalIQC31.actual_shifted_tanh_is_odd_exactly_when_its_equilibrium_center_is_zero']},
    ]
    for route in clause_routes:
        assert all(name in selected_names for name in route.get('reused_selected_declarations', []))
        assert all(name in theorem_names for name in route.get('future_declarations', []))
    new_json(summary_path, {'status': 'prepared_exact_current_Exercise14_6_and_four_literal_correspondence_only_not_promoted',
        'whole_mathematical_peer': ref(PEER), 'source': ref(CANONICAL), 'original_source': ref(SOURCE),
        'all21_complete_proof_bodies_and5_definition_bodies_read_for_preparation': True,
        'all21_prior_peer_assessments_read': peer['all21_complete_public_body_assessments'],
        'entire_current_exercise': exercise, 'current_owner_exercise_status': current_owner_exercise['status'],
        'whole_exercise_peer_decision': peer['whole_exercise_decision'],
        'whole_four_literal_peer_decisions': peer['whole_literal_decisions'], 'precise_clause_routes': clause_routes,
        'retained_selected_support_sources': support,
        'source_qualification_required': False, 'current_NN_page': ref(ROOT / 'SafeLearning/nn-in-the-loop.html'),
        'current_inventory': ref(inventory_path), 'current_modules_owner': ref(ROOT / 'book/coverage/modules.json'),
        'final_diagonal_T_scope': 'Bounded current-source/selected-proof association from the exact existing whole peer; no new generic LMI or stability theorem.',
        'whole_scope_limits': ['No local-box extension or general enlarged odd multiplier theorem.', 'No source change, owner promotion, aggregate selection or checkpoint34 delivery performed.'], 'coverage_complete': False})
    readiness_path = OUT / 'iqc21-future34-paired-readiness-v1.json'
    new_json(readiness_path, {'status': 'passed_actual_exact_IQC21_future34_canonical_standalone_named_pairs_unselected_only',
        'errors': [], 'completed_at_utc': datetime.now(timezone.utc).isoformat(), 'source_count': 1,
        'public_theorem_count': 21, 'public_name_count': 26, 'actual_compiler_command_count': 2,
        'canonical_source': ref(CANONICAL), 'original_source': ref(SOURCE),
        'original_namespaces_preserved': ['SafeLearning.CompleteModulesShiftedTemporalIQC31'],
        'public_declarations': public, 'public_theorem_names': theorem_names, 'actual_paired_records': records,
        'correspondence_summary': ref(summary_path), 'original_whole_mathematical_peer': ref(PEER),
        'original_full_request': peer['original_full_request'], 'retained_original14_native_histories': histories,
        'original_failed_trials_and_measured_times_not_rewritten': True,
        'selected33_public_name_overlap': [], 'selected33_import_checks': import_checks,
        'protected_baseline': ref(baseline_path), 'protection_errors': guard(),
        'all1261_selected33_proof_bytes_all31_site_assets_Source88_inventory_fourowner33_and_mainaggregate_preserved': True,
        'concurrent_Root33_delivery_outside_guard': {'before': delivery_before, 'after': delivery_after,
            'progress_or_publicationrepo_written_by_this_preparation': False},
        'selected33_selection': ref(SELECTION), 'currently_selected_in33': False,
        'in_owner33_proof_metadata': False, 'current_aggregate_modified': False,
        'source_qualification_or_owner_promotion_or_publication_performed': False,
        'fresh_standard_axiom_probe_or_aggregate_kernel_audit_performed': False,
        'requires_next_checkpoint_current_owner_mapping_selection_aggregate_kernel_axiom_ledger_and_delivery': True,
        'not_part_of_checkpoint33_evidence_plan': True,
        'prior_read_only_inspection_failure_preserved': ref(OUT / 'preparation-inspection-failure-v1.json'), 'coverage_complete': False})
    print(json.dumps({'readiness': ref(readiness_path), 'canonical_source': ref(CANONICAL),
                     'unselected_future34': True}), flush=True)


if __name__ == '__main__':
    main()

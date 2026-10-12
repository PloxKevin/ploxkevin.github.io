#!/usr/bin/env python3
"""Independent active-field, exact-inverse and literal-clause owner review."""
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import contextlib
import copy
import importlib.util
import json
import re
import sys
import tempfile
import time
from review_six_qualifier_cumulative_v1 import ROOT, OUT, ref, exact, read_json, sha_bytes

sys.dont_write_bytecode = True
BINDING = ROOT / 'book/coverage/checks/checkpoint33-ledgers/owner-candidate-binding-v2.json'
EXECUTION = ROOT / 'book/coverage/checks/checkpoint33-ledgers/isolated-validator-execution-v2.json'


def encode(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()


def access(document, path):
    for key in path:
        document = document[key]
    return document


def apply_exact_patch(document, patches, backward=False):
    for patch in reversed(patches) if backward else patches:
        parent = access(document, patch['pointer'][:-1])
        key = patch['pointer'][-1]
        old_prefix, new_prefix = ('after', 'before') if backward else ('before', 'after')
        if patch[old_prefix + '_exists']:
            assert parent[key] == patch[old_prefix]
        elif isinstance(parent, list):
            assert key == len(parent)
        else:
            assert key not in parent
        if patch[new_prefix + '_exists']:
            value = copy.deepcopy(patch[new_prefix])
            if isinstance(parent, list) and key == len(parent):
                parent.append(value)
            else:
                parent[key] = value
        elif isinstance(parent, list):
            assert key == len(parent) - 1
            parent.pop()
        else:
            del parent[key]
    return document


def actual_delta(a, b, prefix=()):
    """Identify real differing leaves without using the candidate builder."""
    result = {}
    if isinstance(a, dict) and isinstance(b, dict):
        for key in a.keys() | b.keys():
            path = prefix + (key,)
            if key not in a:
                result[path] = {'before_exists': False, 'after_exists': True, 'after': b[key]}
            elif key not in b:
                result[path] = {'before_exists': True, 'before': a[key], 'after_exists': False}
            else:
                result.update(actual_delta(a[key], b[key], path))
    elif isinstance(a, list) and isinstance(b, list) and len(b) >= len(a):
        for i, value in enumerate(a):
            result.update(actual_delta(value, b[i], prefix + (i,)))
        for i in range(len(a), len(b)):
            result[prefix + (i,)] = {'before_exists': False, 'after_exists': True, 'after': b[i]}
    elif a != b:
        result[prefix] = {'before_exists': True, 'before': a, 'after_exists': True, 'after': b}
    return result


def flatten(routes, field):
    values = [v for clause in routes for v in clause[field]]
    return sorted(set(values)) if field == 'lean_declarations' else list(dict.fromkeys(values))


def main():
    start = datetime.now(timezone.utc).isoformat()
    tick = time.monotonic()
    result_path = OUT / 'independent-four-owner-candidates-review-v4.json'
    assert not result_path.exists()
    binding = json.loads(BINDING.read_bytes())
    assert ref(BINDING)['sha256'] == '4f511019dc4a32d7c876b46680242d6dcac09f9f028818666871ba0bdb5148da'
    execution = json.loads(EXECUTION.read_bytes())
    assert execution['status'] == 'passed' and execution['actual_exit_code'] == 0
    for value in execution.values():
        if isinstance(value, dict) and 'file' in value and 'sha256' in value:
            exact(value)
    inventory = read_json(binding['inventory'])
    review = read_json(binding['qualification_review'])
    component_review = read_json(binding['component_rebase_review'])
    readiness = read_json(binding['canonical_readiness'])
    routes = read_json(binding['exact_subclaims_and_assumptions'])
    assert readiness['errors'] == [] and readiness['source_count'] == 7
    assert readiness['public_theorem_count'] == 78 and readiness['actual_compiler_command_count'] == 14
    mapping = {row['key']: row for row in routes['whole_units']}
    assert sorted(mapping) == review['approved_prospective_whole_keys']
    material = {row['key']: row for row in inventory['material_source_units']}
    exercises = {row['key']: row for row in inventory['exercises']}
    selection_path = ROOT / 'reports/full-coverage/checkpoint-32-selection.json'
    selection = json.loads(selection_path.read_bytes())
    canonical_sources = {}
    receipt_checks = []
    for family in readiness['sources']:
        source = exact(family['canonical_source_ref'])
        assert source.read_bytes() == exact(family['original_tmp_source']).read_bytes()
        canonical_sources[family['canonical_source']] = family['canonical_source_ref']['sha256']
        assert len(family['actual_paired_records']) == 2
        assert {p['kind'] for p in family['actual_paired_records']} == {'standalone', 'named'}
        for pair in family['actual_paired_records']:
            native = read_json(pair['actual_record'])
            assert native['actual_exit_code'] == pair['actual_exit_code'] == 0
            exact(pair['raw_log']); exact(pair['source_snapshot']); exact(pair['source'])
            receipt_checks.append(pair['actual_record'])
    selected_sources = {name: row['sha256'] for name, row in selection['proof_files'].items()}
    permitted_sources = {**selected_sources, **canonical_sources}
    assert len(routes['used_declarations']) == 87
    for name, used in routes['used_declarations'].items():
        source = exact(used['source'])
        assert used['source']['file'] in permitted_sources
        assert permitted_sources[used['source']['file']] == used['source']['sha256']
        assert re.search(r'\btheorem\s+' + re.escape(name.rsplit('.', 1)[1]) + r'\b', source.read_text()), name
    active_fields = {'source_text': 'source_text', 'source_text_sha256': 'text_sha256',
                     'text_sha256': 'text_sha256', 'source_sha256': 'source_sha256'}
    changed_top_allowed = {'source_sha256', 'exercises', 'material_claims', 'proof_files',
                           'proof_sha256', 'counts', 'current_inventory', 'current_inventory_sha256'}
    node922 = 'primer-basics.html::node-922'
    candidates = {}
    reports = []
    original_refs = []
    for replacement in binding['replacements']:
        before_path = exact(replacement['before'])
        candidate_path = exact(replacement['candidate'])
        inverse = read_json(replacement['exact_inverse'])
        before_raw = before_path.read_bytes()
        candidate_raw = candidate_path.read_bytes()
        old, candidate = json.loads(before_raw), json.loads(candidate_raw)
        owner = before_path.stem
        original_refs.append(replacement['before'])
        assert encode(old) == before_raw and encode(candidate) == candidate_raw
        assert inverse['baseline'] == replacement['before'] and inverse['candidate'] == replacement['candidate']
        patch_map = {tuple(p['pointer']): {k: v for k, v in p.items() if k != 'pointer'} for p in inverse['patches']}
        assert len(patch_map) == len(inverse['patches'])
        assert patch_map == actual_delta(old, candidate)
        reconstructed = apply_exact_patch(copy.deepcopy(candidate), inverse['patches'], backward=True)
        assert encode(reconstructed) == before_raw
        del reconstructed
        reconstructed = apply_exact_patch(copy.deepcopy(old), inverse['patches'])
        assert encode(reconstructed) == candidate_raw
        del reconstructed
        assert set(candidate) - set(old) == {'current_checkpoint33_identity'}
        assert set(old) <= set(candidate)
        historical = sorted(k for k in old if k not in changed_top_allowed)
        assert all(old[k] == candidate[k] for k in historical)
        assert old['scope_pages'] == candidate['scope_pages']
        assert candidate['source_sha256'] == {**old['source_sha256'], **{page: inventory['source_sha256'][page] for page in old['scope_pages']}}
        assert len(candidate['exercises']) == len(old['exercises'])
        for original, final in zip(old['exercises'], candidate['exercises']):
            assert {k: v for k, v in original.items() if k != 'source_sha256'} == {k: v for k, v in final.items() if k != 'source_sha256'}
            if 'source_sha256' in final:
                assert final['source_sha256'] == exercises[final['inventory_key']]['source_sha256']
        promotions = {row['index']: row for row in replacement['approved_whole_promotions']}
        component_decisions = {row['claim_id']: row for row in component_review['components']}
        carried = []
        pending922 = []
        for index, original in enumerate(old['material_claims']):
            final = candidate['material_claims'][index]
            assert original['id'] == final['id']
            keys = final.get('source_unit_keys', [])
            if len(keys) == 1:
                literal = material[keys[0]]
                for field, source_field in active_fields.items():
                    if field in final:
                        assert final[field] == literal[source_field], (owner, index, field)
            if index in promotions:
                promotion = promotions[index]
                key = promotion['key']
                assert owner == 'foundations' and original['status'] == 'pending' and final['status'] == 'proved'
                assert keys == [key] and final['kind'] == 'reviewed_entire_current_mathematical_literal'
                assert final['statement_in_prose'] == material[key]['source_text']
                assert final['original_pending_record'] == original
                assert final['remaining_gaps'] == []
                clauses = mapping[key]['all_subclaim_correspondence']
                assert final['all_subclaim_correspondence'] == clauses
                assert final['lean_declarations'] == flatten(clauses, 'lean_declarations')
                assert final['hypotheses'] == flatten(clauses, 'hypotheses')
                assert final['independent_whole_literal_peer'] == mapping[key]['independent_whole_peer']
                exact(final['independent_whole_literal_peer'])
                for clause in clauses:
                    assert clause['source_clause'] and clause['hypotheses']
                    assert all(n in routes['used_declarations'] for n in clause['lean_declarations'])
                    assert clause['classification'] in {'reviewed_mathematical_subclaim', 'reviewed_factual_attribution_and_pedagogical_instruction'}
                assert key != node922
            elif keys == [node922] and original['status'] == 'pending':
                assert owner == 'foundations' and final['status'] == 'pending'
                assert final['remaining_gaps'] == review['node922']['remaining']
                assert final['lean_declarations'] == original['lean_declarations']
                allowed = set(active_fields) | {'statement_in_prose', 'remaining_gaps', 'correspondence', 'qualification_and_current_source_review'}
                assert {k: v for k, v in original.items() if k not in allowed} == {k: v for k, v in final.items() if k not in allowed}
                pending922.append(final['id'])
            else:
                assert {k: v for k, v in original.items() if k not in active_fields} == {k: v for k, v in final.items() if k not in active_fields}
                if final['id'] in component_decisions:
                    decision = component_decisions[final['id']]
                    assert decision['original_row'] == original and decision['candidate_row'] == final
                    carried.append(final['id'])
        old_proof_files = old['proof_files']
        if isinstance(old_proof_files, list):
            assert candidate['proof_files'][:len(old_proof_files)] == old_proof_files
        else:
            assert candidate['proof_files'] == old_proof_files
        assert all(candidate['proof_sha256'][name] == value for name, value in old.get('proof_sha256', {}).items())
        if owner == 'foundations':
            assert len(promotions) == 10 and len(carried) == 18 and len(pending922) == 1
            assert len(candidate['material_claims']) == len(old['material_claims']) + 1
            component = candidate['material_claims'][-1]
            assert component['id'] == node922 + '::qualified-envelope-and-log-curve-component33'
            assert component['source_unit_keys'] == [node922] and component['status'] == 'proved'
            assert component['kind'] == 'reviewed_mathematical_subclaim' and component['remaining_gaps'] == []
            assert component['all_subclaim_correspondence'] == routes['node922_component_routes']
            assert component['lean_declarations'] == flatten(routes['node922_component_routes'], 'lean_declarations')
            assert component['hypotheses'] == flatten(routes['node922_component_routes'], 'hypotheses')
            assert candidate['proof_files'][len(old_proof_files):] == list(canonical_sources)
            assert {name: candidate['proof_sha256'][name] for name in canonical_sources} == canonical_sources
            assert candidate['counts']['material_claim_statuses'] == dict(Counter(row['status'] for row in candidate['material_claims']))
            for key in old['counts']:
                if key != 'material_claim_statuses':
                    assert candidate['counts'][key] == old['counts'][key]
        else:
            assert len(candidate['material_claims']) == len(old['material_claims'])
            assert candidate['proof_files'] == old['proof_files'] and candidate.get('proof_sha256') == old.get('proof_sha256')
            assert candidate['counts'] == old['counts'] and promotions == {} and carried == []
        identity = candidate['current_checkpoint33_identity']
        assert identity['inventory'] == binding['inventory']
        assert identity['node922_whole_pending'] is True
        assert identity['historical_reviews_source_bytes_native_times_and_evidence_preserved'] is True
        assert identity['actual_selected_aggregate_and_owner_installation_pending'] is True
        reports.append({'owner': owner, 'before': replacement['before'], 'candidate': replacement['candidate'],
            'exact_inverse': replacement['exact_inverse'], 'minimal_changed_leaf_count': len(patch_map),
            'exact_forward_and_inverse_restore_original_serialized_bytes': True,
            'all_unchanged_historical_top_fields': historical,
            'old_exercise_statements_claims_statuses_unchanged': True,
            'new_whole_promotions': replacement['approved_whole_promotions'],
            'carried_component_ids': carried, 'node922_pending_ids': pending922})
        candidates[owner] = candidate_path
        del old, candidate, inverse, patch_map, before_raw, candidate_raw
    assert sorted(candidates) == ['applied', 'core', 'foundations', 'modules']
    exact(binding['applied_promotions_unchanged'])
    validator_path = ROOT / 'book/coverage/validate.py'
    sys.path.insert(0, str(ROOT / 'book/coverage'))
    spec = importlib.util.spec_from_file_location('independent_checkpoint33_validator', validator_path)
    validator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(validator)
    log = OUT / 'independent-four-owner-validator-v4.log'
    with tempfile.TemporaryDirectory(prefix='checkpoint33-independent-owner-audit-') as directory:
        tree = Path(directory)
        (tree / 'book/coverage').mkdir(parents=True)
        (tree / 'verification').mkdir()
        (tree / 'SafeLearning').symlink_to(ROOT / 'SafeLearning', target_is_directory=True)
        (tree / 'verification/lean').symlink_to(ROOT / 'verification/lean', target_is_directory=True)
        (tree / 'book/coverage/inventory.json').symlink_to(exact(binding['inventory']))
        for owner, candidate in candidates.items():
            (tree / f'book/coverage/{owner}.json').symlink_to(candidate)
        validator.ROOT = tree
        with log.open('x') as output, contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            audit = validator.validate()
            print(json.dumps({field: audit[field] for field in ('integrity_status', 'mathematical_coverage_complete', 'counts', 'errors')}, indent=2))
    assert audit['integrity_status'] == 'passed' and audit['errors'] == []
    assert audit['counts']['material_review_statuses'] == {'reviewed': 4851, 'pending': 7923}
    assert {k: v for k, v in audit['counts']['statuses'].items() if k.startswith('exercise:')} == {'exercise:complete_math': 536, 'exercise:pending': 12, 'exercise:partial': 8}
    assert not audit['mathematical_coverage_complete']
    audit_path = OUT / 'independent-four-owner-ledger-audit-v4.json'
    audit_path.write_text(json.dumps(audit, indent=2, ensure_ascii=False) + '\n')
    for record in original_refs:
        exact(record)
    for replacement in binding['replacements']:
        exact(replacement['candidate']); exact(replacement['exact_inverse'])
    report = {'status': 'approved_independent_four_owner_candidates_minimal_inverse_exact_active_rebases_and_ten_whole_clause_routes',
        'errors': [], 'started_at_utc': start, 'finished_at_utc': datetime.now(timezone.utc).isoformat(),
        'elapsed_seconds': time.monotonic() - tick, 'binding': ref(BINDING), 'builder_execution': ref(EXECUTION),
        'exact_clause_and_assumption_routes_read': binding['exact_subclaims_and_assumptions'],
        'actual_builder_and_mapping_helpers_read': [execution['actual_helper'], execution['mapping_helper']],
        'seven_canonical_sources_equal_originals_and14_passed_receipts_checked': receipt_checks,
        'all87_used_route_declarations_from_retained1254_or_exact_seven_additions': True,
        'owner_decisions': reports,
        'semantic_route_assessment': {
            'Basics916918': 'Exact error conventions, true recurrence domains, positive reciprocal-power asymptotics, upper-bound countermodel and scalar C2 regular-root invariant Newton neighborhood are separately mapped; shared overlapping clauses add no proof count.',
            'Norm305307311': 'All simultaneous formulas use the preceding positive row/column domain and established norm/Holder-conjugate conventions, including endpoints. Node311 keeps zero-operator dual-ball attenuation and the exact fixture/rounding/full ellipse domain.',
            'Box332': 'Positive radius supplies both nonnegative image/segment identities and nondegenerate scaled independence. Exact finite Minkowski image, attained smallest box and full square area fixture remain separately routed.',
            'Cube191': 'The source s>=0,tau>0,d>=1 conditions match geometry/grid domains. Constructed counts are covering-number upper bounds; ambient-center minimum is derived by projection; general sampled m0 margin retains LipschitzOn/net hypotheses.',
            'Signed205': 'Nonempty proper closed-set domain establishes signed sides and zero boundary; Hausdorff real suprema retain nonempty compactness; sign convention carries no trajectory guarantee.',
            'PositiveP171': 'Finite nontrivial coordinates and 0<p<1 give triangle failure. Exact half-exponent fixture is separate. Paper norm attribution/editorial instruction is explicitly nonformal and uses the preserved whole-peer assessment.',
            'Planar529': 'Real symmetric2x2 forms, primitive class hypotheses, actual orthogonal coordinates, nonzero singular PSD and explicit zero exception cover every geometric clause; generic diagonal PSD equivalence reuses the selected declaration.',
            'Node922_component': 'Only exact envelope certificates, positive-tolerance asymptotics, numerical first envelope indices and exact positive log-curve statements are added; the broader linked algorithm obligations stay pending.'},
        'ten_whole_promotions_only': True, '18_existing_component_rows_exactly_rebased': True,
        'node922_broader_pending_row_preserved_and_one_bounded_component_added': True,
        'applied_promotions_unchanged': binding['applied_promotions_unchanged'],
        'fresh_independent_isolated_candidate_validator': {'source': ref(validator_path), 'raw_log': ref(log), 'audit': ref(audit_path), 'actual_exit_code': 0},
        'counts': audit['counts'], 'owner_installation_performed': False,
        'new_aggregate_kernel_or_publication_claimed': False, 'current_inputs_mutated': False,
        'prior_read_only_harness_failures_preserved': [ref(OUT / 'four-owner-review-inspection-failure-v1.json'), ref(OUT / 'four-owner-review-inspection-failure-v2.json'), ref(OUT / 'four-owner-review-inspection-failure-v3.json')],
        'coverage_complete': False}
    result_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(ref(result_path)))


if __name__ == '__main__':
    main()

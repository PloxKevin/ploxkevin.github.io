#!/usr/bin/env python3
"""Read-only continuation index from bounded, exact existing packets."""
from pathlib import Path
from datetime import datetime, timezone
import json
import sys
from review_six_qualifier_cumulative_v1 import ROOT, OUT, ref, exact, read_json

sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'book/coverage'))
from lean_names import declarations


def local_source(record, peer):
    if not Path(record['file']).is_absolute():
        exact(record)
        return record
    aliases = peer.get('bounded_original_ref_aliases', peer.get('all_original_byte_aliases', {}))
    values = aliases.values() if isinstance(aliases, dict) else aliases
    for alias in values:
        for field in ('original_byte_copy', 'original_closed_byte_copy', 'root_physical_original'):
            if isinstance(alias, dict) and field in alias:
                candidate = alias[field]
                if candidate.get('sha256') == record['sha256'] and not Path(candidate['file']).is_absolute():
                    exact(candidate)
                    return candidate
    raise AssertionError(('No exact Root alias', record))


def main():
    destination = OUT / 'next-unselected-work-index-v1.json'
    assert not destination.exists()
    inventory_path = ROOT / 'book/coverage/inventory.json'
    inventory = json.loads(inventory_path.read_bytes())
    material = {row['key']: row for row in inventory['material_source_units']}
    exercises = {row['key']: row for row in inventory['exercises']}
    selection_path = ROOT / 'reports/full-coverage/checkpoint-33-selection.json'
    selection = json.loads(selection_path.read_bytes())
    readiness_path = ROOT / 'book/coverage/checks/checkpoint33-proofs/actual-reviewed33-seven-canonical-paired-readiness-v1.json'
    readiness = json.loads(readiness_path.read_bytes())
    audit32_path = ROOT / 'reports/full-coverage/lean-checkpoint-32-source81-recovery-v1/verification-original.json'
    audit32 = json.loads(audit32_path.read_bytes())
    selected_names = {row['name'] for row in audit32['declarations']}
    selected_names.update(row['name'] for family in readiness['sources'] for row in family['public_declarations'])
    selected_hashes = {row['sha256'] for row in selection['proof_files'].values()}
    installed = json.loads((ROOT / 'reports/full-coverage/owner33-integration-v1.json').read_bytes())
    assert installed['applied']
    original_remaining_path = ROOT / 'book/coverage/remaining-exercises32.json'
    remaining32 = json.loads(original_remaining_path.read_bytes())
    owner_refs = {owner: ref(ROOT / f'book/coverage/{owner}.json') for owner in ('foundations', 'applied', 'modules', 'core')}
    owner_cache = {}
    current_unfinished = []
    for previous in remaining32['exercises']:
        owner = previous['owner']
        if owner not in owner_cache:
            owner_cache[owner] = json.loads((ROOT / owner_refs[owner]['file']).read_bytes())
        rows = [row for row in owner_cache[owner]['exercises'] if row['inventory_key'] == previous['inventory_key']]
        assert len(rows) == 1
        row = rows[0]
        assert row['status'] == previous['status'] and row['label'] == previous['label']
        claims = [{field: claim[field] for field in ('id', 'statement_in_prose', 'hypotheses', 'remaining_gaps')}
                  for claim in row['claims'] if claim['status'] == 'pending']
        assert claims == previous['pending_claims']
        literal = exercises[row['inventory_key']]
        assert row['source_sha256'] == literal['source_sha256']
        current_unfinished.append({'owner': owner, 'inventory_key': row['inventory_key'],
            'label': row['label'], 'status': row['status'], 'current_text_sha256': literal['text_sha256'],
            'current_page_sha256': literal['source_sha256'], 'pending_claims': claims})
    assert len(current_unfinished) == 20
    assert sum(r['status'] == 'partial' for r in current_unfinished) == 8
    assert sum(r['status'] == 'pending' for r in current_unfinished) == 12

    paths = {
        'NN65': 'book/coverage/checks/future32-core/NN143-full-composition-independent-modules-v1/modules-NN143-exact-four-line-prospective-entire-three-part-exercise-full-mathematical-composition-independent-modules32-closed-peer-v1.json',
        'NN_narrow': 'book/coverage/checks/future32-core/NN143-four-line-narrow-independent-foundations-v1/modules-NN143-four-line-full-literal-support-fresh-full29-parser-narrow-independent-foundations32-closed-peer-v1.json',
        'IQC21': 'book/coverage/checks/future32-core/IQC21-full-independent-foundations-v1/modules-IQC21-entire-current-Exercise14_6-four-literals-full-mathematical-independent-foundations32-closed-peer-v1.json',
        'NN26': 'book/coverage/checks/future32-core/NN26-components-independent-foundations-v1/modules-NN26-entire-source-two-exercises-ten-literals-exact-components-independent-foundations32-closed-peer-v1.json',
        'Conditional28': 'book/coverage/checks/future32-applied/conditional28-independent-foundations-v1/applied-conditional28-entire-source-current387-components-prospective387-whole-independent-foundations32-closed-peer-v1.json',
        'Conditional_narrow': 'book/coverage/checks/future32-applied/conditional28-independent-foundations-v1/applied-conditional387-two-exact-qualifiers-full-literal-support-fresh29-parser-independent-foundations32-closed-peer-v1.json',
        'Polygonal14': 'book/coverage/checks/future32-applied/polygonal14-independent-v1/polygonal14-all-bodies-actual-Euler-component-independent-applied32-closed-peer-v1.json',
        'Integral39': 'book/coverage/checks/modules-future31/current81-integral39-ast19-realpair-v1/modules31-current81-integral39-realpair-ast19-independently-reviewed-final-offer-v4.json',
        'Convolution13': 'book/coverage/checks/future32-applied/convolution13-independent-foundations-v1/applied-convolution13-entire-source-entire-current1531-whole-independent-foundations32-closed-peer-v1.json',
        'StaticRegret20': 'book/coverage/checks/future32-applied/static-regret20-independent-v1/static-regret20-all-bodies-entire-current359-whole-independent-applied32-closed-peer-v1.json',
    }
    peers = {family: json.loads((ROOT / path).read_bytes()) for family, path in paths.items()}
    for family, peer in peers.items():
        assert peer.get('errors', []) == []
    sources = {
        'NN65': local_source(peers['NN65']['entire65_source'], peers['NN65']),
        'IQC21': local_source(peers['IQC21']['entire_source'], peers['IQC21']),
        'NN26': local_source(peers['NN26']['entire_final_source'], peers['NN26']),
        'Conditional28': local_source(peers['Conditional28']['entire_source'], peers['Conditional28']),
    }
    names = {}
    for family, source in sources.items():
        parsed = declarations(exact(source).read_text())
        names[family] = {row['name'] for row in parsed}
        assert source['sha256'] not in selected_hashes
        assert names[family].isdisjoint(selected_names), family
    assert names['NN26'] <= names['NN65']
    for key, pair in peers['NN65']['entire_current_and_prospective_changed_inventory_literals'].items():
        assert pair['entire_current'] == (exercises[key] if key in exercises else material[key])
    assert peers['IQC21']['entire_current_exercise'] == exercises['nn-in-the-loop.html::exercise-20']
    for key, decision in peers['IQC21']['whole_literal_decisions'].items():
        assert decision['entire_literal'] == material[key] and decision['entire_current_literal_approved']
    assert peers['Conditional28']['current_whole_decision']['entire_current_literal'] == material['primer-probability.html::node-387']
    nn_proposal_ref = peers['NN65']['proposal']
    nn_proposal = read_json(nn_proposal_ref)
    assert len(nn_proposal['all_four_entire_current_and_proposed_changed_literals']) == 4
    conditional_proposal_ref = peers['Conditional28']['exact_proposal']
    conditional_proposal = read_json(conditional_proposal_ref)
    assert len(conditional_proposal['exact_replacements']) == 2
    scope_plan_path = ROOT / 'book/coverage/checks/future32-core/NN26-components-independent-foundations-v1/exact-original-by-sha256/8cb0391c3ecc6caa404611c7b29c995788d525d18dea0dcdde9c5595edbcb424/modules-NN143-boundary-and144-explorer-concrete-scope-plan-v3.json'
    scope_plan = json.loads(scope_plan_path.read_bytes())
    assert ref(scope_plan_path)['sha256'] == '8cb0391c3ecc6caa404611c7b29c995788d525d18dea0dcdde9c5595edbcb424'
    nn_simulation = peers['NN65']['actual_finite_scalar_simulation_receipt']
    exact(nn_simulation)
    tasks = [
        {'priority': 1, 'id': 'close_shifted_temporal_IQC_Exercise14_6',
         'target_exercises': ['nn-in-the-loop.html::exercise-20'], 'current_status': 'partial',
         'source': sources['IQC21'], 'public_theorems': 21, 'public_names': len(names['IQC21']),
         'packet': ref(ROOT / paths['IQC21']), 'author_request': peers['IQC21']['original_full_request'],
         'existing_peer_scope': peers['IQC21']['whole_exercise_decision'],
         'whole_material_keys': sorted(peers['IQC21']['whole_literal_decisions']),
         'source_qualification': {'required': False, 'current_page_sha256': inventory['source_sha256']['SafeLearning/nn-in-the-loop.html']},
         'maturity': 'Historical TMP source and all21 bodies have a closed entire-current Exercise14.6/four-literal peer; final trial14 passed. Exact source is unselected in33.',
         'remaining_actions': ['Read all21 bodies and exact primary-association restrictions; preserve all14 failed/passed native histories and the old partial owner row.', 'Install the exact source under a fresh canonical filename with its original namespaces; run genuine standalone/named and standard-axiom checks in a fresh current Source88/owner33 context.', 'Rebuild an exact current-owner mapping for all six exercise requirements and the four specifically approved literals; preserve all unrelated pending claims and old proof entries.', 'Run selected aggregate, kernel and working/frozen ledger audit and delivery evidence before reporting completion.'],
         'scope_limits': ['No general odd/enlarged multiplier class, local-box extension or generic Section3 stability theorem is covered.', 'If combined with NN14.3 source changes, these unchanged IQC literals retain their text but need the new NN page fingerprint.']},
        {'priority': 2, 'id': 'apply_exact_NN14_3_precision_and_select_NN65',
         'target_exercises': ['nn-in-the-loop.html::exercise-17'], 'current_status': 'pending',
         'source': sources['NN65'], 'public_theorems': 65, 'public_names': len(names['NN65']),
         'packet': ref(ROOT / paths['NN65']), 'narrow_peer': ref(ROOT / paths['NN_narrow']),
         'proposal': nn_proposal_ref, 'individual_candidate': peers['NN65']['exact_prospective_page'],
         'finite_simulation_receipt': nn_simulation,
         'whole_decision': peers['NN65']['whole_exercise_decision'],
         'whole_material_keys': sorted(peers['NN65']['whole_four_changed_material_unit_decisions']),
         'source_qualification': {'required': True, 'exact_four_entire_line_changes': nn_proposal['all_four_entire_current_and_proposed_changed_literals'], 'current_page_sha256': inventory['source_sha256']['SafeLearning/nn-in-the-loop.html']},
         'maturity': 'Closed full prospective three-part exercise and four-literal mathematical composition plus a distinct full29 narrow parser peer. Exact65 source and all95 names are unselected in33.',
         'remaining_actions': ['Read exact59d proposal, full186b peer, narrow7b31 peer and all component/source native histories; do not use the earlier uncompiled891c candidate.', 'Apply only the four reviewed full-line replacements, rebuilding the full29 inventory from current Source88 pages and checking the exact full-page inverse.', 'Install and genuinely compile the full exact65 bytes with retained namespaces, checking all95 public names; do not install any redundant26/49/57/62 prefixes beside the65 source.', 'Map only the exact prospective Exercise14.3 and four approved material units against owner33, with actual domains and finite simulation kept distinct from the proved all-time conclusions.', 'Rebase unchanged IQC/other NN source identities without promoting Exercise14.4 or generic neighbors; run selected aggregate/kernel/axiom and ledger/delivery checks.'],
         'scope_limits': ['The supremal open certificate union is not an attained closed boundary box.', 'Rounded numbers need exact formulas/approximation signs and the full valid multiplier endpoints; lambda0.7499 is infeasible.', 'The finite scalar simulation is not an infinite-time proof and does not cover the default2D explorer.']},
        {'priority': 3, 'id': 'apply_Conditional28_node387_exact_domain_qualifiers',
         'target_exercises': [], 'target_material_keys': ['primer-probability.html::node-387'],
         'source': sources['Conditional28'], 'public_theorems': 28, 'public_names': len(names['Conditional28']),
         'packet': ref(ROOT / paths['Conditional28']), 'narrow_peer': ref(ROOT / paths['Conditional_narrow']),
         'author_request': peers['Conditional28']['request'], 'proposal': conditional_proposal_ref,
         'source_qualification': {'required': True, 'exact_replacements': conditional_proposal['exact_replacements'], 'current_page_sha256': inventory['source_sha256']['SafeLearning/primer-probability.html']},
         'maturity': 'Closed all28 full-body/prospective387 mathematical peer and distinct exact-two-qualifier/full29 parser peer. Source remains unselected in33.',
         'remaining_actions': ['Read all28 source/axiom histories, full mathematical peer and distinct narrow peer; preserve current387 pending record and any existing exact components.', 'Apply exactly the almost-every-observation/version-law qualifier and integrability/measurability/product qualifier, with no neighboring wording change.', 'Build fresh full29 parser evidence from the current pages; refresh Applied owner active identities and exact current387 whole correspondence.', 'Install exact original source bytes, run genuine canonical paired checks and selected/kernel/axiom/ledger/delivery checks.'],
         'scope_limits': ['Null-observation values are version-dependent; no unconditional density existence is asserted.', 'No neighboring total-variance node390 or environment-wide performance lemma is promoted.', 'This closes a material definition unit; it does not itself close any of the20 exercises.']},
        {'priority': 4, 'id': 'complete_actual_default2D_Exercise14_4_correspondence',
         'target_exercises': ['nn-in-the-loop.html::exercise-18'], 'current_status': 'pending',
         'existing_component_packet': ref(ROOT / paths['NN26']), 'component_source': sources['NN26'],
         'concrete_scope_plan': ref(scope_plan_path),
         'maturity': 'Existing26 source is independently component-reviewed only; its35 public names are a subset of the full95-name NN65 source. No closed whole14.4 or compiled actual2D scope is supplied.',
         'remaining_whole_gaps': [gap for gap in peers['NN26']['all_original_remaining_whole_gaps_retained'] if '14.4' in gap or 'two-state' in gap],
         'concrete_next_steps': ['Read the exact actual2D explorer IIFE and the separate14.4 plan; bind its genuine solver-produced delta/P/multipliers to producer evidence instead of the rounded nominal matrix.', 'Derive certified finite trajectory enclosures from(-17/4,14/5), including the time4 sector exit and entry by abouttime18 into the proposed escape region.', 'Prove the actual escape-region invariance and infinite divergence; handle exact box-corner trajectories and the correct delta domain separately.', 'Prove actual saddle derivative/spectrum and obtain an actual nonlinear stable-manifold/location correspondence or leave that clause explicitly pending; scalar contraction alone is insufficient.', 'Review the complete containment/induction explanation and every source clause before any whole exercise promotion.'],
         'source_qualification': {'already_reviewed_whole_proposal': False, 'warning': 'The static scope plan is an uncompiled research plan; its numerical or manifold assertions are not fresh proofs.'},
         'scope_limits': ['Avoid installing the redundant26 source after NN65.', 'The different14.4 map, saddle radius and2D invariant set cannot be inferred from the scalar14.3 open basin.']},
        {'priority': 5, 'id': 'finish_general_Filippov_local_existence_for_Exercise10_1',
         'target_exercises': ['barriers.html::exercise-16'], 'current_status': 'partial',
         'existing_component_peer': ref(ROOT / paths['Polygonal14']),
         'existing_author_request': peers['Polygonal14']['reviewed_request'],
         'maturity': 'The14 polygonal/Euler components are already selected in32 and retained in33; the exact peer explicitly declines general local-existence/whole-exercise approval.',
         'remaining_whole_gaps': peers['Polygonal14']['remaining_whole_existence_gaps'],
         'live_pending_claims': next(row['pending_claims'] for row in current_unfinished if row['inventory_key'] == 'barriers.html::exercise-16'),
         'concrete_next_steps': ['Reuse selected Euler24/polygonal14 and essential-velocity definitions as retained prerequisites; add an actual grid-interpolation construction.', 'Extract a compact subsequence on a fixed finite horizon and derive an absolutely continuous limiting curve, its integral representation and almost-everywhere inclusion.', 'Derive the local domain and locally essentially bounded measurable closed-loop field from the source hypotheses on f,g,u; establish local integral-curve existence from every permitted initial state.', 'Keep existing-trajectory barrier halfspace/integrating-factor results distinct from existence; obtain a fresh full-source and entire-exercise review before completion.'],
         'source_qualification': {'new_wording_proposal_supplied': False, 'current_exercise_text_sha256': exercises['barriers.html::exercise-16']['text_sha256']},
         'scope_limits': ['A radius/increment estimate or a particular sign-inclusion witness does not establish universal finite-dimensional existence.', 'The original14 peer/compiler receipts remain historical; no additional14 theorem count is available by reinstalling it.']},
    ]
    exclusions = []
    for family, source_field in (('Integral39', 'new_source'), ('Convolution13', 'entire_source'), ('StaticRegret20', 'source'), ('Polygonal14', 'source')):
        source = peers[family][source_field]
        matches = [name for name, row in selection['proof_files'].items() if row['sha256'] == source['sha256']]
        assert len(matches) == 1, family
        exclusions.append({'family': family, 'existing_packet': ref(ROOT / paths[family]),
            'actual_selected_canonical': {'file': matches[0], 'sha256': source['sha256']},
            'reason': 'Already selected; historical packet pending-installation/selection flags are not current-state flags. Preserve them, do not reinstall old owner candidates or recount the source.'})
    for family in readiness['sources']:
        assert family['canonical_source_ref']['sha256'] in selected_hashes
        exclusions.append({'family': family['family'], 'actual_selected_canonical': family['canonical_source_ref'],
                           'reason': 'Consumed by checkpoint33 exact seven-source integration.'})
    report = {'schema_version': 1,
        'status': 'checked_read_only_installed_Source88_owner33_unselected_continuation_index_no_new_math',
        'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'errors': [],
        'current_inventory': ref(inventory_path), 'current_owner_refs': owner_refs,
        'current_selected33': ref(selection_path), 'selection_original_status': selection['status'],
        'selected33_proof_count': selection['proof_file_count'],
        'selected33_aggregate_or_kernel_completion_inferred_by_index': False,
        'installed_owner33': ref(ROOT / 'reports/full-coverage/owner33-integration-v1.json'),
        'independent_live_installation_check': ref(OUT / 'independent-live-owner33-installed-bytes-check-v1.json'),
        'historical_remaining32_index': ref(original_remaining_path),
        'historical_next_batch32_index_not_current_state': ref(ROOT / 'book/coverage/checks/recovery32/next-batch-source-qualification-index-v1.json'),
        'current_unfinished20_exercises_and_original_pending_claims': current_unfinished,
        'next_tasks': tasks,
        'ready_unselected_families': [{'family': family, 'source': sources[family],
            'public_names': len(names[family]), 'zero_selected33_public_name_overlap': True}
            for family in ('IQC21', 'NN65', 'Conditional28')],
        'NN26_prefix_overlap': {'subset_of_NN65': True, 'shared_public_name_count': len(names['NN26']),
            'separate_extra_source_count_if_full65_selected': 0},
        'consumed_or_already_selected_exclusions': exclusions,
        'bound_current_sources': {name: ref(ROOT / name) for name in ('SafeLearning/nn-in-the-loop.html', 'SafeLearning/primer-probability.html', 'SafeLearning/barriers.html')},
        'instructions_for_next_agent': ['Start with the exact current owner33/Source88 hashes and selection33; historical Source81 inventories/owner30/31 templates are read-only provenance.', 'Prefer IQC21 and NN65 to reduce incomplete exercises; Conditional28 is an independent material batch that can run in parallel.', 'Create a fresh current compiler context; old0396/Source81 guards are invalid after owner33 changes. Preserve all prior failures, genuine native commands/raw logs/source snapshots and measured times.', 'Use exact reviewed replacements and current full29 parser evidence; maintain all established claims and pending unrelated clauses. Compose NN14.3 and IQC14.6 carefully because they share the same page.', 'Independent full math, narrow qualification, canonical paired readiness, exact owner mapping, selected aggregate/kernel/axiom audit and delivery evidence are distinct requirements; do not infer any from proof count.', 'Do not bulk-copy old snapshots, build caches, remote full papers or peer trees. Reuse bounded exact physical Root references and retain the full-coverage objective.'],
        'new_Lean_or_parser_or_owner_or_source_application_performed': False,
        'coverage_complete': False}
    destination.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'index': ref(destination), 'next_tasks': len(tasks), 'remaining_exercises': len(current_unfinished)}))


if __name__ == '__main__':
    main()

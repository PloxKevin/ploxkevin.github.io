"""Prepare exact Conditional28 bytes as an unselected future34 proof source.

Record two genuine canonical compiler commands. Existing current387 remains
pending; exact qualification, fresh parser/composition, owner correspondence,
selection, kernel/axiom audit and delivery are distinct future actions.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, re, subprocess, sys, time

sys.dont_write_bytecode = True
BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3]
INDEX = 'book/coverage/checks/checkpoint33-review/next-unselected-work-index-v1.json'
CANONICAL = 'verification/lean/SafeLearning/CompleteAppliedConditionalExpectationMSEDensityWhole34.lean'
SOURCE_SHA = 'a17a13e4b8ab97a3d020061b923eb5cdf15d115d30654ddf12a968fb0c53aba6'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def path(n):
    p = Path(n)
    assert not p.is_absolute() and '..' not in p.parts and p.as_posix() == n
    p = ROOT / p
    assert not p.is_symlink() and p.resolve().is_relative_to(ROOT)
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(ROOT))
    return p

def ref(p):
    p = path(p) if isinstance(p, str) else p
    return {'file': str(p.relative_to(ROOT)), 'sha256': sha(p), 'bytes': p.stat().st_size}

def exact(r):
    p = path(r['file'])
    assert p.is_file() and sha(p) == r['sha256'], r['file']
    if 'bytes' in r:
        assert p.stat().st_size == r['bytes'], r['file']
    return p

def read(r):
    return json.loads(exact(r).read_bytes())

def new(p, data):
    assert not p.exists(), str(p)
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as out:
        out.write(data)
    p.chmod(0o444)

def write(p, data):
    new(p, (json.dumps(data, indent=2) + '\n').encode())

def main():
    helper = ref(Path(__file__))
    index_ref = ref(INDEX)
    index = read(index_ref)
    task = next(r for r in index['next_tasks'] if r['priority'] == 3)
    assert task['id'] == 'apply_Conditional28_node387_exact_domain_qualifiers'
    assert task['source']['sha256'] == SOURCE_SHA
    assert task['public_theorems'] == 28 and task['public_names'] == 29
    original = exact(task['source'])
    full = read(task['packet'])
    narrow = read(task['narrow_peer'])
    request = read(task['author_request'])
    proposal = read(task['proposal'])
    assert full['status'] == 'passed_full_independent_conditional28_components_current387_gaps_prospective387_whole_review'
    assert full['errors'] == narrow['errors'] == []
    assert full['entire_source']['sha256'] == SOURCE_SHA
    assert narrow['supporting_full28_math_review']['sha256'] == SOURCE_SHA
    assert full['current_whole_decision']['approved'] is False
    assert full['prospective_whole_decision']['approved'] is True
    assert full['prospective_whole_decision']['conditional_on_exact_later_source_application'] is True
    assert full['prospective_whole_decision']['remaining_gaps'] == []
    replacements = task['source_qualification']['exact_replacements']
    assert len(replacements) == 2 and replacements == narrow['exact_two_replacements'] == proposal['exact_replacements']
    assert narrow['exact_full29_changed_keys'] == {'exercises': [], 'material_source_units': ['primer-probability.html::node-387']}
    assert narrow['all_other28_pages_and_all_other_literal_records_unchanged'] is True
    assert narrow['source_ordinal_reserved_or_applied'] is False
    names_ref = ref('book/coverage/lean_names.py')
    spec = importlib.util.spec_from_file_location('conditional34_names', exact(names_ref))
    names = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(names)
    def public(text):
        # The unchanged existing index omits noncomputable def lines. Normalize
        # only an in-memory read for the additional full-name collision guard.
        text = re.sub(r'(?m)^(\s*)noncomputable\s+(def|abbrev|instance)\s+', r'\1\2 ', text)
        return names.declarations(text)
    text = original.read_text()
    indexed = names.declarations(text)
    all_public = public(text)
    assert len(indexed) == 29 and sum(d['kind'] in {'theorem', 'lemma'} for d in indexed) == 28
    assert len(all_public) == 33 and sum(d['kind'] in {'theorem', 'lemma'} for d in all_public) == 28
    assert all(d['name'].startswith('SafeLearning.CompleteAppliedConditionalExpectationMaterial31.') for d in all_public)
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b', names.without_comments(text))
    theorem_names = {d['name'] for d in indexed if d['kind'] in {'theorem', 'lemma'}}
    assessments = full['all28_complete_public_body_assessments']
    assert {r['declaration'] for r in assessments} == theorem_names and len(assessments) == 28
    assert all(r['entire_body_and_actual_all_input_predicates_read'] and r['independently_approved_exact_component'] for r in assessments)
    selected_ref = index['current_selected33']
    selection = read(selected_ref)
    selected = {n: r['sha256'] for n, r in selection['proof_files'].items()}
    assert len(selected) == 1261
    manifest_ref = ref('reports/full-coverage/checkpoint-33-manifest.json')
    manifest = read(manifest_ref)
    audited = manifest['successful_verification']
    audit_ref = {'file': audited['report'], 'sha256': audited['report_sha256']}
    audit = read(audit_ref)
    assert audit['status'] == 'passed' and audit['proof_file_count'] == 1261 and audit['theorem_count'] == 11345
    assert audit['proof_sha256'] == selected and len(audit['source_sha256']) == 31
    protected = {**audit['source_sha256'], selected_ref['file']: selected_ref['sha256'],
                 manifest_ref['file']: manifest_ref['sha256'], audit_ref['file']: audit_ref['sha256'],
                 index_ref['file']: index_ref['sha256'], names_ref['file']: names_ref['sha256'],
                 helper['file']: helper['sha256']}
    for r in [index['current_inventory'], *index['current_owner_refs'].values()]:
        exact(r)
        protected[r['file']] = r['sha256']
    for n in ['verification/lean/SafeLearning.lean', 'verification/lean/AxiomAudit.lean',
              'verification/lean/lean-toolchain', 'verification/lean/lakefile.toml',
              'verification/lean/lake-manifest.json', 'verification/lean/verify.py',
              'book/coverage/material-corrections.json', 'book/coverage/applied-promotions.json']:
        protected[n] = sha(path(n))
    other_families = [r for r in index['ready_unselected_families'] if r['family'] in {'IQC21', 'NN65'}]
    assert len(other_families) == 2
    occupied = set()
    for n, h in selected.items():
        p = exact({'file': n, 'sha256': h})
        occupied.update(d['name'] for d in public(p.read_text()))
    for family in other_families:
        p = exact(family['source'])
        occupied.update(d['name'] for d in public(p.read_text()))
        protected[family['source']['file']] = family['source']['sha256']
    new_names = {d['name'] for d in all_public}
    assert not occupied.intersection(new_names)
    current = read(index['current_owner_refs']['applied'])
    pending = [(i, r) for i, r in enumerate(current['material_claims']) if 'primer-probability.html::node-387' in r.get('source_unit_keys', [])]
    assert len(pending) == 1
    pending_i, pending_row = pending[0]
    assert pending_row['status'] == 'pending' and pending_row['remaining_gaps']
    assert pending_row['text_sha256'] == full['current_whole_decision']['entire_current_literal']['text_sha256']
    assert pending_row['source_sha256'] == task['source_qualification']['current_page_sha256']
    assert audit['source_sha256']['SafeLearning/primer-probability.html'] == task['source_qualification']['current_page_sha256']
    page = path('SafeLearning/primer-probability.html').read_text()
    assert all(page.count(r['before']) == 1 and page.count(r['after']) == 0 for r in replacements)
    originals = {}
    for r in [task['source'], task['packet'], task['narrow_peer'], task['author_request'], task['proposal']]:
        exact(r)
        originals[r['file']] = r['sha256']
    for document in [full, narrow, request]:
        for n, h in document['required_evidence_artifacts_sha256'].items():
            exact({'file': n, 'sha256': h})
            originals[n] = h
    histories = full['all_original_eight_genuine_compiler_histories']
    assert len(histories) == 8
    assert [r['actual_exit_code'] for r in histories] == [1, 0, 1, 1, 1, 0, 1, 0]
    axiom = full['actual_original_all28_axiom_native']
    assert axiom['actual_exit_code'] == 0
    for history in histories + [axiom]:
        native = read(history['native'])
        assert native['actual_exit_code'] == history['actual_exit_code']
        assert native['source_sha256_before'] == native['source_sha256_after'] == history['source']['sha256'] == history['source_snapshot']['sha256']
        assert native['raw_log_sha256'] == history['raw_log']['sha256']
        assert all(native[k] == v for k, v in history['original_body_times'].items())
        for k in ['native', 'source', 'source_snapshot', 'raw_log']:
            r = history[k]
            exact(r)
            originals[r['file']] = r['sha256']
    assert histories[-1]['source']['sha256'] == SOURCE_SHA
    assert set(full['actual_standard_axioms_per_declaration']) == theorem_names
    assert all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in full['actual_standard_axioms_per_declaration'].values())
    assert not path(CANONICAL).exists()
    snapshot = BASE / 'source-snapshots' / Path(CANONICAL).name
    def guard():
        for n, h in {**selected, **protected, **originals}.items():
            assert sha(path(n)) == h, n
        for p in (ROOT / 'verification/lean/SafeLearning').glob('*34.lean'):
            if p.name != Path(CANONICAL).name:
                assert not new_names.intersection(d['name'] for d in public(p.read_text())), str(p)
        if path(CANONICAL).exists():
            assert sha(path(CANONICAL)) == SOURCE_SHA and sha(snapshot) == SOURCE_SHA
    guard()
    context = {'status': 'current_Source88_owner33_exact_Conditional28_future34_compiler_context',
               'created_at_utc': datetime.now(timezone.utc).isoformat(), 'continuation_index': index_ref,
               'baseline_selection': selected_ref, 'actual_passing_baseline_audit': audit_ref,
               'current_inventory': index['current_inventory'], 'current_four_owners': index['current_owner_refs'],
               'compiler_recorder': helper, 'protected_selected33_source_count': len(selected),
               'protected_current_inputs_sha256': protected, 'checked_original_evidence_sha256': originals,
               'original_genuine_compiler_histories': histories, 'original_all28_axiom_history': axiom,
               'current387_preserved_pending': {'owner': index['current_owner_refs']['applied'],
                  'JSON_pointer': ['material_claims', pending_i], 'id': pending_row['id'],
                  'text_sha256': pending_row['text_sha256'], 'status': pending_row['status']},
               'current_whole387_approved': False, 'source_qualifiers_applied': False,
               'original_indexed_public_name_count': 29, 'additional_noncomputable_public_names_guarded': 4,
               'total_actual_public_names_guarded': 33,
               'selected33_and_exact_forthcoming_IQC21_NN65_public_name_overlap': [],
               'source_or_owner_or_inventory_or_aggregate_or_PUB_or_progress_mutation': False,
               'coverage_complete': False}
    context_path = BASE / 'actual-current88-owner33-conditional34-context-v1.json'
    write(context_path, context)
    new(path(CANONICAL), original.read_bytes())
    new(snapshot, original.read_bytes())
    pairs = []
    for kind in ['standalone', 'named']:
        guard()
        name = Path(CANONICAL).stem
        command = ['lake', 'env', 'lean', 'SafeLearning/' + name + '.lean'] if kind == 'standalone' else ['lake', 'build', 'SafeLearning.' + name]
        raw_log = BASE / (name + '-' + kind + '-actual-v1.log')
        receipt = BASE / (name + '-' + kind + '-actual-v1.json')
        before = sha(path(CANONICAL))
        started = datetime.now(timezone.utc).isoformat()
        tick = time.monotonic()
        with raw_log.open('xb') as raw:
            result = subprocess.run(command, cwd=ROOT / 'verification/lean', stdout=raw, stderr=subprocess.STDOUT, check=False)
        elapsed = time.monotonic() - tick
        finished = datetime.now(timezone.utc).isoformat()
        raw_log.chmod(0o444)
        record = {'status': 'passed' if result.returncode == 0 else 'failed', 'kind': kind,
                  'command': command, 'actual_command': command, 'actual_workdir': str(ROOT / 'verification/lean'),
                  'exit_code': result.returncode, 'actual_exit_code': result.returncode,
                  'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': elapsed,
                  'source': CANONICAL, 'source_sha256_before': before, 'source_sha256_after': sha(path(CANONICAL)),
                  'source_snapshot': ref(snapshot), 'raw_log': ref(raw_log),
                  'compiler_recorder': helper, 'compiler_recorder_sha256_after': sha(Path(__file__)),
                  'context': ref(context_path), 'coverage_complete': False}
        write(receipt, record)
        guard()
        assert result.returncode == 0, str(receipt)
        pairs.append({'kind': kind, 'source': ref(CANONICAL), 'actual_record': ref(receipt),
                      'raw_log': ref(raw_log), 'source_snapshot': ref(snapshot), 'actual_exit_code': result.returncode})
        print(json.dumps({'family': 'Conditional28', 'kind': kind, 'actual_exit_code': result.returncode}), flush=True)
    guard()
    readiness = {'status': 'passed_actual_reviewed_Conditional28_canonical34_paired_checks_future_unselected',
                 'errors': [], 'completed_at_utc': datetime.now(timezone.utc).isoformat(),
                 'family': 'Conditional28', 'canonical_source': CANONICAL, 'canonical_source_ref': ref(CANONICAL),
                 'original_source': task['source'], 'original_namespaces': ['SafeLearning.CompleteAppliedConditionalExpectationMaterial31'],
                 'public_declarations': indexed, 'public_theorem_count': 28, 'public_name_count': 29,
                 'actual_public_declarations_including_noncomputable': all_public,
                 'all_actual_public_name_count': 33, 'declaration_parser': names_ref,
                 'actual_compiler_command_count': 2, 'actual_paired_records': pairs,
                 'independent_full_math_peer': task['packet'], 'independent_narrow_qualification_peer': task['narrow_peer'],
                 'original_author_request': task['author_request'], 'exact_proposal': task['proposal'],
                 'exact_reviewed_unapplied_replacements': replacements,
                 'current387_preserved_pending': context['current387_preserved_pending'],
                 'current_whole387_approved': False, 'prospective_whole387_peer_approved_conditional_on_exact_application': True,
                 'context': ref(context_path), 'source_qualifiers_applied': False,
                 'fresh_current_full29_parser_or_independent_composition_performed': False,
                 'remaining_requirements': [
                     'Apply exactly the two reviewed qualifiers against the current page and derive a byte-exact inverse.',
                     'Execute a fresh full29 parser and obtain exact current/prospective literal and independent composition evidence.',
                     'Rebase Applied active inventory/source identities and record independent exact whole387 owner correspondence.',
                     'Select new canonical bytes and run combined aggregate, kernel and standard-axiom audits, ledger checks and delivery evidence.',
                 ], 'scope_limits': task['scope_limits'], 'original_evidence_retained_by_exact_references': True,
                 'old_snapshot_tree_or_build_cache_or_original_source_tree_copied': False,
                 'selected_in33_or34': False, 'aggregate_kernel_fresh_axiom_owner_promotion_or_publication34_claimed': False,
                 'site_inventory_four_owners_selected33_proofs_and_main_aggregates_preserved': True,
                 'coverage_complete': False}
    target = BASE / 'actual-conditional28-canonical34-paired-readiness-v1.json'
    write(target, readiness)
    print(json.dumps({'status': readiness['status'], 'readiness': ref(target), 'theorems': 28,
                      'indexed_public_names': 29, 'all_actual_public_names_guarded': 33, 'actual_commands': 2,
                      'original_refs_checked': len(originals), 'current387_remains_pending': True}), flush=True)

if __name__ == '__main__':
    main()

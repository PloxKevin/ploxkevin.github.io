"""Select exactly eight independently reviewed additions to frozen checkpoint26.

Original selections, complete row data and historical executions remain intact.
The result still requires a fresh aggregate build, kernel and axiom audit.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, copy, hashlib, json, re
from lean_names import declarations
from retain_baseline_inputs27_v1 import retain, validate_evidence_aliases, normalized_baseline_evidence

ROOT = Path(__file__).resolve().parents[2]
BASELINE = 'reports/full-coverage/checkpoint-26-selection.json'
BASELINE_SHA = '12527ed93a283e1b37a491f7f799ac04e6217b1d7e20aee74116b312e580e23f'
MANIFEST = 'reports/full-coverage/checkpoint-26-manifest.json'
MANIFEST_SHA = 'ef777b585d9654e5dd784160dd4e9502eaae230d1f4fefcd9bdb2458c347f896'
AUDIT = 'reports/full-coverage/lean-checkpoint-26/verification-original.json'
AUDIT_SHA = '41e872c24a3c0e33e1e284d5247353815984df529ecd479041a8ed3eca0d206e'
INVENTORY = 'book/coverage/inventory-after-correction55.json'
INVENTORY_SHA = '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
DESTINATION = 'reports/full-coverage/checkpoint-27-selection.json'
CONTENT_MAP = 'book/coverage/checks/frozen26-input-content-bindings27-v1.json'
PAIRS = 'book/coverage/checks/future27-core/eight-source141-canonical-v1/eight-source141-actual-canonical-paired-readiness27-v1.json'
PAIRS_SHA = '74f6e5413cb390698e6090b798d6f0eed0b667082bd24681f7b2e82c49deef1f'

def safe(name):
    assert isinstance(name, str) and name
    p = Path(name)
    assert not p.is_absolute() and '..' not in p.parts and p.as_posix() == name
    p = ROOT / p
    assert p.resolve().is_relative_to(ROOT)
    return p

def sha(name): return hashlib.sha256(safe(name).read_bytes()).hexdigest()
def read(name): return json.loads(safe(name).read_bytes())
def checked(ref):
    assert set(ref) == {'file', 'sha256'} and re.fullmatch('[0-9a-f]{64}', ref['sha256'])
    assert sha(ref['file']) == ref['sha256'], ref['file']
    return read(ref['file'])
def exact(mapping):
    for n, h in mapping.items():
        assert isinstance(h, str) and re.fullmatch('[0-9a-f]{64}', h)
        assert sha(n) == h, n
def zero(d):
    values = [d[k] for k in ('actual_exit_code', 'exit_code') if k in d]
    assert values and all(type(v) is int and v == 0 for v in values)
def canonical_row_sha(row):
    return hashlib.sha256(json.dumps(row, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()).hexdigest()

def prepare(plan_name, apply=False):
    plan = read(plan_name)
    assert plan['status'] == 'independently_reviewed_installed_current55_owner27_selection_plan'
    assert not safe(DESTINATION).exists() and not safe(CONTENT_MAP).exists()
    assert plan['destination'] == DESTINATION and plan['content_map'] == CONTENT_MAP
    exact(plan['helpers_sha256'])
    assert plan['helpers_sha256'][Path(__file__).relative_to(ROOT).as_posix()] == sha(Path(__file__).relative_to(ROOT).as_posix())
    assert 'book/coverage/retain_baseline_inputs27_v1.py' in plan['helpers_sha256']
    code_peer = checked(plan['independent_selection_helper_review'])
    assert code_peer['status'] == plan['expected_selection_helper_review_status'] and code_peer['errors'] == []
    assert code_peer['helper'] == {'file': Path(__file__).relative_to(ROOT).as_posix(), 'sha256': sha(Path(__file__).relative_to(ROOT).as_posix())}
    assert plan['inventory'] == {'file': INVENTORY, 'sha256': INVENTORY_SHA}
    checked(plan['inventory'])
    assert sha('book/coverage/inventory.json') == INVENTORY_SHA
    baseline = checked(plan['baseline_selection'])
    manifest = checked(plan['baseline_manifest'])
    audit = checked(plan['baseline_audit'])
    assert plan['baseline_selection'] == {'file': BASELINE, 'sha256': BASELINE_SHA}
    assert plan['baseline_manifest'] == {'file': MANIFEST, 'sha256': MANIFEST_SHA}
    assert plan['baseline_audit'] == {'file': AUDIT, 'sha256': AUDIT_SHA}
    assert len(baseline['proof_files']) == audit['proof_file_count'] == 1167
    assert audit['status'] == 'passed' and audit['theorem_count'] == 9503
    assert all(type(r['exit_code']) is int and r['exit_code'] == 0 for r in audit['checks'])
    assert audit['proof_sha256'] == {n: r['sha256'] for n, r in baseline['proof_files'].items()}
    assert manifest['status'] == 'formal_verification_passed_partial_coverage'
    assert len(manifest['frozen_inputs_sha256']) == 47277
    assert manifest['selection'] == BASELINE and manifest['selection_sha256'] == BASELINE_SHA
    integration = checked(plan['integration_result'])
    execution = checked(plan['actual_integration_execution']); zero(execution)
    assert integration['status'] == 'four_exact_reviewed_owner27_candidate_bytes_integrated_pending_fresh_current55_global_integrity_and_aggregate27_audit'
    assert integration['applied'] is True and integration['inventory_sha256'] == INVENTORY_SHA
    binding_ref = {'file': integration['binding_manifest'], 'sha256': integration['binding_manifest_sha256']}
    binding = checked(binding_ref)
    assert execution['actual_command'] == ['python3', integration['actual_helper']['file'], binding_ref['file'], '--apply']
    assert execution['actual_workdir'] == str(ROOT)
    assert execution['helper_sha256_before'] == execution['helper_sha256_after']
    assert execution['helper_sha256_after'][integration['actual_helper']['file']] == integration['actual_helper']['sha256']
    exact(execution['helper_sha256_after']); assert sha(execution['log']) == execution['log_sha256']
    replacements = {r['destination']: r for r in integration['exact_replacements']}
    assert set(replacements) == {'book/coverage/' + n + '.json' for n in ['core', 'foundations', 'applied', 'modules', 'applied-promotions']}
    for name, row in replacements.items():
        checked(row['candidate']); assert sha(name) == row['candidate']['sha256']
        assert sha(row['original26_byte_copy']) == row['before_sha256']
    authorization = plan['authorized_baseline_evidence_aliases']
    assert authorization['integration_result'] == plan['integration_result']
    assert authorization['actual_integration_execution'] == plan['actual_integration_execution']
    aliases = validate_evidence_aliases(ROOT, BASELINE, MANIFEST, authorization)
    selected = copy.deepcopy(baseline['proof_files'])
    for source, row in selected.items():
        assert sha(source) == row['sha256']
        original = copy.deepcopy(row)
        normalized, used = normalized_baseline_evidence(original, aliases)
        if used:
            assert 'checkpoint27_original_baseline_evidence' not in row
            row['evidence_sha256'] = normalized
            row['checkpoint27_original_baseline_evidence'] = {
                'original_baseline_selection': {'file': BASELINE, 'sha256': BASELINE_SHA},
                'original_baseline_source': source,
                'original_row_canonical_json_sha256': canonical_row_sha(original),
                'authorized_original_path_aliases': used}
        exact(row['evidence_sha256'])
    pairs = checked(plan['actual_canonical_readiness'])
    assert plan['actual_canonical_readiness'] == {'file': PAIRS, 'sha256': PAIRS_SHA}
    assert pairs['errors'] == [] and pairs['source_count'] == 8 and pairs['public_theorem_count'] == 141
    assert pairs['actual_compiler_command_count'] == len(pairs['actual_paired_records']) == 16
    expected = {r['canonical_source']: r['source']['sha256'] for r in pairs['sources']}
    assert len(expected) == 8 and not set(expected).intersection(selected)
    offers, peers, seen = {}, {}, set()
    first = selected[sorted(selected)[0]]
    for owner, row in binding['owners'].items():
        dest = 'book/coverage/' + owner + '.json'
        assert row['destination'] == dest and replacements[dest]['candidate'] == row['candidate']
        offer = checked(row['reviewed_offer']); peer = checked(row['final_mapping_peer'])
        assert peer['status'] == row['expected_final_mapping_peer_status'] and peer['errors'] == []
        assert offer.get('inventory_sha256', offer.get('current_inventory_sha256')) == INVENTORY_SHA
        exact(offer['source_sha256'])
        offers[row['reviewed_offer']['file']] = row['reviewed_offer']['sha256']; peers[owner] = row['final_mapping_peer']
        proofs = offer['proof_files']; assert set(proofs) == set(row['new_sources'])
        for source, proof in proofs.items():
            assert source in expected and source not in seen and proof['sha256'] == expected[source]
            exact(proof['evidence_sha256']); seen.add(source)
            source_pairs = [p for p in pairs['actual_paired_records'] if p['source']['file'] == source]
            assert len(source_pairs) == 2 and {p['kind'] for p in source_pairs} == {'standalone', 'named'}
            for p in source_pairs:
                native = checked(p['actual_record']); zero(native)
                assert native['source'] == source and native['source_sha256_before'] == native['source_sha256_after'] == expected[source]
                command = ['lake', 'env', 'lean', 'SafeLearning/' + Path(source).name] if p['kind'] == 'standalone' else ['lake', 'build', 'SafeLearning.' + Path(source).stem]
                assert native['command'] == command and native['actual_workdir'] == str(ROOT / 'verification/lean')
                assert p['raw_log'] == {'file': native['log'], 'sha256': native['log_sha256']}
                assert sha(p['raw_log']['file']) == p['raw_log']['sha256']
                assert p['source_snapshot']['sha256'] == expected[source] == sha(p['source_snapshot']['file'])
                assert proof['evidence_sha256'][p['actual_record']['file']] == p['actual_record']['sha256']
                assert proof['evidence_sha256'][p['raw_log']['file']] == p['raw_log']['sha256']
            selected[source] = copy.deepcopy(proof)
            selected[source]['original_actual_zero_record'] = next(p['actual_record']['file'] for p in source_pairs if p['kind'] == 'standalone')
        for ref in [row['reviewed_offer'], row['final_mapping_peer'], row['actual_finalizer'], row['candidate']]:
            first['evidence_sha256'][ref['file']] = ref['sha256']
    assert seen == set(expected) and len(selected) == 1175
    new_names = [d['name'] for n in expected for d in declarations(safe(n).read_text()) if d['kind'] in {'theorem', 'lemma'}]
    assert len(new_names) == len(set(new_names)) == 141
    all_names = [d['name'] for n in selected for d in declarations(safe(n).read_text())]
    assert len(all_names) == len(set(all_names))
    theorem_names = [d['name'] for n in selected for d in declarations(safe(n).read_text()) if d['kind'] in {'theorem', 'lemma'}]
    assert len(theorem_names) == len(set(theorem_names)) == 9644
    for owner in binding['owners']:
        ledger = read('book/coverage/' + owner + '.json')
        for claim in ledger['material_claims'] + [c for e in ledger['exercises'] for c in e['claims']]:
            assert set(claim['lean_declarations']) <= set(all_names), (owner, claim['id'])
    for n in selected:
        for line in re.findall(r'^import[^\n]*', safe(n).read_text(), re.M):
            for dependency in line.split()[1:]:
                if dependency.startswith('SafeLearning.'):
                    assert 'verification/lean/' + dependency.replace('.', '/') + '.lean' in selected
    global_audit = checked(plan['global_integrity'])
    assert global_audit['integrity_status'] == 'passed' and global_audit['errors'] == []
    assert global_audit['inventory_sha256'] == INVENTORY_SHA and global_audit['mathematical_coverage_complete'] is False
    assert {r['domain'] for r in global_audit['domains']} == set(binding['owners'])
    for r in global_audit['domains']:
        assert r['ledger_sha256'] == replacements['book/coverage/' + r['domain'] + '.json']['candidate']['sha256']
    extras = copy.deepcopy(baseline['extra_frozen_inputs'])
    for n, row in extras.items(): assert sha(n) == row['sha256']
    for n, row in plan['additional_frozen_inputs'].items():
        assert set(row) == {'sha256', 'scope'} and row['scope'] == 'immutable_audit_or_local_source_evidence'
        assert any(safe(n).resolve().is_relative_to((ROOT / base).resolve()) for base in ['book/coverage', 'reports/full-coverage/source-history'])
        assert sha(n) == row['sha256'] and row['sha256'] not in set(plan['excluded_full_external_reference_sha256'])
        assert n not in extras or extras[n] == row; extras[n] = row
    for ref in [plan['global_integrity'], plan['integration_result'], plan['actual_integration_execution'], binding_ref, plan['actual_canonical_readiness'], plan['independent_selection_helper_review']]:
        first['evidence_sha256'][ref['file']] = ref['sha256']
    first['evidence_sha256'][plan_name] = sha(plan_name)
    first['evidence_sha256'].update(plan['helpers_sha256'])
    if not apply:
        return {'status': 'passed_selection_preflight_no_writes', 'proofs': 1175, 'new_sources': 8, 'new_public_declarations': 141, 'owners': 5, 'coverage_complete': False}
    provenance = retain(ROOT, BASELINE, MANIFEST, selected, extras, CONTENT_MAP, authorization)
    result = dict(status='explicit_current55_source_matched_selection_requires_fresh_aggregate_audit', created_at_utc=datetime.now(timezone.utc).isoformat(), baseline_selection=BASELINE, baseline_selection_sha256=BASELINE_SHA, actual_passing_baseline_audit=AUDIT, actual_passing_baseline_audit_sha256=AUDIT_SHA, current_inventory=INVENTORY, current_inventory_sha256=INVENTORY_SHA, offers_sha256=offers, independent_owner_mapping_peers=peers, global_integrity=plan['global_integrity']['file'], global_integrity_sha256=plan['global_integrity']['sha256'], proof_files=dict(sorted(selected.items())), proof_file_count=1175, new_file_count=8, extra_frozen_inputs=extras, previous_frozen_input_content_binding=provenance, selection_plan=plan_name, selection_plan_sha256=sha(plan_name), deliberate_baseline_source_revisions={}, coverage_complete=False, limits=['All1167 baseline26 proof sources and full original selection row data remain exact. Eight reviewed additions require a fresh frozen27 aggregate build, kernel replay and all9644-declaration axiom audit.', 'Every47277 frozen26 original path and byte hash is retained by exact content bindings. Historical commands, results, logs and times remain historical.', 'Whole MPC replanning certificate and all other open exercises and material remain pending.'])
    with safe(DESTINATION).open('x') as f: f.write(json.dumps(result, ensure_ascii=False, separators=(',', ':')) + '\n')
    assert safe(DESTINATION).stat().st_size < 100_000_000
    return {'proofs': 1175, 'new': 8, 'selection_sha256': sha(DESTINATION), 'content_map': provenance}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--plan', required=True); parser.add_argument('--apply', action='store_true')
    args = parser.parse_args(); print(json.dumps(prepare(args.plan, args.apply)))

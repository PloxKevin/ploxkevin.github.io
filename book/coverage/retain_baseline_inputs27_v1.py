"""Retain all frozen26 bytes and authorize only five exact historical aliases.

Four old owner-ledger references require genuine Root27 installation records;
the old Lyapunov source requires genuine source54/55 application records. Every
other evidence reference remains exact. Original full rows are retrieved through
the immutable baseline selection and a deterministic full-row fingerprint,
preserving existing row fields, bodies, times and older embedded provenance.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

BASELINE = 'reports/full-coverage/checkpoint-26-selection.json'
BASELINE_SHA = '12527ed93a283e1b37a491f7f799ac04e6217b1d7e20aee74116b312e580e23f'
MANIFEST = 'reports/full-coverage/checkpoint-26-manifest.json'
MANIFEST_SHA = 'ef777b585d9654e5dd784160dd4e9502eaae230d1f4fefcd9bdb2458c347f896'
AUDIT = 'reports/full-coverage/lean-checkpoint-26/verification-original.json'
AUDIT_SHA = '41e872c24a3c0e33e1e284d5247353815984df529ecd479041a8ed3eca0d206e'
OWNER_EVIDENCE_PATHS = {'book/coverage/' + owner + '.json' for owner in
                        ('core', 'foundations', 'applied', 'modules')}
SOURCE = 'SafeLearning/lyapunov-mpc.html'
SOURCE_OLD_SHA = '5e21c5319d41968468781ee0bf9b18aec5147666f764827f3a96e9e73d0138af'
SOURCE_NEW_SHA = '63a1ac8be7f5cf8b490dd1dd872d416affee95f6de0d5ba3c1c618f4b86cd79f'
SOURCE_ARCHIVE = 'reports/full-coverage/source-history/approved-mpc-conformal-corrections54-55-20261011/source53-original-root/' + SOURCE
APPLICATION = {'file': 'reports/full-coverage/source54-55-corrections-application-v1.json',
               'sha256': '845937be3efd0d3bb88518fe9597b4bf6f22ead237cd1292a28ad5b16265c528'}
APPLICATION_EXECUTION = {'file': 'reports/full-coverage/source54-55-corrections-application-execution-v1.json',
                         'sha256': 'a255862de464e0f1acf284807c4a48b732bc69055cf71b445ea2df5920494805'}
INTEGRATION_HELPER = 'book/coverage/checks/root_integrate_owner27_candidates_v2.py'
ALIAS_PATHS = OWNER_EVIDENCE_PATHS | {SOURCE}

def canonical_row_sha256(row):
    return hashlib.sha256(json.dumps(row, sort_keys=True, separators=(',', ':'),
                                    ensure_ascii=False).encode()).hexdigest()

def _access(root):
    root = Path(root)
    def safe(name):
        assert isinstance(name, str) and name
        path = Path(name)
        assert not path.is_absolute() and '..' not in path.parts and str(path) == name
        result = root / path
        assert result.resolve().is_relative_to(root.resolve()), name
        assert not result.is_symlink(), name
        return result
    def sha(name): return hashlib.sha256(safe(name).read_bytes()).hexdigest()
    def verify(ref):
        assert isinstance(ref, dict) and set(ref) == {'file', 'sha256'}
        assert isinstance(ref['sha256'], str) and re.fullmatch('[0-9a-f]{64}', ref['sha256'])
        path = safe(ref['file']); assert path.is_file() and sha(ref['file']) == ref['sha256'], ref['file']
        return path
    def checked(ref): return json.loads(verify(ref).read_bytes())
    return safe, sha, verify, checked

def _zero(record):
    codes = [record[k] for k in ('actual_exit_code', 'exit_code') if k in record]
    assert codes and all(type(code) is int and code == 0 for code in codes)

def _command(record):
    commands = [record[k] for k in ('actual_command', 'command') if k in record]
    assert commands and all(isinstance(c, list) and c == commands[0] for c in commands)
    return commands[0]

def _execution(root, record, expected_command, helper, safe, sha):
    _zero(record)
    command = _command(record)
    assert command in expected_command
    assert Path(record['actual_workdir']).resolve() == Path(root).resolve()
    assert record['helper_sha256_before'] == record['helper_sha256_after']
    helpers = record['helper_sha256_after']; assert isinstance(helpers, dict)
    assert helpers[helper['file']] == helper['sha256'] == sha(helper['file'])
    for name, digest in helpers.items(): assert sha(name) == digest, name
    assert sha(record['log']) == record['log_sha256']

def validate_evidence_aliases(root, baseline_name, manifest_name, authorization):
    safe, sha, verify, checked = _access(root)
    assert baseline_name == BASELINE and sha(baseline_name) == BASELINE_SHA
    assert manifest_name == MANIFEST and sha(manifest_name) == MANIFEST_SHA
    baseline = json.loads(safe(baseline_name).read_bytes())
    manifest = json.loads(safe(manifest_name).read_bytes())
    assert manifest['selection'] == baseline_name and manifest['selection_sha256'] == BASELINE_SHA
    assert manifest['proof_files'] == baseline['proof_files'] and len(baseline['proof_files']) == 1167
    assert len(manifest['frozen_inputs_sha256']) == 47277
    assert set(authorization) == {'actual_integration_execution', 'integration_result',
                                  'source_application', 'actual_source_application_execution', 'aliases'}
    assert set(authorization['aliases']) == ALIAS_PATHS
    result = checked(authorization['integration_result'])
    execution = checked(authorization['actual_integration_execution'])
    assert result['status'] == 'four_exact_reviewed_owner27_candidate_bytes_integrated_pending_fresh_current55_global_integrity_and_aggregate27_audit'
    assert result['applied'] is True and result['coverage_complete'] is False
    assert result['protected_proof_source_count'] == 1175 and result['new_canonical_source_count'] == 8
    helper = result['actual_helper']; verify(helper)
    assert helper['file'] == INTEGRATION_HELPER
    binding_ref = {'file': result['binding_manifest'], 'sha256': result['binding_manifest_sha256']}
    binding = checked(binding_ref); assert binding['helper'] == helper
    expected = [['python3', helper_path, binding_path, '--apply']
                for helper_path in [helper['file'], str(safe(helper['file']))]
                for binding_path in [binding_ref['file'], str(safe(binding_ref['file']))]]
    _execution(root, execution, expected, helper, safe, sha)
    replacements = {row['destination']: row for row in result['exact_replacements']}
    assert len(result['exact_replacements']) == len(replacements) == 5
    assert set(replacements) == OWNER_EVIDENCE_PATHS | {'book/coverage/applied-promotions.json'}
    checked_aliases = {}
    for name in OWNER_EVIDENCE_PATHS:
        alias = authorization['aliases'][name]
        assert set(alias) == {'original_sha256', 'immutable_byte_copy'}
        old_sha = manifest['working_inputs_sha256'][name]
        assert alias['original_sha256'] == old_sha
        row = replacements[name]; assert row['before_sha256'] == old_sha
        archive = 'reports/full-coverage/owner26-originals-before-owner27-integration-v1/' + Path(name).name
        assert row['original26_byte_copy'] == archive
        assert alias['immutable_byte_copy'] == {'file': archive, 'sha256': old_sha}
        verify(alias['immutable_byte_copy']); verify(row['candidate'])
        assert sha(name) == row['candidate']['sha256']
        occurrences = [r for r in baseline['proof_files'].values() if name in r['evidence_sha256']]
        assert occurrences and all(r['evidence_sha256'][name] == old_sha for r in occurrences)
        checked_aliases[name] = alias
    # The source exception is derived from a separate actual write and its exact
    # before-write archive. It authorizes no other changed source or inventory.
    assert authorization['source_application'] == APPLICATION
    assert authorization['actual_source_application_execution'] == APPLICATION_EXECUTION
    application = checked(APPLICATION); source_execution = checked(APPLICATION_EXECUTION)
    assert application['status'] == 'passed_actual_source54_and_source55_corrections_full29_inventory_owner_identity_rebase_pending'
    assert application['coverage_complete'] is False and application['selected26_proof_sources_unchanged'] == 1167
    assert application['five_installed26_owner_ledgers_unchanged'] is True
    assert [r['correction_id'] for r in application['applications']] == [54, 55]
    source_helper = application['helper']; verify(source_helper)
    _execution(root, source_execution, [['python3', source_helper['file']],
                ['python3', str(safe(source_helper['file']))]], source_helper, safe, sha)
    history = checked(application['preserved_history'])
    assert history['status'] == 'exact_source53_and_owner26_original_bytes_preserved_before_source54_55'
    original = {'file': SOURCE_ARCHIVE, 'sha256': SOURCE_OLD_SHA}
    assert history['original_root_files'][SOURCE] == original
    alias = authorization['aliases'][SOURCE]
    assert alias == {'original_sha256': SOURCE_OLD_SHA, 'immutable_byte_copy': original}
    assert manifest['working_inputs_sha256'][SOURCE] == SOURCE_OLD_SHA
    assert application['applications'][0]['source_after'] == {'file': SOURCE, 'sha256': SOURCE_NEW_SHA}
    assert sha(SOURCE) == SOURCE_NEW_SHA; verify(original)
    occurrences = [r for r in baseline['proof_files'].values() if SOURCE in r['evidence_sha256']]
    assert occurrences and all(r['evidence_sha256'][SOURCE] == SOURCE_OLD_SHA for r in occurrences)
    checked_aliases[SOURCE] = alias
    return checked_aliases

def normalized_baseline_evidence(row, aliases):
    normalized = dict(row['evidence_sha256']); used = {}
    assert set(aliases) == ALIAS_PATHS
    for original, alias in aliases.items():
        if original not in normalized: continue
        assert normalized.pop(original) == alias['original_sha256']
        immutable = alias['immutable_byte_copy']
        assert immutable['file'] not in normalized or normalized[immutable['file']] == immutable['sha256']
        normalized[immutable['file']] = immutable['sha256']; used[original] = alias
    return normalized, used

def retain(root, baseline_name, manifest_name, selected, extras, destination_name, authorization):
    safe, sha, verify, checked = _access(root)
    for name in (baseline_name, manifest_name, destination_name): safe(name)
    baseline = json.loads(safe(baseline_name).read_bytes())
    manifest = json.loads(safe(manifest_name).read_bytes())
    assert baseline['status'].endswith('requires_fresh_aggregate_audit')
    assert manifest['status'] == 'formal_verification_passed_partial_coverage'
    assert manifest['selection'] == baseline_name and manifest['selection_sha256'] == sha(baseline_name)
    assert manifest['proof_files'] == baseline['proof_files']
    assert sha(AUDIT) == AUDIT_SHA
    audit = json.loads(safe(AUDIT).read_bytes()); assert audit['status'] == 'passed'
    assert audit['proof_file_count'] == 1167
    aliases = validate_evidence_aliases(root, baseline_name, manifest_name, authorization)
    actual_result = checked(authorization['integration_result'])
    current_sha256 = {r['destination']: r['candidate']['sha256'] for r in actual_result['exact_replacements']}
    current_sha256[SOURCE] = SOURCE_NEW_SHA
    assert set(baseline['proof_files']) <= set(selected)
    for name, row in baseline['proof_files'].items():
        assert selected[name]['sha256'] == row['sha256'], name
        normalized, used = normalized_baseline_evidence(row, aliases)
        assert all(selected[name]['evidence_sha256'].get(n) == h for n, h in normalized.items()), name
        for original, alias in used.items():
            if original in selected[name]['evidence_sha256']:
                h = selected[name]['evidence_sha256'][original]
                assert h != alias['original_sha256'] and h == current_sha256[original] == sha(original)
        for key, value in row.items():
            if key != 'evidence_sha256': assert selected[name][key] == value, (name, key)
        if used:
            assert selected[name]['checkpoint27_original_baseline_evidence'] == {
                'original_baseline_selection': {'file': baseline_name, 'sha256': sha(baseline_name)},
                'original_baseline_source': name,
                'original_row_canonical_json_sha256': canonical_row_sha256(row),
                'authorized_original_path_aliases': used}, name
    for name, row in baseline['extra_frozen_inputs'].items(): assert extras.get(name) == row, name
    assert safe(manifest['snapshot']).resolve().is_relative_to((Path(root) / 'reports/full-coverage').resolve())
    bound = {}
    def bind(name, digest):
        assert safe(name).is_file() and sha(name) == digest, name
        assert name not in bound or bound[name] == digest, name
        bound[name] = digest
    for name, row in selected.items():
        bind(name, row['sha256'])
        for n, h in row['evidence_sha256'].items(): bind(n, h)
    for name, row in extras.items(): bind(name, row['sha256'])
    by_digest = {}
    for name, digest in sorted(bound.items()): by_digest.setdefault(digest, name)
    first = selected[sorted(selected)[0]]; rows = []; added = {}; reused = 0
    for name, digest in sorted(manifest['frozen_inputs_sha256'].items()):
        safe(name); frozen = manifest['snapshot'] + '/' + name
        assert safe(frozen).resolve().is_relative_to(safe(manifest['snapshot']).resolve())
        assert sha(frozen) == digest, name
        retained = by_digest.get(digest)
        if retained is None:
            retained = frozen; bind(retained, digest); by_digest[digest] = retained
            first['evidence_sha256'][retained] = digest; added[retained] = digest
        else: reused += 1
        assert bound[retained] == digest and sha(retained) == digest
        rows.append({'original_frozen_path': name, 'sha256': digest, 'retained_input': retained})
    assert len(rows) == len(manifest['frozen_inputs_sha256']) == 47277
    assert {r['original_frozen_path']: r['sha256'] for r in rows} == manifest['frozen_inputs_sha256']
    for name in (baseline_name, manifest_name, AUDIT):
        bind(name, sha(name)); first['evidence_sha256'][name] = sha(name)
    destination = safe(destination_name); assert not destination.exists()
    result = {
        'status': 'all_original_frozen_inputs_retained_by_exact_content_fingerprints',
        'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'baseline_selection': baseline_name, 'baseline_selection_sha256': sha(baseline_name),
        'baseline_manifest': manifest_name, 'baseline_manifest_sha256': sha(manifest_name),
        'baseline_actual_audit': {'file': AUDIT, 'sha256': AUDIT_SHA},
        'original_snapshot': manifest['snapshot'], 'original_input_count': len(rows),
        'retained_existing_content_rows': reused, 'new_unique_snapshot_aliases': added,
        'new_unique_snapshot_alias_count': len(added),
        'new_unique_snapshot_alias_bytes': sum(safe(n).stat().st_size for n in added),
        'input_bindings': rows, 'authorized_baseline_evidence_aliases': authorization,
        'original_row_retrieval': 'Immutable baseline selection plus source key and deterministic sorted compact JSON full-row SHA; every prior row field/body/time remains exact.',
        'scope': 'Every frozen26 path/hash is retained by exact bytes. Only four genuine Root owner archives and the genuine source54 old Lyapunov archive normalize historical evidence; no new mathematical or execution claim.'}
    payload = (json.dumps(result, ensure_ascii=False, separators=(',', ':')) + '\n').encode()
    assert len(payload) < 100_000_000
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open('xb') as stream: stream.write(payload)
    first['evidence_sha256'][destination_name] = sha(destination_name)
    return {'file': destination_name, 'sha256': sha(destination_name),
            'original_inputs': len(rows), 'new_snapshot_aliases': len(added)}

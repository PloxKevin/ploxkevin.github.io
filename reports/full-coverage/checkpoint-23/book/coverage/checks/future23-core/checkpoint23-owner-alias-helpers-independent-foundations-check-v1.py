"""Independent code/isolated-fixture reader; never execute production prepare."""
from pathlib import Path
from datetime import datetime, timezone
import ast
import copy
import hashlib
import importlib.util
import json
import sys

ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = ROOT / 'book/coverage/checks/future23-core/checkpoint23-owner-alias-helpers-independent-foundations-review-v1.json'
FIXTURE = Path('/tmp/foundations-owner23-alias-retention-fixtures-v1')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
R = lambda p: json.loads(Path(p).read_text())
REF = lambda n: {'file': n, 'sha256': H(ROOT / n)}
assert not OUT.exists() and not FIXTURE.exists()
hashes = {
    'book/coverage/prepare_checkpoint23_selection_v3.py': '3d646ccd946674944edd86bf55b10c5d5a4ee3cda4a1e7498f41aae8af6f226d',
    'book/coverage/retain_baseline_inputs23_v3.py': '904341fa346e1e76cf6914b5660b978666bf0653664e75b1517e0400b9a25068',
    'book/coverage/checks/prepare_root_owner23_alias_plan_v3.py': 'd1688dbe882a4bb989f65293b8b7e232fcff106ba2afefcefb583c6eb2b1a243',
}
bodies = {}
for n, digest in hashes.items():
    assert H(ROOT / n) == digest, n
    bodies[n] = (ROOT / n).read_text()
    ast.parse(bodies[n])
baseline_name = 'reports/full-coverage/checkpoint-22-selection.json'
manifest_name = 'reports/full-coverage/checkpoint-22-manifest.json'
baseline, manifest = R(ROOT / baseline_name), R(ROOT / manifest_name)
old_plan_name = 'book/coverage/checks/future23-core/checkpoint23-installed-owner-selection-plan-v1.json'
old_plan = R(ROOT / old_plan_name)
assert H(ROOT / baseline_name) == '083fe75e535ebbd37326e34407d13b90357738ea7f4244eb1cfe5da8226f9ff9'
assert H(ROOT / manifest_name) == 'c8e4ce87ceceed0092e0593d4b6d5fed1340bc151af9aa2aaeb6e07f220413bb'
assert len(baseline['proof_files']) == 1113 and len(manifest['frozen_inputs_sha256']) == 34051
integration_ref = old_plan['owners']['modules']['integration_result']
execution_ref = old_plan['owners']['modules']['actual_builder']
integration = R(ROOT / integration_ref['file'])
execution = R(ROOT / execution_ref['file'])
assert H(ROOT / integration_ref['file']) == integration_ref['sha256']
assert H(ROOT / execution_ref['file']) == execution_ref['sha256']
assert execution['actual_exit_code'] == 0 and integration['applied'] is True
rows = {row['destination']: row for row in integration['exact_replacements']}
owners = {'book/coverage/' + owner + '.json' for owner in ['core', 'foundations', 'applied', 'modules']}
aliases = {n: {'original_sha256': manifest['working_inputs_sha256'][n], 'immutable_byte_copy': {'file': rows[n]['original22_byte_copy'], 'sha256': manifest['working_inputs_sha256'][n]}} for n in sorted(owners)}
authorization = {'actual_integration_execution': execution_ref, 'integration_result': integration_ref, 'aliases': aliases}
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('foundation_independent_retainer23_v3', ROOT / 'book/coverage/retain_baseline_inputs23_v3.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
# This is the genuine read-only validator against actual original Root inputs.
assert module.validate_owner_evidence_aliases(ROOT, baseline_name, manifest_name, authorization) == aliases
assert aliases['book/coverage/applied.json']['original_sha256'] == '0ee60f1f224d01f443a762e0427d4527d6bd9b1d3ae5ed1d893c67750e331d20'
assert manifest['frozen_inputs_sha256']['book/coverage/applied.json'] == '94615acc4869b7e2fdab15d55989b6af1059d506b1d9eac2c086d48ac0b947b8'
assert aliases['book/coverage/applied.json']['original_sha256'] != manifest['frozen_inputs_sha256']['book/coverage/applied.json']
stale = []
normalized_baseline = copy.deepcopy(baseline['proof_files'])
for source, original in baseline['proof_files'].items():
    assert H(ROOT / source) == original['sha256']
    normalized, used = module.normalized_baseline_owner_evidence(original, aliases)
    assert original == baseline['proof_files'][source]
    if used:
        normalized_baseline[source]['evidence_sha256'] = normalized
        normalized_baseline[source]['checkpoint23_original_baseline_owner_evidence'] = {
            'original_baseline_selection': REF(baseline_name), 'original_baseline_source': source,
            'original_row_body': copy.deepcopy(original), 'authorized_original_path_aliases': used,
        }
    for name, digest in original['evidence_sha256'].items():
        if H(ROOT / name) != digest:
            stale.append({'source': source, 'original_path': name, 'original_sha256': digest, 'current_sha256': H(ROOT / name)})
            assert name in aliases and digest == aliases[name]['original_sha256']
    for name, digest in normalized.items():
        assert H(ROOT / name) == digest
assert len(stale) == 4 and {r['original_path'] for r in stale} == owners

fixture_results = []


def reject_auth(label, mutator):
    candidate = copy.deepcopy(authorization)
    mutator(candidate)
    try:
        module.validate_owner_evidence_aliases(ROOT, baseline_name, manifest_name, candidate)
    except (AssertionError, KeyError, FileNotFoundError, ValueError):
        fixture_results.append({'fixture': label, 'expected': 'reject', 'observed': 'rejected'})
    else:
        raise AssertionError('Invalid authorization accepted: ' + label)


reject_auth('missing_one_of_exactly_four_paths', lambda d: d['aliases'].pop('book/coverage/core.json'))
reject_auth('unauthorized_fifth_path', lambda d: d['aliases'].update({'book/coverage/applied-promotions.json': copy.deepcopy(aliases['book/coverage/applied.json'])}))
reject_auth('wrong_old_digest', lambda d: d['aliases']['book/coverage/core.json'].update(original_sha256='0' * 64))
reject_auth('Applied_frozen_pruned_digest_cannot_replace_raw_working22', lambda d: d['aliases']['book/coverage/applied.json'].update(original_sha256=manifest['frozen_inputs_sha256']['book/coverage/applied.json']))
reject_auth('wrong_archive_copy_digest', lambda d: d['aliases']['book/coverage/core.json']['immutable_byte_copy'].update(sha256='0' * 64))
reject_auth('wrong_archive_copy_path_even_if_content_hash_known', lambda d: d['aliases']['book/coverage/core.json']['immutable_byte_copy'].update(file='reports/full-coverage/checkpoint-22/book/coverage/core.json'))
reject_auth('wrong_execution_record_hash', lambda d: d['actual_integration_execution'].update(sha256='0' * 64))
reject_auth('wrong_integration_result_hash', lambda d: d['integration_result'].update(sha256='0' * 64))
reject_auth('genuine_failed_execution_is_not_an_actual_zero_apply', lambda d: d.update(actual_integration_execution=REF('reports/full-coverage/prepare-checkpoint23-selection-execution-v1.json')))

# Synthetic minimal retention fixtures exercise the real retainer body. The
# actual Root authorization validator was checked above; replacing only that
# call avoids inventing synthetic actual-execution records. Every owner byte
# copied below is a real original/current body, and the frozen Applied body is
# its distinct real94615 hash. No production inputs are written.
FIXTURE.mkdir()


def put(name, data):
    path = FIXTURE / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def put_json(name, data):
    put(name, (json.dumps(data, indent=2) + '\n').encode())


source = 'verification/lean/SafeLearning/SyntheticRetentionFixture.lean'
ordinary = 'book/coverage/checks/synthetic-ordinary-evidence.txt'
put(source, b'-- Synthetic retention fixture only; no Lean execution is claimed.\n')
put(ordinary, b'Exact independent ordinary-evidence fixture.\n')
for name, alias in aliases.items():
    put(name, (ROOT / name).read_bytes())
    put(alias['immutable_byte_copy']['file'], (ROOT / alias['immutable_byte_copy']['file']).read_bytes())
put(integration_ref['file'], (ROOT / integration_ref['file']).read_bytes())
fixture_row = {'sha256': H(FIXTURE / source), 'evidence_sha256': {ordinary: H(FIXTURE / ordinary), **{n: a['original_sha256'] for n, a in aliases.items()}}, 'original_review_time': 'synthetic fixture metadata, not an execution time', 'original_semantic_body': {'scope': 'synthetic immutable baseline body'}}
fixture_baseline = {'status': 'synthetic_fixture_requires_fresh_aggregate_audit', 'proof_files': {source: fixture_row}, 'extra_frozen_inputs': {}}
put_json(baseline_name, fixture_baseline)
fixture_frozen = {source: H(FIXTURE / source), ordinary: H(FIXTURE / ordinary)}
snapshot = 'reports/full-coverage/checkpoint-22'
for n in fixture_frozen:
    put(snapshot + '/' + n, (FIXTURE / n).read_bytes())
for name in owners:
    original_frozen = ROOT / snapshot / name
    put(snapshot + '/' + name, original_frozen.read_bytes())
    fixture_frozen[name] = H(original_frozen)
fixture_manifest = {'status': 'formal_verification_passed_partial_coverage', 'selection': baseline_name, 'selection_sha256': H(FIXTURE / baseline_name), 'snapshot': snapshot, 'proof_files': fixture_baseline['proof_files'], 'frozen_inputs_sha256': fixture_frozen, 'working_inputs_sha256': manifest['working_inputs_sha256'], 'synthetic_fixture_only': True}
put_json(manifest_name, fixture_manifest)
normalized, used = module.normalized_baseline_owner_evidence(fixture_row, aliases)
fixture_selected_row = copy.deepcopy(fixture_row)
fixture_selected_row['evidence_sha256'] = {**normalized, **{n: rows[n]['candidate']['sha256'] for n in owners}}
fixture_selected_row['checkpoint23_original_baseline_owner_evidence'] = {'original_baseline_selection': {'file': baseline_name, 'sha256': H(FIXTURE / baseline_name)}, 'original_baseline_source': source, 'original_row_body': copy.deepcopy(fixture_row), 'authorized_original_path_aliases': used}
actual_validator = module.validate_owner_evidence_aliases
module.validate_owner_evidence_aliases = lambda root, b, m, a: copy.deepcopy(aliases)
try:
    selected = {source: copy.deepcopy(fixture_selected_row)}
    output = module.retain(FIXTURE, baseline_name, manifest_name, selected, {}, 'book/coverage/checks/synthetic-positive-content-map.json', authorization)
    content_map = R(FIXTURE / output['file'])
    assert content_map['original_input_count'] == len(fixture_frozen)
    assert {r['original_frozen_path']: r['sha256'] for r in content_map['input_bindings']} == fixture_frozen
    applied_binding = next(r for r in content_map['input_bindings'] if r['original_frozen_path'] == 'book/coverage/applied.json')
    assert applied_binding['sha256'] == manifest['frozen_inputs_sha256']['book/coverage/applied.json']
    assert applied_binding['retained_input'] != aliases['book/coverage/applied.json']['immutable_byte_copy']['file']
    assert selected[source]['checkpoint23_original_baseline_owner_evidence']['original_row_body'] == fixture_row
    fixture_results.append({'fixture': 'old_archive_aliases_and_actual_current_raw_owner_paths_coexist_with_entire_original_metadata', 'expected': 'accept', 'observed': 'accepted', 'frozen_Applied946_is_separately_retained': True})
    failures = [
        ('resurfaced_old_raw_owner_hash', lambda r: r['evidence_sha256'].update({'book/coverage/core.json': aliases['book/coverage/core.json']['original_sha256']})),
        ('arbitrary_new_raw_owner_hash', lambda r: r['evidence_sha256'].update({'book/coverage/core.json': '0' * 64})),
        ('frozen_Applied946_as_current_raw_path', lambda r: r['evidence_sha256'].update({'book/coverage/applied.json': manifest['frozen_inputs_sha256']['book/coverage/applied.json']})),
        ('missing_original_archive_alias', lambda r: r['evidence_sha256'].pop(aliases['book/coverage/core.json']['immutable_byte_copy']['file'])),
        ('changed_ordinary_evidence_hash', lambda r: r['evidence_sha256'].update({ordinary: '0' * 64})),
        ('changed_original_top_level_metadata_time', lambda r: r.update(original_review_time='changed synthetic metadata')),
        ('changed_entire_original_nested_row_body', lambda r: r['checkpoint23_original_baseline_owner_evidence']['original_row_body'].update(original_review_time='changed synthetic metadata')),
        ('changed_original_proof_source_hash', lambda r: r.update(sha256='0' * 64)),
    ]
    for index, (label, mutate) in enumerate(failures, 1):
        row = copy.deepcopy(fixture_selected_row)
        mutate(row)
        destination = 'book/coverage/checks/synthetic-negative-' + str(index) + '.json'
        try:
            module.retain(FIXTURE, baseline_name, manifest_name, {source: row}, {}, destination, authorization)
        except (AssertionError, KeyError, FileNotFoundError, ValueError):
            assert not (FIXTURE / destination).exists()
            fixture_results.append({'fixture': label, 'expected': 'reject', 'observed': 'rejected_before_writing'})
        else:
            raise AssertionError('Invalid retainer fixture accepted: ' + label)
finally:
    module.validate_owner_evidence_aliases = actual_validator

selector_body = bodies['book/coverage/prepare_checkpoint23_selection_v3.py']
retainer_body = bodies['book/coverage/retain_baseline_inputs23_v3.py']
plan_body = bodies['book/coverage/checks/prepare_root_owner23_alias_plan_v3.py']
for token in ['selection = copy.deepcopy(baseline[\'proof_files\'])', 'original = copy.deepcopy(row)', "'original_row_body': original", 'exact(row[\'evidence_sha256\'])', 'retain(ROOT, BASELINE, MANIFEST, selection, extras, CONTENT_MAP, authorization)', "all(type(code) is int and code == 0 for code in codes)"]:
    assert token in selector_body
for token in ["actual_installed_sha256[evidence] == sha(evidence)", "if key != 'evidence_sha256': assert selected[name][key] == value", "'original_row_body': row", "assert set(authorization['aliases']) == OWNER_EVIDENCE_PATHS", "manifest['working_inputs_sha256'][name]", "row['before_sha256'] == old_sha", "sha(expected_archive) == old_sha"]:
    assert token in retainer_body
assert "reverse['helpers_sha256']=original['helpers_sha256']" in plan_body and 'assert reverse == original' in plan_body
assert "failed['actual_exit_code'] == 1" in plan_body
assert "NEW_SELECTOR = 'book/coverage/prepare_checkpoint23_selection_v3.py'" in plan_body
assert "NEW_RETAINER = 'book/coverage/retain_baseline_inputs23_v3.py'" in plan_body
historical_paths = ['book/coverage/prepare_checkpoint23_selection_v1.py', 'book/coverage/retain_baseline_inputs23.py', 'book/coverage/prepare_checkpoint23_selection_v2.py', 'book/coverage/retain_baseline_inputs23_v2.py', 'reports/full-coverage/prepare-checkpoint23-selection-execution-v1.json', 'reports/full-coverage/prepare-checkpoint23-selection-execution-v1.log', old_plan_name]
historical_sha = {n: H(ROOT / n) for n in historical_paths}
assert R(ROOT / historical_paths[4])['actual_exit_code'] == 1
assert 'AssertionError: book/coverage/foundations.json' in (ROOT / historical_paths[5]).read_text()
assert all(H(ROOT / n) == digest for n, digest in hashes.items())
assert H(ROOT / baseline_name) == '083fe75e535ebbd37326e34407d13b90357738ea7f4244eb1cfe5da8226f9ff9'
assert all(H(ROOT / n) == rows[n]['candidate']['sha256'] for n in owners)
report = {
    'status': 'passed_independent_selector23_retainer23_alias_plan_v3_code_and_fixture_review_requires_actual_production_execution',
    'reviewed_at_utc': datetime.now(timezone.utc).isoformat(), 'reviewer': '/root/config21_next',
    'helpers_sha256': hashes, 'entire_reviewed_helper_bodies': bodies,
    'actual_checker': str(Path(__file__).relative_to(ROOT)), 'actual_checker_sha256': H(__file__),
    'actual_root_integration_execution': execution_ref, 'entire_original_actual_integration_execution': execution,
    'actual_root_integration_result': integration_ref, 'entire_original_actual_integration_result': integration,
    'validated_exact_four_owner_authorization': authorization, 'exact_four_stale_original_baseline_references': stale,
    'all1113_baseline_sources_and_normalized_other_original_evidence_rehashed': True,
    'fixture_results': fixture_results, 'synthetic_fixture_directory': str(FIXTURE),
    'fixture_scope': 'Actual validator is invoked read-only against genuine Root inputs and mutated authorization pointers. The generic retainer body runs on explicitly synthetic minimal fixtures using real copied old/current/frozen owner bytes; only the already-tested authorization call is substituted. No synthetic actual-execution records are created. These fixtures are code tests, not a production selection/freeze/audit.',
    'original_unmodified_history_sha256': historical_sha,
    'mechanical_decisions': [
        'Exactly four old working-owner evidence path/hash pairs are authorized by the genuine actual0 Root --apply execution, pinned command/cwd/helper/log, before hashes, exact archive paths, current candidate hashes and manifest22 working inputs.',
        'Original1113 sources and every other evidence byte remain exact. Each remapped row preserves its entire original row body/time and four original paths/hashes in explicit provenance. Current owner raw paths may coexist only at the validated installed hash and exact current bytes.',
        'Applied old working0ee, frozen946 and currentcf35 remain distinct. The frozen946 input is retained independently by its own exact fingerprint; the unpruned0ee archive is not treated as that frozen input.',
        'The new plan reverses entirely to originalv1 after removing additions and restoring only two helper references. The genuine selectorv1 failure/rawlog and original helper/plan bodies are retained, never retimed or turned into passing executions.',
        'Production selector retains the previous reviewed owner/source/import/paired-record/global/34051-content-map checks. This code reader does not call production prepare or plan prepare, and creates no production selection/content map.',
    ],
    'errors': [], 'coverage_complete': False,
    'scope': 'Independent exact code, actual-input and isolated accept/reject fixture review only. Root must execute the new plan and selector for genuine production outputs; aggregate23, Pages and live publication require separate actual checks. No current ledger, original baseline, source HTML, inventory or PUB file was modified.'
}
with OUT.open('x') as output:
    output.write(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'], 'report': str(OUT.relative_to(ROOT)), 'sha256': H(OUT), 'fixtures': len(fixture_results), 'actual_production_selection_executed': False}))

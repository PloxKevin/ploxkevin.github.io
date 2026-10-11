"""Draft Root-only exact frozen23 publication staging; never implies an audit pass.

Derived from immutable reviewed publication23_v2; both original unexecuted drafts are retained.
V3 requires the actual repaired selector-v3 execution-v2 and exact old-owner evidence
alias plan, preserving the genuine failed selector-v1 execution separately. It keeps
the config-v2 output and its independent review, which exclude
older lean-checkpoint-21 website content while retaining those exact files in Git. Execution requires genuine
23 audit/export/publication/config outputs and their independent readers.
Writing this draft performs no publication copy, Git operation or owner edit.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, subprocess, time

ROOT = Path(__file__).resolve().parents[3]
REPORTS = ROOT / 'reports/full-coverage'
SNAPSHOT = REPORTS / 'checkpoint-23'
PUBLICATION = ROOT / 'reports/book/publication-repo'
PRIOR_HELPER = 'book/coverage/checks/root_prepare_and_stage_publication22_v2.py'
PRIOR_HELPER_SHA = '9cd7262173790ce37bd45639f480d0963fd731333a7f6c85eaacb92a25bf1e7b'
ORIGINAL_DRAFT = 'book/coverage/checks/root_prepare_and_stage_publication23_v1.py'
ORIGINAL_DRAFT_SHA = '41f9b0b3abed1fa040e71c804eb9a090451b517578032d146dd397722735a718'
ORIGINAL_CONFIG_DRAFT = 'book/coverage/checks/root_prepare_pages23_config_v1.py'
ORIGINAL_CONFIG_DRAFT_SHA = '739f8c19235462895071307b783fe5bb96cff68301da1fb1bc48976141a52686'
EXPECTED_PROOFS = 1131
EXPECTED_THEOREMS = 9193
EXPECTED_BASELINE22 = 1113
EXPECTED_NEW = 18
EXPECTED_CORRECTIONS = 51
EXPECTED_INVENTORY_SHA = 'd746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
CONFIG_PEER = 'book/coverage/checks/pages23-config-independent-modules-review-v2.json'
STAGE_PEER = 'book/coverage/checks/publication23-helper-independent-foundations-review-v2.json'
ORIGINAL_STAGE_V2 = 'book/coverage/checks/root_prepare_and_stage_publication23_v2.py'
ORIGINAL_STAGE_V2_SHA = 'bee648459aac9a9b4277848f5486f65b0d13741e0207cec2d1544fc3d03a089f'
ORIGINAL_STAGE_PEER = 'book/coverage/checks/publication23-helper-independent-foundations-review-v1.json'
ORIGINAL_STAGE_PEER_SHA = '043f9fc04f6cde729d78a76f90d085a70fa6b019ed1a6f4ad70d15137a598020'
ALIAS_PLAN = 'book/coverage/checks/future23-core/checkpoint23-installed-owner-selection-plan-v3.json'
ALIAS_PEER_PREFIX = 'book/coverage/checks/future23-core/checkpoint23-owner-alias-helpers-independent-foundations'
REPAIR_HELPERS_SHA = {
    'book/coverage/prepare_checkpoint23_selection_v3.py': '3d646ccd946674944edd86bf55b10c5d5a4ee3cda4a1e7498f41aae8af6f226d',
    'book/coverage/retain_baseline_inputs23_v3.py': '904341fa346e1e76cf6914b5660b978666bf0653664e75b1517e0400b9a25068',
    'book/coverage/checks/prepare_root_owner23_alias_plan_v3.py': 'd1688dbe882a4bb989f65293b8b7e232fcff106ba2afefcefb583c6eb2b1a243',
    'book/coverage/prepare_checkpoint23_selection_v2.py': '9fea9b7ad21f72079967a705f138b4451f55519b87b478df0a4cb1961f9c5a2e',
    'book/coverage/retain_baseline_inputs23_v2.py': 'db95ec28d3d0a77d812e68cd1cc7bb1547a6d22e9f03f0672d76b20803ffb41a',
    'book/coverage/checks/prepare_root_owner23_alias_plan_v2.py': 'c84a2895470b6f98973d8d8972b9d1174f48d856baaa45c9880e327cc4b0622a',
}
PRODUCTION_PEER = 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-independent-confirmation-v1.json'
APPLIED_EXCLUSIONS = [
    'verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean',
    'verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean',
    'verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean',
]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text())

def safe_name(name):
    assert name and not Path(name).is_absolute() and '..' not in Path(name).parts, name
    assert '\x00' not in name and not any(x in name for x in ('\n', '\r')), name
    return name

def source_file(name):
    source = ROOT / safe_name(name)
    assert source.is_file() and not source.is_symlink() and source.stat().st_size < 100_000_000, name
    return source

def copy(name):
    source = source_file(name)
    target = PUBLICATION / name
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    assert sha(source) == sha(target), name
    return sha(source)

def actual_zero(name):
    record = read(source_file(name))
    codes = [record[key] for key in ('actual_exit_code', 'exit_code') if key in record]
    assert codes and all(code == 0 for code in codes), name
    for log_key, hash_key in (('log', 'log_sha256'), ('raw_log', 'raw_log_sha256')):
        if log_key in record and hash_key in record:
            assert sha(source_file(record[log_key])) == record[hash_key], name
    return record

started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
assert sha(ROOT / PRIOR_HELPER) == PRIOR_HELPER_SHA
assert sha(ROOT / ORIGINAL_DRAFT) == ORIGINAL_DRAFT_SHA
assert sha(ROOT / ORIGINAL_CONFIG_DRAFT) == ORIGINAL_CONFIG_DRAFT_SHA
assert sha(ROOT / ORIGINAL_STAGE_V2) == ORIGINAL_STAGE_V2_SHA
assert sha(ROOT / ORIGINAL_STAGE_PEER) == ORIGINAL_STAGE_PEER_SHA
for name, digest in REPAIR_HELPERS_SHA.items():
    assert sha(source_file(name)) == digest, name
manifest_path = REPORTS / 'checkpoint-23-manifest.json'
selection_path = REPORTS / 'checkpoint-23-selection.json'
manifest = read(manifest_path)
selection = read(selection_path)
audit = read(REPORTS / 'lean-checkpoint-23/verification-original.json')
assert manifest['status'] == 'formal_verification_passed_partial_coverage'
assert sha(selection_path) == manifest['selection_sha256']
assert len(manifest['proof_files']) == selection['proof_file_count'] == EXPECTED_PROOFS
assert audit['status'] == 'passed' and audit['proof_file_count'] == EXPECTED_PROOFS
assert audit['theorem_count'] == EXPECTED_THEOREMS
assert all(check['exit_code'] == 0 for check in audit['checks'])
execution_names = (
    'prepare-checkpoint23-selection-execution-v2', 'prepare-owner23-alias-plan-execution-v3',
    'freeze-checkpoint23-execution-v1',
    'cache-checkpoint23-execution-v1', 'verify-checkpoint23-execution-v1',
    'export-checkpoint23-execution-v1', 'prepare-publication23-execution-v1',
    'browser-checkpoint23-binding-execution-v1', 'frozen-ledger-checkpoint23-execution-v1',
)
for name in execution_names:
    actual_zero('reports/full-coverage/' + name + '.json')
# The original failed selector is history, never a successful prerequisite.
failed_selection_name = 'reports/full-coverage/prepare-checkpoint23-selection-execution-v1.json'
failed_selection = read(source_file(failed_selection_name))
failed_codes = [failed_selection[key] for key in ('actual_exit_code', 'exit_code') if key in failed_selection]
assert failed_codes and all(type(code) is int and code == 1 for code in failed_codes)
assert failed_selection['actual_command'] == [
    'python3', 'book/coverage/prepare_checkpoint23_selection_v1.py', '--plan',
    'book/coverage/checks/future23-core/checkpoint23-installed-owner-selection-plan-v1.json']
assert sha(source_file(failed_selection['log'])) == failed_selection['log_sha256']
repaired_selection = actual_zero('reports/full-coverage/prepare-checkpoint23-selection-execution-v2.json')
assert repaired_selection['actual_command'] == [
    'python3', 'book/coverage/prepare_checkpoint23_selection_v3.py', '--plan', ALIAS_PLAN]
alias_peer = read(source_file(ALIAS_PEER_PREFIX + '-review-v1.json'))
assert 'passed' in alias_peer['status']
actual_zero(ALIAS_PEER_PREFIX + '-actual-v1.json')
alias_plan = read(source_file(ALIAS_PLAN))
assert alias_plan['helpers_sha256'] == {
    name: REPAIR_HELPERS_SHA[name] for name in (
        'book/coverage/prepare_checkpoint23_selection_v3.py',
        'book/coverage/retain_baseline_inputs23_v3.py')}
authorized_aliases = alias_plan['authorized_baseline_owner_evidence_aliases']['aliases']
assert set(authorized_aliases) == {'book/coverage/' + owner + '.json'
    for owner in ('core', 'foundations', 'applied', 'modules')}
for name, row in authorized_aliases.items():
    archive = row['immutable_byte_copy']
    assert archive['sha256'] == row['original_sha256'] == sha(source_file(archive['file'])), name
assert alias_plan['original_failed_selector_v1_provenance']['actual_failed_execution'] == {
    'file': failed_selection_name, 'sha256': sha(source_file(failed_selection_name))}
actual_zero('reports/full-coverage/pages23-config-execution-v2.json')
config_peer = read(source_file(CONFIG_PEER))
assert 'passed' in config_peer['status']
assert config_peer['config_sha256'] == sha(PUBLICATION / '_config.yml')
production_peer = read(source_file(PRODUCTION_PEER))
assert 'passed' in production_peer['status']
stage_peer = read(source_file(STAGE_PEER))
assert 'passed' in stage_peer['status']
assert stage_peer['helper_sha256'] == sha(Path(__file__))

baseline = read(REPORTS / 'checkpoint-22-selection.json')
assert len(baseline['proof_files']) == EXPECTED_BASELINE22
assert set(baseline['proof_files']) <= set(manifest['proof_files'])
new_proofs = set(manifest['proof_files']) - set(baseline['proof_files'])
assert len(new_proofs) == EXPECTED_NEW
for name, row in baseline['proof_files'].items():
    assert manifest['proof_files'][name]['sha256'] == row['sha256'] == sha(SNAPSHOT / name), name
for name, row in manifest['proof_files'].items():
    assert sha(SNAPSHOT / name) == row['sha256'], name

# Working owners include the three retained, unreferenced Applied metadata rows;
# publication owners match the deliberately pruned, immutable frozen ledgers.
for owner in ('core', 'foundations', 'applied', 'modules'):
    name = 'book/coverage/' + owner + '.json'
    assert sha(ROOT / name) == manifest['working_inputs_sha256'][name], name
    assert sha(SNAPSHOT / name) == sha(PUBLICATION / name) == manifest['frozen_inputs_sha256'][name], name
    working = read(ROOT / name)
    frozen = read(SNAPSHOT / name)
    exclusions = manifest['excluded_unreferenced_ledger_metadata'][owner]
    assert exclusions == (APPLIED_EXCLUSIONS if owner == 'applied' else []), owner
    assert set(working['proof_files']) - set(manifest['proof_files']) == set(exclusions), owner
    listed = working['proof_files']
    working['proof_files'] = ([n for n in listed if n in manifest['proof_files']] if isinstance(listed, list)
                              else {n: v for n, v in listed.items() if n in manifest['proof_files']})
    if 'proof_sha256' in working:
        working['proof_sha256'] = {n: v for n, v in working['proof_sha256'].items() if n in manifest['proof_files']}
    assert working == frozen, owner

assets = {name: digest for name, digest in manifest['frozen_inputs_sha256'].items() if name.startswith('SafeLearning/')}
assert len(assets) == 31
for name, digest in assets.items():
    assert sha(ROOT / name) == sha(SNAPSHOT / name) == sha(PUBLICATION / name) == digest, name
assert sha(SNAPSHOT / 'book/coverage/inventory.json') == EXPECTED_INVENTORY_SHA
browser = read(REPORTS / 'browser-checkpoint-23.json')
assert browser['status'] == 'passed_actual_changed_pages_and_exact_unchanged_evidence'
assert browser['source_sha256'] == assets
assert (browser['verified_viewport_count'], browser['fresh_verified_viewport_count'],
        browser['retained_verified_viewport_count']) == (145, 10, 135)
assert sha(source_file(browser['actual_execution'])) == browser['actual_execution_sha256']
# Mechanical browser evidence does not assert a new complete manual visual pass.

names = set(read(REPORTS / 'publication-prepared-23-files.json'))
assert all(safe_name(name) == name for name in names)
for name in read(REPORTS / 'publication-prepared-22-files.json'):
    assert (PUBLICATION / safe_name(name)).is_file(), name
extras = {
    'book/coverage/checks/root_prepare_and_stage_publication23_v3.py', STAGE_PEER, CONFIG_PEER,
    'book/coverage/checks/root_prepare_pages23_config_v2.py', PRODUCTION_PEER,
    ORIGINAL_DRAFT, ORIGINAL_CONFIG_DRAFT, ORIGINAL_STAGE_V2, ORIGINAL_STAGE_PEER,
    ALIAS_PLAN, ALIAS_PEER_PREFIX + '-review-v1.json', ALIAS_PEER_PREFIX + '-check-v1.py',
    ALIAS_PEER_PREFIX + '-actual-v1.json', ALIAS_PEER_PREFIX + '-actual-v1.log',
    failed_selection_name, failed_selection['log'],
    'book/coverage/prepare_checkpoint23_selection_v1.py', 'book/coverage/retain_baseline_inputs23.py',
    'book/coverage/checks/future23-core/checkpoint23-installed-owner-selection-plan-v1.json',
}
extras.update(REPAIR_HELPERS_SHA)
extras.update(row['immutable_byte_copy']['file'] for row in authorized_aliases.values())
for name in execution_names:
    extras.update('reports/full-coverage/' + name + ext for ext in ('.json', '.log'))
extras.update('reports/full-coverage/' + name for name in (
    'checkpoint23-cache-preparation.json', 'publication-prepared-23-files.json',
    'pages23-config-preparation-v2.json', 'pages23-config-previous-original-v2.yml',
    'pages23-config-previous-original-v2.json', 'pages23-config-execution-v2.json',
    'pages23-config-execution-v2.log', 'publication-checks/ledger-checkpoint-23.json',
))
extras.update(str(path.relative_to(ROOT)) for path in (REPORTS / 'lean-checkpoint-23').rglob('*') if path.is_file())
extras.update(str(path.relative_to(ROOT)) for path in (ROOT / 'book/coverage/checks/future23-core').glob('modules-checkpoint23-production-output-*') if path.is_file())
extras.update(str(path.relative_to(ROOT)) for path in (ROOT / 'book/coverage/checks').glob('pages23-config-independent-modules-*') if path.is_file())
extras.update(str(path.relative_to(ROOT)) for path in (ROOT / 'book/coverage/checks').glob('pages23-config-independent-foundations-*') if path.is_file())
extra_hashes = {name: sha(source_file(name)) for name in sorted(extras)}

expected = dict(manifest['frozen_inputs_sha256'])
for name, digest in list(expected.items()):
    safe_name(name)
    assert sha(SNAPSHOT / name) == digest, name
    if name.startswith('reports/full-coverage/source-history/'):
        expected['reports/full-coverage/checkpoint-23/' + name] = digest
expected.pop('book/coverage/progress.json')
progress = read(PUBLICATION / 'book/coverage/progress.json')
original = read(SNAPSHOT / 'book/coverage/progress.json')
allowed = {'verified_checkpoint', 'current_frozen_audit', 'publication_status',
           'current_documented_material_corrections', 'inventory_sha256', 'current_published_ledger_candidate'}
assert {k: v for k, v in progress.items() if k not in allowed} == {k: v for k, v in original.items() if k not in allowed}
assert progress['verified_checkpoint']['proof_files'] == EXPECTED_PROOFS
assert progress['verified_checkpoint']['theorems'] == audit['theorem_count']
assert progress['verified_checkpoint']['status'] == 'passed'
assert progress['verified_checkpoint']['coverage_complete'] is False
assert progress['current_documented_material_corrections'] == EXPECTED_CORRECTIONS
assert progress['inventory_sha256'] == EXPECTED_INVENTORY_SHA

names.add('_config.yml')
extra_path = REPORTS / 'publication-extra23-files.json'
extra_name = str(extra_path.relative_to(ROOT))
names.update(extras)
names.update((extra_name, 'book/coverage/progress.json'))
for name in names:
    # Frozen historical evidence can include explicitly unselected archival trials.
    # It does not admit future24 active proof files or ledger promotions as23 coverage.
    if name.startswith('verification/lean/SafeLearning/') and name.endswith('.lean'):
        assert name in manifest['proof_files'], name
for argv in (['git', 'diff', '--name-only', '-z'], ['git', 'diff', '--cached', '--name-only', '-z'],
             ['git', 'ls-files', '--others', '--exclude-standard', '-z']):
    dirty = subprocess.run(argv, cwd=PUBLICATION, capture_output=True, check=True).stdout
    assert {name.decode() for name in dirty.split(b'\0') if name} <= names

# All audit/config/owner/source/frozen-byte prerequisites above are read-only.
# Only now copy the explicit, completed postfreeze evidence, then stage exact names.
for name, digest in extra_hashes.items():
    assert copy(name) == digest, name
assert not extra_path.exists()
extra_path.write_text(json.dumps(dict(status='actual_postfreeze_execution_evidence_copied_exactly',
    created_at_utc=datetime.now(timezone.utc).isoformat(), paths_sha256=extra_hashes,
    coverage_complete=False), indent=2) + '\n')
copy(extra_name)
excluded = [line[4:] for line in (PUBLICATION / '_config.yml').read_text().splitlines() if line.startswith('  - ')]
assert len(set(excluded)) == len(excluded) and 'reports/full-coverage/checkpoint-23' in excluded
included = sum(path.stat().st_size for path in PUBLICATION.rglob('*') if path.is_file()
    and '.git' not in path.relative_to(PUBLICATION).parts
    and not any(path.relative_to(PUBLICATION).as_posix() == x or
                path.relative_to(PUBLICATION).as_posix().startswith(x + '/') for x in excluded))
assert included < 900_000_000
for name in sorted(names):
    target = PUBLICATION / name
    assert target.is_file() and not target.is_symlink(), name
    if name in expected:
        assert sha(target) == expected[name], name
    elif name in {'book/coverage/progress.json', '_config.yml'}:
        expected[name] = sha(target)
    else:
        assert sha(target) == sha(ROOT / name), name
        expected[name] = sha(target)

record = REPORTS / 'publication-checkpoint23-prestage-integrity.json'
assert not record.exists()
record.write_text(json.dumps(dict(status='passed_exact_frozen_and_explicit_actual_evidence',
    checked_at_utc=datetime.now(timezone.utc).isoformat(), snapshot=str(SNAPSHOT.relative_to(ROOT)),
    manifest_sha256=sha(manifest_path), selection_sha256=sha(selection_path),
    baseline22_proofs_byte_exact=EXPECTED_BASELINE22, new23_selected_proof_count=EXPECTED_NEW,
    original22_helper=PRIOR_HELPER, original22_helper_sha256=PRIOR_HELPER_SHA,
    original_unexecuted23_stage_v2=ORIGINAL_STAGE_V2, original_unexecuted23_stage_v2_sha256=ORIGINAL_STAGE_V2_SHA,
    original_stage_v2_independent_peer=ORIGINAL_STAGE_PEER, original_stage_v2_independent_peer_sha256=ORIGINAL_STAGE_PEER_SHA,
    preserved_failed_selector_v1_execution=failed_selection_name, preserved_failed_selector_v1_execution_sha256=sha(source_file(failed_selection_name)),
    repaired_selector_helpers_sha256=REPAIR_HELPERS_SHA, repaired_selection_plan=ALIAS_PLAN,
    repaired_selection_plan_sha256=sha(source_file(ALIAS_PLAN)),
    original_unexecuted23_draft=ORIGINAL_DRAFT, original_unexecuted23_draft_sha256=ORIGINAL_DRAFT_SHA,
    original_unexecuted23_config_draft=ORIGINAL_CONFIG_DRAFT, original_unexecuted23_config_draft_sha256=ORIGINAL_CONFIG_DRAFT_SHA,
    published_file_budget_bytes=included, coverage_complete=False, paths_sha256=expected), indent=2) + '\n')
record_name = str(record.relative_to(ROOT))
copy(record_name)
names.add(record_name)
whitelist = REPORTS / 'publication-checkpoint23-staging-whitelist.json'
assert not whitelist.exists()
whitelist.write_text(json.dumps(sorted(names), indent=2) + '\n')
pathspec = REPORTS / 'publication-checkpoint23-stage-pathspec.nul'
assert not pathspec.exists()
pathspec.write_bytes(b''.join(name.encode() + b'\0' for name in sorted(names)))
command = ['git', 'add', '-f', '--pathspec-from-file=' + str(pathspec), '--pathspec-file-nul']
execution = subprocess.run(command, cwd=PUBLICATION, capture_output=True)
staged = subprocess.run(['git', 'diff', '--cached', '--name-only', '-z'], cwd=PUBLICATION, capture_output=True, check=True)
staged_names = {name.decode() for name in staged.stdout.split(b'\0') if name}
result = REPORTS / 'publication-checkpoint23-staging-execution.json'
assert not result.exists()
result.write_text(json.dumps(dict(status='passed_explicit_whitelist_staged' if execution.returncode == 0 else 'failed',
    actual_exit_code=execution.returncode, actual_command=command, actual_workdir=str(PUBLICATION),
    started_at_utc=started, finished_at_utc=datetime.now(timezone.utc).isoformat(),
    elapsed_seconds=time.monotonic() - tick, command_stdout=execution.stdout.decode(),
    command_stderr=execution.stderr.decode(), checked_paths=len(names), staged_paths=len(staged_names),
    integrity_record=record_name, integrity_record_sha256=sha(record)), indent=2) + '\n')
assert execution.returncode == 0 and staged_names and staged_names <= names
print(json.dumps(dict(status='passed', checked_paths=len(names), staged_paths=len(staged_names), elapsed_seconds=time.monotonic() - tick)))

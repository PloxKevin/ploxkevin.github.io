"""Independent read-only review of the actual Pages22 configuration output.

This script writes its unique TMP review only. It never runs the preparer,
Lean, Git, Pages, export or deployment commands.
"""
from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
import hashlib
import json
import os
import re

ROOT = Path('/home/oxrexkevin/SafetyBased')
PUB = ROOT / 'reports/book/publication-repo'
REPORTS = ROOT / 'reports/full-coverage'
OUT = Path('/tmp/pages22-config-independent-modules-review-v1.json')
OLD_CONFIG_SHA = '410746b5dbe55b9f760aeabd0939dfc791bfcf59a598b4e7f3d84e1381999bc2'
INV_SHA = '2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
PREPARER_SHA = '8d0eaf460c1ad7e12941d8747ad68898a5b5708007a80b7974934aa35512f6d8'
START = datetime.now(timezone.utc).isoformat()


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(path.read_text())


def ref(path):
    return {'file': path.relative_to(ROOT).as_posix(), 'sha256': sha(path)}


def literal_excludes(path):
    significant = [line for line in path.read_text().splitlines()
                   if line and not line.startswith('#')]
    assert significant[0] == 'exclude:'
    entries = []
    for line in significant[1:]:
        match = re.fullmatch(r'  - ([A-Za-z0-9][A-Za-z0-9/_.-]*)', line)
        assert match, (path, line)
        entry = match.group(1)
        pure = PurePosixPath(entry)
        assert not pure.is_absolute() and '..' not in pure.parts and '.' not in pure.parts
        assert pure.as_posix() == entry
        entries.append(entry)
    assert entries == sorted(set(entries))
    return entries


assert not OUT.exists(), 'Prior independent decisions must remain immutable'
config = PUB / '_config.yml'
previous = REPORTS / 'pages22-config-previous-original-v1.yml'
preparation_path = REPORTS / 'pages22-config-preparation-v1.json'
execution_path = REPORTS / 'pages22-config-execution-v1.json'
log_path = REPORTS / 'pages22-config-execution-v1.log'
preparer = ROOT / 'book/coverage/checks/root_prepare_pages22_config_v1.py'
preparation = read(preparation_path)
execution = read(execution_path)
assert execution['status'] == 'passed' and execution['actual_exit_code'] == 0
assert execution.get('actual_command', execution.get('command')) == ['python3', preparer.relative_to(ROOT).as_posix()]
assert execution['actual_workdir'] == str(ROOT)
assert sha(preparer) == preparation['actual_helper_sha256'] == PREPARER_SHA
expected_helper_map = {preparer.relative_to(ROOT).as_posix(): PREPARER_SHA}
assert execution['helper_sha256_before'] == execution['helper_sha256_after'] == expected_helper_map
assert execution['log_sha256'] == sha(log_path)
assert sha(previous) == OLD_CONFIG_SHA == preparation['previous_config_sha256']
assert preparation['previous_config'] == previous.relative_to(ROOT).as_posix()
old_peer = read(ROOT / 'book/coverage/checks/pages21-config-independent-foundations-review-v1.json')
assert 'passed' in old_peer['status'] and old_peer['config_sha256'] == OLD_CONFIG_SHA
assert sha(config) == preparation['config_sha256']
initial_config_sha = sha(config)
excluded = literal_excludes(config)
old_excluded = literal_excludes(previous)
assert len(old_excluded) == 50
inventories = {p.relative_to(PUB).as_posix() for p in (PUB / 'book/coverage').iterdir()
               if p.is_file() and re.fullmatch(r'inventory.*\.json', p.name) and p.name != 'inventory.json'}
expected_excluded = set(old_excluded) | inventories | {
    'reports/full-coverage/checkpoint-22',
    'reports/full-coverage/owner21-originals-before-owner22-integration-v1',
}
assert set(excluded) == expected_excluded
assert preparation['exclusions'] == excluded and preparation['excluded_count'] == len(excluded)


def is_excluded(name):
    name_parts = PurePosixPath(name).parts
    return any(name_parts[:len(PurePosixPath(entry).parts)] == PurePosixPath(entry).parts
               for entry in excluded)


manifest_path = REPORTS / 'checkpoint-22-manifest.json'
selection_path = REPORTS / 'checkpoint-22-selection.json'
audit_path = REPORTS / 'lean-checkpoint-22/verification-original.json'
manifest = read(manifest_path)
selection = read(selection_path)
audit = read(audit_path)
assert manifest['status'] == 'formal_verification_passed_partial_coverage'
assert manifest['coverage_complete'] is False
assert sha(selection_path) == manifest['selection_sha256']
assert selection['proof_file_count'] == len(manifest['proof_files']) == 1113
assert set(selection['proof_files']) == set(manifest['proof_files'])
assert audit['status'] == 'passed' and audit['proof_file_count'] == 1113
assert audit['theorem_count'] == 9002 and audit['checks']
assert all(row['exit_code'] == 0 for row in audit['checks'])
old_manifest_path = REPORTS / 'checkpoint-21-manifest.json'
assert sha(old_manifest_path) == 'f5d27edc32eb5d952b1cfc92424f3ab6399dd37586885b59e15fee6028184010'
old_manifest = read(old_manifest_path)
assert len(old_manifest['proof_files']) == 1089
assert len(old_manifest['frozen_inputs_sha256']) == 32040
binding_path = ROOT / 'book/coverage/checks/root-owner22-reviewed-candidate-bindings-v3.json'
assert sha(binding_path) == '8b39f77d1f8ead44b6b20d6a759434173b61c852a871a0b6805923c0d4c29b7f'
binding = read(binding_path)
new = binding['new_immutable_proof_sources_sha256']
assert len(new) == 24 and not set(new) & set(old_manifest['proof_files'])
assert set(manifest['proof_files']) == set(old_manifest['proof_files']) | set(new)
for name, row in manifest['proof_files'].items():
    assert sha(ROOT / name) == row['sha256']
    expected = old_manifest['proof_files'][name]['sha256'] if name in old_manifest['proof_files'] else new[name]
    assert row['sha256'] == expected

assets = {name: value for name, value in manifest['frozen_inputs_sha256'].items()
          if name.startswith('SafeLearning/')}
old_assets = {name: value for name, value in old_manifest['frozen_inputs_sha256'].items()
              if name.startswith('SafeLearning/')}
assert len(assets) == 31 and assets == old_assets == preparation['exact_current48_assets']
required = dict(assets)
required['book/coverage/inventory.json'] = INV_SHA
assert sha(ROOT / 'book/coverage/inventory-after-correction48.json') == INV_SHA
for owner in ('applied', 'core', 'foundations', 'modules'):
    name = f'book/coverage/{owner}.json'
    required[name] = manifest['working_inputs_sha256'][name]
    assert required[name] == binding['owners'][owner]['candidate_ledger']['sha256']
report_names = [
    'reports/full-coverage/README.md',
    'reports/full-coverage/integration-22.json',
    'reports/full-coverage/browser-checkpoint-22.json',
    'reports/full-coverage/checkpoint-22-manifest.json',
    'reports/full-coverage/checkpoint-22-selection.json',
    'reports/full-coverage/lean-checkpoint-22/verification-original.json',
    'reports/full-coverage/lean-checkpoint-22/verification.json',
    'reports/full-coverage/lean-checkpoint-22/ledger-audit.json',
    'reports/full-coverage/owner22-reviewed-candidate-integration-v1.json',
]
for name in report_names:
    required[name] = sha(ROOT / name)
for name, digest in required.items():
    assert not is_excluded(name), name
    assert (ROOT / name).is_file() and (PUB / name).is_file()
    assert not (PUB / name).is_symlink()
    assert sha(PUB / name) == sha(ROOT / name) == digest, name
assert required == preparation['required_published_sha256']
assert sorted(required) == preparation['required_published_paths']
assert not is_excluded('book/coverage/progress.json')
integration = read(ROOT / report_names[-1])
assert integration['applied'] is True and len(integration['exact_replacements']) == 5
assert integration['binding_manifest_sha256'] == sha(binding_path)
for key in ('all32040_frozen21_inputs_exact', 'all1089_selected21_root_source_hashes_exact',
            'all31_current48_safelearning_assets_exact'):
    assert integration[key] is True

old_trial_files = {name: digest for name, digest in old_manifest['frozen_inputs_sha256'].items()
                   if name.startswith('book/coverage/checks/future22-monitoring/')}
assert len(old_trial_files) == 32
for name, digest in old_trial_files.items():
    assert name not in selection['proof_files'] and is_excluded(name)
    for base in (ROOT, PUB, REPORTS / 'checkpoint-21'):
        assert (base / name).is_file() and sha(base / name) == digest
assert all(is_excluded(p.relative_to(ROOT).as_posix())
           for p in (ROOT / 'verification/lean/SafeLearning').glob('*.lean')
           if p.relative_to(ROOT).as_posix() not in manifest['proof_files'])

# Independently walk the actual publication tree, without trusting helper totals.
included_bytes = excluded_bytes = included_files = excluded_files = 0
for directory, subdirectories, filenames in os.walk(PUB, followlinks=False):
    subdirectories[:] = [name for name in subdirectories if name != '.git']
    for name in subdirectories:
        path = Path(directory) / name
        if not is_excluded(path.relative_to(PUB).as_posix()):
            assert not path.is_symlink(), str(path)
    for name in filenames:
        path = Path(directory) / name
        if not path.is_file():
            continue
        if is_excluded(path.relative_to(PUB).as_posix()):
            excluded_bytes += path.stat().st_size
            excluded_files += 1
        else:
            assert not path.is_symlink(), str(path)
            included_bytes += path.stat().st_size
            included_files += 1
assert included_bytes < 900_000_000
assert sha(config) == initial_config_sha
report = {
    'status': 'independent_actual_pages22_configuration_and_exact_publication_output_review_passed',
    'reviewed_by': '/root/modules_resume',
    'started_at_utc': START,
    'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
    'actual_checker': str(Path(__file__)),
    'actual_checker_sha256': sha(Path(__file__)),
    'config': ref(config), 'config_sha256': initial_config_sha,
    'previous_config': ref(previous), 'previous_config_sha256': OLD_CONFIG_SHA,
    'actual_preparation': ref(preparation_path), 'actual_preparation_execution': ref(execution_path),
    'actual_preparation_raw_log': ref(log_path), 'actual_preparer': ref(preparer),
    'exclusions': excluded, 'new_exclusions': sorted(set(excluded) - set(old_excluded)),
    'required_published_sha256': required,
    'exact_current48_asset_count': len(assets), 'exact_installed_owner_ledger_count': 4,
    'actual_audit': {'report': ref(audit_path), 'proof_file_count': 1113,
                     'theorem_count': 9002, 'check_count': len(audit['checks']), 'all_exit_codes_zero': True},
    'all1089_baseline_proof_hashes_exact': True, 'all24_new_canonical_proof_hashes_exact': True,
    'archival32_prior_monitoring_trial_files_sha256': old_trial_files,
    'included_source_bytes': included_bytes, 'included_source_file_count': included_files,
    'excluded_source_bytes': excluded_bytes, 'excluded_source_file_count': excluded_files,
    'independent_budget_limit_bytes': 900_000_000,
    'preparation_included_source_bytes': preparation['included_file_bytes'],
    'measurement_difference_bytes': included_bytes - preparation['included_file_bytes'],
    'coverage_complete': False,
    'scope': 'Read-only independent output check. Actual Pages workflow, generated artifact and deployment require separate execution. No compiler, export, preparer, Git or Pages command is run by this checker. Original source/review times and execution evidence stay immutable.',
}
OUT.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'], 'report': str(OUT), 'sha256': sha(OUT),
                  'config_sha256': initial_config_sha, 'included_source_bytes': included_bytes}))

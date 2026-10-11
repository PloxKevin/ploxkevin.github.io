"""Independent read-only review of the actual Pages23 configuration output.

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
OUT = Path('/tmp/pages23-config-independent-modules-review-v3.json')
OLD_CONFIG_SHA = '443a2c117d1caf7d3d0236235b15af1cafc48cfd60ab8f9b60ef5a9c7909e41a'
INV_SHA = 'd746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
PREPARER_SHA = 'efb1d71313f940a531c98af69900482ba71713dd4d7cca35a01a1dcca0f0c1c4'
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
previous = REPORTS / 'pages23-config-previous-original-v3.yml'
preparation_path = REPORTS / 'pages23-config-preparation-v3.json'
execution_path = REPORTS / 'pages23-config-execution-v3.json'
log_path = REPORTS / 'pages23-config-execution-v3.log'
preparer = ROOT / 'book/coverage/checks/root_prepare_pages23_config_v3.py'
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
old_peer = read(ROOT / 'book/coverage/checks/pages22-config-independent-modules-review-v1.json')
assert 'passed' in old_peer['status'] and old_peer['config_sha256'] == OLD_CONFIG_SHA
assert sha(config) == preparation['config_sha256']
initial_config_sha = sha(config)
excluded = literal_excludes(config)
old_excluded = literal_excludes(previous)
assert len(old_excluded) == 52
inventories = {p.relative_to(PUB).as_posix() for p in (PUB / 'book/coverage').iterdir()
               if p.is_file() and re.fullmatch(r'inventory.*\.json', p.name) and p.name != 'inventory.json'}

# Independently check the original genuine budget failure and exact old archives.
import ast
constant_nodes = {n.targets[0].id: n.value for n in ast.parse(preparer.read_text()).body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name)}
archive_map = ast.literal_eval(constant_nodes['OLD_REPORT_INVENTORY_ARCHIVES_SHA256'])
assert len(archive_map)==8
assert set(archive_map)=={p.relative_to(PUB).as_posix() for p in (PUB/'reports/full-coverage').glob('inventory*.json')}
assert archive_map==preparation['old_report_inventory_archives_sha256_retained_exact_in_git']
for n,d in archive_map.items(): assert sha(ROOT/n)==sha(PUB/n)==d
failed_path = ROOT/'reports/full-coverage/pages23-config-execution-v2.json'
failed_log = ROOT/'reports/full-coverage/pages23-config-execution-v2.log'
failed = read(failed_path)
assert sha(failed_path)==preparation['actual_failed_config_v2_sha256']=='29ba55b594f8fc16240a2228c3911290d6bc402efc6cab0211b8a31b7b3b542d'
assert failed['status']=='failed' and failed['actual_exit_code']==preparation['actual_failed_config_v2_exit_code']==1
assert failed['actual_command']==['python3','book/coverage/checks/root_prepare_pages23_config_v2.py']
assert sha(failed_log)==failed['log_sha256']==preparation['actual_failed_config_v2_raw_log_sha256']=='746c7b7122bd91aaa8d7427ac6f82ab321857a84d817d42aeba22cd2e684d069'
assert 'assert included_bytes < 900_000_000' in failed_log.read_text()
assert not any((REPORTS/n).exists() for n in ['pages23-config-previous-original-v2.yml','pages23-config-previous-original-v2.json','pages23-config-preparation-v2.json'])
assert sha(ROOT/'book/coverage/checks/root_prepare_pages23_config_v2.py')==preparation['original_config_v2_sha256']=='7256ceed8c875961e8ecc097caf070c9727be2b9099a1c07e112d0e90af97331'

expected_excluded = set(old_excluded) | inventories | set(archive_map) | {
    'reports/full-coverage/checkpoint-23',
    'reports/full-coverage/owner22-originals-before-owner23-integration-v1',
    'reports/full-coverage/lean-checkpoint-21',
}
assert set(excluded) == expected_excluded
assert preparation['exclusions'] == excluded and preparation['excluded_count'] == len(excluded)


def is_excluded(name):
    name_parts = PurePosixPath(name).parts
    return any(name_parts[:len(PurePosixPath(entry).parts)] == PurePosixPath(entry).parts
               for entry in excluded)


manifest_path = REPORTS / 'checkpoint-23-manifest.json'
selection_path = REPORTS / 'checkpoint-23-selection.json'
audit_path = REPORTS / 'lean-checkpoint-23/verification-original.json'
manifest = read(manifest_path)
selection = read(selection_path)
audit = read(audit_path)
assert manifest['status'] == 'formal_verification_passed_partial_coverage'
assert manifest['coverage_complete'] is False
assert sha(selection_path) == manifest['selection_sha256']
assert selection['proof_file_count'] == len(manifest['proof_files']) == 1131
assert set(selection['proof_files']) == set(manifest['proof_files'])
assert audit['status'] == 'passed' and audit['proof_file_count'] == 1131
assert audit['theorem_count'] == 9193 and audit['checks']
assert all(type(row['exit_code']) is int and row['exit_code'] == 0 for row in audit['checks'])
assert len(audit['declarations'])==9193
assert audit['proof_sha256']=={n:r['sha256'] for n,r in selection['proof_files'].items()}
old_manifest_path = REPORTS / 'checkpoint-22-manifest.json'
assert sha(old_manifest_path) == 'c8e4ce87ceceed0092e0593d4b6d5fed1340bc151af9aa2aaeb6e07f220413bb'
old_manifest = read(old_manifest_path)
assert len(old_manifest['proof_files']) == 1113
assert len(old_manifest['frozen_inputs_sha256']) == 34051
binding_path = ROOT / 'book/coverage/checks/root-owner23-reviewed-candidate-bindings-v1.json'
assert sha(binding_path) == '4b6dd0eb2bae622be47e0fd96adf12a4b3c2dc10cc44baf1b34703c6cca8b054'
binding = read(binding_path)
new = {n:r['sha256'] for owner in binding['owners'].values() for n,r in owner['new_immutable_proof_sources'].items()}
assert len(new) == 18 and not set(new) & set(old_manifest['proof_files'])
assert set(manifest['proof_files']) == set(old_manifest['proof_files']) | set(new)
for name, row in manifest['proof_files'].items():
    assert sha(ROOT / name) == row['sha256']
    expected = old_manifest['proof_files'][name]['sha256'] if name in old_manifest['proof_files'] else new[name]
    assert row['sha256'] == expected

assets = {name: value for name, value in manifest['frozen_inputs_sha256'].items()
          if name.startswith('SafeLearning/')}
old_assets = {name: value for name, value in old_manifest['frozen_inputs_sha256'].items()
              if name.startswith('SafeLearning/')}
source_revisions = {'SafeLearning/cmdp.html':'76c03226e17b8c058fa05085e55dbe9374272541fd1c347d7a0dc98542b3795a','SafeLearning/lyapunov-mpc.html':'228e4e22eaa32ad287069001abe9507706ec0112ec2ed9e1d3cfb2d569c4be7c'}
expected_assets = dict(old_assets); expected_assets.update(source_revisions)
assert len(assets) == 31 and assets == expected_assets == preparation['exact_current51_assets']
assert {n for n in assets if assets[n] != old_assets[n]} == set(source_revisions)
assert preparation['deliberate_source51_asset_revisions_from22'] == source_revisions
required = dict(assets)
required['book/coverage/inventory.json'] = INV_SHA
assert sha(ROOT / 'book/coverage/inventory-after-correction51.json') == INV_SHA
ledger_scope_rows = []
expected_removed = {
    'applied': [
        'verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean',
        'verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean',
        'verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean',
    ],
}
for owner in ('applied', 'core', 'foundations', 'modules'):
    name = f'book/coverage/{owner}.json'
    live_digest = manifest['working_inputs_sha256'][name]
    frozen_digest = manifest['frozen_inputs_sha256'][name]
    assert sha(ROOT / name) == live_digest == binding['owners'][owner]['candidate_ledger']['sha256']
    assert sha(PUB / name) == sha(REPORTS / 'checkpoint-23' / name) == frozen_digest
    removed = manifest['excluded_unreferenced_ledger_metadata'][owner]
    assert removed == expected_removed.get(owner, [])
    live = read(ROOT / name)
    published = read(PUB / name)
    assert set(live['proof_files']) - set(manifest['proof_files']) == set(removed)
    # Reverse the sole approved frozen-ledger transformation independently.
    normalized = json.loads(json.dumps(live))
    if isinstance(normalized['proof_files'], list):
        normalized['proof_files'] = [n for n in normalized['proof_files'] if n not in removed]
    else:
        normalized['proof_files'] = {n:v for n,v in normalized['proof_files'].items() if n not in removed}
    if 'proof_sha256' in normalized:
        normalized['proof_sha256'] = {n:v for n,v in normalized['proof_sha256'].items() if n not in removed}
    assert normalized == published, owner
    required[name] = frozen_digest
    ledger_scope_rows.append({'owner':owner, 'working_sha256':live_digest,
                              'frozen_published_sha256':frozen_digest,
                              'exact_removed_unreferenced_metadata':removed,
                              'all_other_json_bodies_unchanged':True})
assert preparation['working_owner_ledger_sha256'] == {f'book/coverage/{r["owner"]}.json':r['working_sha256'] for r in ledger_scope_rows}
assert preparation['excluded_unreferenced_ledger_metadata'] == manifest['excluded_unreferenced_ledger_metadata']
report_names = [
    'reports/full-coverage/README.md',
    'reports/full-coverage/integration-23.json',
    'reports/full-coverage/browser-checkpoint-23.json',
    'reports/full-coverage/checkpoint-23-manifest.json',
    'reports/full-coverage/checkpoint-23-selection.json',
    'reports/full-coverage/lean-checkpoint-23/verification-original.json',
    'reports/full-coverage/lean-checkpoint-23/verification.json',
    'reports/full-coverage/lean-checkpoint-23/ledger-audit.json',
    'reports/full-coverage/owner23-reviewed-candidate-integration-v1.json',
]
for name in report_names:
    required[name] = sha(PUB / name) if name == 'reports/full-coverage/README.md' else sha(ROOT / name)
for name, digest in required.items():
    assert not is_excluded(name), name
    assert (ROOT / name).is_file() and (PUB / name).is_file()
    assert not (PUB / name).is_symlink()
    assert sha(PUB / name) == digest, name
    if name != 'reports/full-coverage/README.md' and name not in {f'book/coverage/{owner}.json' for owner in ('applied','core','foundations','modules')}:
        assert sha(ROOT / name) == digest, name
assert required == preparation['required_published_sha256']
assert sorted(required) == preparation['required_published_paths']
assert not is_excluded('book/coverage/progress.json')
integration = read(ROOT / report_names[-1])
assert integration['applied'] is True and len(integration['exact_replacements']) == 5
assert integration['binding_manifest_sha256'] == sha(binding_path)
for key in ('all34051_frozen22_inputs_exact', 'all1113_selected22_root_source_hashes_exact',
            'all31_current51_safelearning_assets_exact'):
    assert integration[key] is True

original21 = read(REPORTS / 'checkpoint-21-manifest.json')
old_trial_files = {name: digest for name, digest in original21['frozen_inputs_sha256'].items()
                   if name.startswith('book/coverage/checks/future22-monitoring/')}
assert len(old_trial_files) == 32
for name, digest in old_trial_files.items():
    assert name not in selection['proof_files'] and is_excluded(name)
    for base in (ROOT, PUB, REPORTS / 'checkpoint-21'):
        assert (base / name).is_file() and sha(base / name) == digest
assert all(is_excluded(p.relative_to(ROOT).as_posix())
           for p in (ROOT / 'verification/lean/SafeLearning').glob('*.lean')
           if p.relative_to(ROOT).as_posix() not in manifest['proof_files'])

older_archive = 'reports/full-coverage/lean-checkpoint-21'
older_files = {p.relative_to(ROOT).as_posix():sha(p) for p in (ROOT / older_archive).rglob('*') if p.is_file()}
assert older_files and older_files == preparation['older21_audit_archive_sha256_retained_exact_in_git']
assert all(sha(PUB/n)==d and is_excluded(n) for n,d in older_files.items())
assert sum((PUB/n).stat().st_size for n in older_files)==preparation['older21_audit_archive_bytes']
import subprocess
tracked = subprocess.run(['git','ls-files','-z','--',older_archive],cwd=PUB,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
assert set(filter(None,tracked.stdout.decode().split('\0')))==set(older_files)
subprocess.run(['git','diff','--quiet','HEAD','--',older_archive],cwd=PUB,check=True)

assert all(is_excluded(n) for n in archive_map)
tracked_inventories = subprocess.run(['git','ls-files','-z','--',*sorted(archive_map)],cwd=PUB,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
assert set(filter(None,tracked_inventories.stdout.decode().split('\0')))==set(archive_map)
subprocess.run(['git','diff','--quiet','HEAD','--',*sorted(archive_map)],cwd=PUB,check=True)
assert sum((PUB/n).stat().st_size for n in archive_map)==preparation['old_report_inventory_archive_bytes']

assert not is_excluded('reports/full-coverage/lean-checkpoint-22/verification-original.json')
assert sha(config)==initial_config_sha

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
    'status': 'independent_actual_pages23_configuration_and_exact_publication_output_review_passed',
    'reviewed_by': '/root/modules_resume',
    'started_at_utc': START,
    'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
    'actual_checker': str(Path(__file__)),
    'preserved_first_actual_reader_failure': {'checker': str(Path('/tmp/modules-pages23-output-independent-check-v2.py')), 'checker_sha256': sha(Path('/tmp/modules-pages23-output-independent-check-v2.py')), 'actual_execution': {'file': '/tmp/pages23-config-independent-modules-actual-execution-v2.json', 'sha256': sha(Path('/tmp/pages23-config-independent-modules-actual-execution-v2.json'))}, 'raw_log': {'file': '/tmp/pages23-config-independent-modules-actual-execution-v2.log', 'sha256': sha(Path('/tmp/pages23-config-independent-modules-actual-execution-v2.log'))}, 'reason': 'The first actual reader requested a flat new-source field from the four-owner binding; the binding records the same exact hashes under each owner. This corrected reader merges that explicit map without changing actual configuration or evidence.'},
    'actual_checker_sha256': sha(Path(__file__)),
    'config': ref(config), 'config_sha256': initial_config_sha,
    'previous_config': ref(previous), 'previous_config_sha256': OLD_CONFIG_SHA,
    'actual_preparation': ref(preparation_path), 'actual_preparation_execution': ref(execution_path),
    'actual_preparation_raw_log': ref(log_path), 'actual_preparer': ref(preparer),
    'exclusions': excluded, 'new_exclusions': sorted(set(excluded) - set(old_excluded)),
    'required_published_sha256': required,
    'exact_current51_asset_count': len(assets), 'exact_installed_owner_ledger_count': 4,
    'working_and_frozen_owner_ledger_scopes': ledger_scope_rows,
    'independent_config_code_peer': ref(ROOT / 'book/coverage/checks/pages23-config-v3-helper-independent-foundations-review-v1.json'),
    'preserved_original_unexecuted_independent_checker': {'file': str(Path('/tmp/modules-pages23-output-independent-check-v1.py')), 'sha256': sha(Path('/tmp/modules-pages23-output-independent-check-v1.py'))},
    'original_actual_config_v2_budget_failure': ref(failed_path), 'original_actual_config_v2_failure_raw_log': ref(failed_log),
    'exact_old_report_inventory_archives_retained_in_git': archive_map,
    'actual_audit': {'report': ref(audit_path), 'proof_file_count': 1131,
                     'theorem_count': 9193, 'check_count': len(audit['checks']), 'all_exit_codes_zero': True},
    'all1113_baseline_proof_hashes_exact': True, 'all18_new_canonical_proof_hashes_exact': True,
    'archival32_prior_monitoring_trial_files_sha256': old_trial_files,
    'included_source_bytes': included_bytes, 'included_source_file_count': included_files,
    'excluded_source_bytes': excluded_bytes, 'excluded_source_file_count': excluded_files,
    'independent_budget_limit_bytes': 900_000_000,
    'preparation_included_source_bytes': preparation['included_file_bytes'],
    'measurement_difference_bytes': included_bytes - preparation['included_file_bytes'],
    'coverage_complete': False,
    'scope': 'Read-only independent output check. Actual Pages workflow, generated artifact and deployment require separate execution. No compiler, export, preparer, Git mutation or Pages command is run by this checker; Git tracked names and HEAD equality are checked read-only. Original source/review times and execution evidence stay immutable.',
}
OUT.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'], 'report': str(OUT), 'sha256': sha(OUT),
                  'config_sha256': initial_config_sha, 'included_source_bytes': included_bytes}))

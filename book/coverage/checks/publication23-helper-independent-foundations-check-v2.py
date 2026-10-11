"""Read-only independent code review; do not import or execute the staging draft."""
from pathlib import Path
from datetime import datetime, timezone
import ast
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
H = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
helper = ROOT / 'book/coverage/checks/root_prepare_and_stage_publication23_v3.py'
out = ROOT / 'book/coverage/checks/publication23-helper-independent-foundations-review-v2.json'
assert not out.exists()
assert H(helper) == '9a584d7155f6696a9fd225277005341dc8f908f4a74fdb911498eb7de0a078bb'
body = helper.read_text()
tree = ast.parse(body)
constants = {}
for node in tree.body:
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        try:
            constants[node.targets[0].id] = ast.literal_eval(node.value)
        except (ValueError, TypeError):
            pass
assert (constants['EXPECTED_PROOFS'], constants['EXPECTED_THEOREMS'], constants['EXPECTED_BASELINE22'], constants['EXPECTED_NEW'], constants['EXPECTED_CORRECTIONS']) == (1131, 9193, 1113, 18, 51)
assert constants['EXPECTED_INVENTORY_SHA'] == 'd746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
bindings = {
    constants['PRIOR_HELPER']: constants['PRIOR_HELPER_SHA'],
    constants['ORIGINAL_DRAFT']: constants['ORIGINAL_DRAFT_SHA'],
    constants['ORIGINAL_CONFIG_DRAFT']: constants['ORIGINAL_CONFIG_DRAFT_SHA'],
    'book/coverage/checks/root_prepare_pages23_config_v2.py': '7256ceed8c875961e8ecc097caf070c9727be2b9099a1c07e112d0e90af97331',
}
for name, digest in bindings.items():
    assert H(ROOT / name) == digest, name
assert constants['CONFIG_PEER'] == 'book/coverage/checks/pages23-config-independent-modules-review-v2.json'
assert constants['STAGE_PEER'] == 'book/coverage/checks/publication23-helper-independent-foundations-review-v2.json'
assert constants['PRODUCTION_PEER'] == 'book/coverage/checks/future23-core/modules-checkpoint23-production-output-independent-confirmation-v1.json'
assert constants['APPLIED_EXCLUSIONS'] == [
    'verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean',
    'verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean',
    'verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean',
]
# Inspect the actual bodies, and check that mutations follow the prerequisites.
functions = {node.name: ast.get_source_segment(body, node) for node in tree.body if isinstance(node, ast.FunctionDef)}
assert 'Path(name).is_absolute()' in functions['safe_name'] and "'..' not in Path(name).parts" in functions['safe_name']
assert "'\\x00' not in name" in functions['safe_name'] and "('\\n', '\\r')" in functions['safe_name']
assert 'not source.is_symlink()' in functions['source_file'] and '100_000_000' in functions['source_file']
assert 'all(code == 0 for code in codes)' in functions['actual_zero'] and "('actual_exit_code', 'exit_code')" in functions['actual_zero']
assert "('log', 'log_sha256'), ('raw_log', 'raw_log_sha256')" in functions['actual_zero']
tokens = [
    "manifest['status'] == 'formal_verification_passed_partial_coverage'",
    "sha(selection_path) == manifest['selection_sha256']",
    "audit['status'] == 'passed'", "all(check['exit_code'] == 0 for check in audit['checks'])",
    "stage_peer['helper_sha256'] == sha(Path(__file__))",
    "config_peer['config_sha256'] == sha(PUBLICATION / '_config.yml')",
    "set(baseline['proof_files']) <= set(manifest['proof_files'])",
    "len(new_proofs) == EXPECTED_NEW", "sha(SNAPSHOT / name) == row['sha256']",
    "sha(ROOT / name) == manifest['working_inputs_sha256'][name]",
    "sha(SNAPSHOT / name) == sha(PUBLICATION / name) == manifest['frozen_inputs_sha256'][name]",
    'assert working == frozen', 'assert len(assets) == 31',
    "sha(ROOT / name) == sha(SNAPSHOT / name) == sha(PUBLICATION / name) == digest",
    "(145, 10, 135)", "sha(source_file(browser['actual_execution'])) == browser['actual_execution_sha256']",
    "assert sha(SNAPSHOT / name) == digest", "expected.pop('book/coverage/progress.json')",
    "progress['verified_checkpoint']['coverage_complete'] is False",
    "progress['inventory_sha256'] == EXPECTED_INVENTORY_SHA", "assert name in manifest['proof_files']",
    "['git', 'diff', '--name-only', '-z']", "['git', 'diff', '--cached', '--name-only', '-z']",
    "['git', 'ls-files', '--others', '--exclude-standard', '-z']",
    "assert {name.decode() for name in dirty.split(b'\\0') if name} <= names",
    "assert included < 900_000_000", "assert sha(target) == expected[name]",
    "assert sha(target) == sha(ROOT / name)", "'--pathspec-file-nul'",
    "assert execution.returncode == 0 and staged_names and staged_names <= names",
]
for token in tokens:
    assert token in body, token
mutation_boundary = body.index('for name, digest in extra_hashes.items():')
for token in tokens[:25]:
    assert body.index(token) < mutation_boundary, token
for name in [
    'prepare-checkpoint23-selection-execution-v1', 'freeze-checkpoint23-execution-v1',
    'cache-checkpoint23-execution-v1', 'verify-checkpoint23-execution-v1',
    'export-checkpoint23-execution-v1', 'prepare-publication23-execution-v1',
    'browser-checkpoint23-binding-execution-v1', 'frozen-ledger-checkpoint23-execution-v1',
    'pages23-config-execution-v2.json', 'pages23-config-preparation-v2.json',
    'pages23-config-previous-original-v2.yml', 'pages23-config-previous-original-v2.json',
]:
    assert name in body
assert "glob('pages23-config-independent-modules-*')" in body
assert "glob('pages23-config-independent-foundations-*')" in body
assert "ROOT / 'book/coverage/progress.json'" not in body
assert '.unlink(' not in body and 'shutil.rmtree' not in body
old_peer = ROOT / constants['ORIGINAL_STAGE_PEER']
old_helper = ROOT / constants['ORIGINAL_STAGE_V2']
assert H(old_peer) == constants['ORIGINAL_STAGE_PEER_SHA'] == '043f9fc04f6cde729d78a76f90d085a70fa6b019ed1a6f4ad70d15137a598020'
assert H(old_helper) == constants['ORIGINAL_STAGE_V2_SHA'] == 'bee648459aac9a9b4277848f5486f65b0d13741e0207cec2d1544fc3d03a089f'
original_peer = json.loads(old_peer.read_text())
assert original_peer['helper_sha256'] == H(old_helper)
for name,digest in constants['REPAIR_HELPERS_SHA'].items(): assert H(ROOT/name)==digest,name
alias_peer_path = ROOT / (constants['ALIAS_PEER_PREFIX'] + '-review-v1.json')
assert H(alias_peer_path) == 'b68086df2c8f34d2ae5d5cebf00ad82a91776dd3d6997b2ca6e1e311548f6e0e'
alias_peer = json.loads(alias_peer_path.read_text())
assert 'passed' in alias_peer['status'] and not alias_peer['errors']
for name,digest in alias_peer['helpers_sha256'].items(): assert constants['REPAIR_HELPERS_SHA'][name]==digest
failed_path=ROOT/'reports/full-coverage/prepare-checkpoint23-selection-execution-v1.json';failed=json.loads(failed_path.read_text());assert failed['actual_exit_code']==1;assert H(ROOT/failed['log'])==failed['log_sha256']
for token in [
    "'prepare-checkpoint23-selection-execution-v2', 'prepare-owner23-alias-plan-execution-v3'",
    "assert failed_codes and all(type(code) is int and code == 1 for code in failed_codes)",
    "'python3', 'book/coverage/prepare_checkpoint23_selection_v3.py', '--plan', ALIAS_PLAN",
    "actual_zero(ALIAS_PEER_PREFIX + '-actual-v1.json')",
    "archive['sha256'] == row['original_sha256'] == sha(source_file(archive['file']))",
    "extras.update(REPAIR_HELPERS_SHA)",
    "extras.update(row['immutable_byte_copy']['file'] for row in authorized_aliases.values())",
    "ALIAS_PEER_PREFIX + '-actual-v1.json', ALIAS_PEER_PREFIX + '-actual-v1.log'",
    "assert alias_plan['original_failed_selector_v1_provenance']['actual_failed_execution']",
]:
    assert token in body,token
    if not token.startswith('extras.') and not token.startswith('ALIAS_PEER_PREFIX'): assert body.index(token)<mutation_boundary,token

config_before = H(ROOT / 'reports/book/publication-repo/_config.yml')
future_paths = [
    'reports/full-coverage/checkpoint-23-manifest.json',
    'reports/full-coverage/lean-checkpoint-23/verification-original.json',
    'reports/full-coverage/pages23-config-preparation-v2.json',
    'reports/full-coverage/pages23-config-execution-v2.json',
    constants['CONFIG_PEER'], constants['PRODUCTION_PEER'],
]
observed = {name: {'present_at_code_review': (ROOT / name).exists(), 'sha256': H(ROOT / name) if (ROOT / name).is_file() else None} for name in future_paths}
assert H(helper) == '9a584d7155f6696a9fd225277005341dc8f908f4a74fdb911498eb7de0a078bb'
assert H(ROOT / 'reports/book/publication-repo/_config.yml') == config_before
report = {
    'status': 'passed_independent_publication23_staging_helper_code_review_requires_actual_future_outputs',
    'reviewed_at_utc': datetime.now(timezone.utc).isoformat(), 'reviewer': '/root/config21_next',
    'helper': str(helper.relative_to(ROOT)), 'helper_sha256': H(helper), 'entire_reviewed_helper_body': body,
    'actual_checker': str(Path(__file__).relative_to(ROOT)), 'actual_checker_sha256': H(__file__),
    'original_and_current_helper_bindings_sha256': bindings,
     'entire_original_stage_v2_independent_peer_body_and_time': original_peer,
    'original_v2_stage_helper_sha256': H(old_helper),
    'independent_alias_v3_code_and_fixture_peer': {'file':str(alias_peer_path.relative_to(ROOT)),'sha256':H(alias_peer_path)},
    'genuine_failed_selection_v1_execution_sha256':H(failed_path),
    'narrow_v3_delta_reason': 'Actual repaired selector-v3 execution-v2 and plan-v3 execution are mandatory successful prerequisites; original selector-v1 exit1 stays failed history. Exact helper-v3 and original unexecuted helper-v2 hashes plus alias peer/checker/actual JSON/rawlog and four old archive bytes are explicitly preserved. All prior reviewed staging guards stay present, including working/frozen Applied scope and explicit whitelist/budget/source/progress checks.',
    'mechanical_decisions': [
        'The actual23 passed manifest, selection hash, 1131-proof/9193-theorem audit and all-zero checks are prerequisites. Baseline22 1113 source hashes and exactly18 new files are checked against the frozen snapshot.',
        'All nine named actual wrappers and actual config-v2 wrapper must contain a zero exit code, without conflicting exit-code fields; each supplied paired raw-log field is rehashed. Independent production/config/code peers are required, and the code peer binds this exact helper.',
        'All four working ledgers are rehashed separately from frozen/PUB ledgers; only the exact3 declared Applied unused metadata rows may be removed. Full normalized JSON equality is required, preserving every other body, hypothesis, proof and historical timestamp.',
        'All31 current51 assets are equal ROOT/frozen/PUB. Inventory d746 and browser145/10fresh/135retained with actual browser execution binding are required. Browser mechanics does not imply a new complete manual visual review.',
        'All frozen input hashes and historical source-history aliases are checked. Only six permitted progress fields may differ; proof/theorem totals, correction51 and inventory identity are constrained, coverage_complete remains false.',
        'Publication file names are explicit and checked; absolute, parent traversal, NUL, newline and symlink source paths are rejected. Existing22 prepared files are retained, and an active verification/lean/SafeLearning source must belong to the selected23 proof set.',
        'All dirty, staged and untracked paths must be inside the explicit future whitelist before copying completed extra evidence. After copy, the exact selected bytes and every additional ROOT/PUB hash are checked, and the actual site inclusion budget must remain below900MB.',
        'Exact NUL-separated file names are passed to git add; nonzero git return codes and staged paths outside the whitelist are rejected. New integrity, staging and evidence records use distinct23 paths and assert absence before writing.',
    ],
    'future_inputs_observed_at_code_review': observed,
    'publication_config_unchanged_during_reader_sha256': config_before,
    'scope': 'Code-only independent review of the exact unexecuted draft. This reader does not execute/import the stager, copy publication files, stage Git, mutate owners, claim that absent actual23 outputs passed, or approve an actual Pages/push/live result. Root must execute the genuine prerequisites and final stager; output reviews remain separate.',
    'errors': [], 'coverage_complete': False,
}
with out.open('x') as output:
    output.write(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'], 'report': str(out.relative_to(ROOT)), 'sha256': H(out), 'helper_sha256': H(helper)}))

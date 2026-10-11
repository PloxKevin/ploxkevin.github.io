"""Prepare literal Pages25 exclusions only after genuine audit/export/publication prep.

This draft has future actual execution gates. Authoring it makes no audit,
publication, website build or delivery claim. All old archives remain in Git.
"""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, subprocess

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / 'reports/book/publication-repo'
CFG = PUB / '_config.yml'
REPORT = 'reports/full-coverage/pages25-config-preparation-v2.json'
BACKUP = 'reports/full-coverage/pages25-config-previous-original-v2.yml'
BACKUP_RECORD = 'reports/full-coverage/pages25-config-previous-original-v2.json'
BEFORE = 'f687b33a73defabc3e95085addaa796961f088df8de06f7fc98093a9dc0af523'
BASELINE_MANIFEST = '5e0a58f71b685edbd3bbf7c965a2fda3ffd18f8edfde75c5bf810c7bb63d18e0'
RETIRED_FILES = {
    'reports/full-coverage/checkpoint-19-manifest.json': 'b6ec94fc308b266f2a8a16be156dbbdea8fae7915146ec66fab6375fa2501575',
    'reports/full-coverage/checkpoint-19-selection.json': '9fcf2c8d8785e1b1e98fa482d47a4a4dda2fb5f19ae9d8375e860f32767e4672',
}
RETIRED_DIR = 'reports/full-coverage/lean-checkpoint-23'

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(name): return json.loads((ROOT / name).read_text())
def ref(name): return {'file': name, 'sha256': sha(ROOT / name)}
def zero(record):
    codes = [record[k] for k in ('actual_exit_code', 'exit_code') if k in record]
    assert codes and all(type(c) is int and c == 0 for c in codes)
def actual(stem):
    record = read('reports/full-coverage/' + stem + '-execution-v1.json')
    zero(record)
    assert sha(ROOT / record['log']) == record['log_sha256']
    return record
def tracked_exact(name, files):
    tracked = subprocess.run(['git', 'ls-files', '-z', '--', name], cwd=PUB,
                             check=True, capture_output=True)
    assert {n for n in tracked.stdout.decode().split('\0') if n} == set(files)
    subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', name], cwd=PUB, check=True)
    for n, digest in files.items(): assert sha(ROOT / n) == sha(PUB / n) == digest

assert all(not (ROOT / name).exists() for name in (REPORT, BACKUP, BACKUP_RECORD))
# The original helper and both genuine prewrite failures remain unchanged.
ORIGINAL_HELPER = 'book/coverage/checks/root_prepare_pages25_config_v1.py'
ORIGINAL_HELPER_SHA = '04207875a69824919c74a78d0fc95b415369cbceaab24989815b7b96dafaccad'
ORIGINAL_CODE_PEER = 'book/coverage/checks/pages25-config-helper-independent-modules-review-v1.json'
ORIGINAL_CODE_PEER_SHA = 'ba892a53759813bb42833b41e23d14dc8dc5857c2c923ad2fec14a42daa7342d'
ORIGINAL_FAILURES = {
    'reports/full-coverage/pages25-config-execution-v1.json': 'ef933ee106db20118429b07227486b51b065d7dfb45530f4c7b0beb04df98e97',
    'reports/full-coverage/pages25-config-execution-v2.json': '1f8191e1d5f271b600c08c804131283b70c33341592cc32f941bf1a3f55819cf',
}
assert sha(ROOT / ORIGINAL_HELPER) == ORIGINAL_HELPER_SHA
assert sha(ROOT / ORIGINAL_CODE_PEER) == ORIGINAL_CODE_PEER_SHA
original_peer = read(ORIGINAL_CODE_PEER)
assert 'passed' in original_peer['status'] and original_peer.get('errors', []) == []
assert original_peer['helper_sha256'] == ORIGINAL_HELPER_SHA
original_failed_evidence = {}
for name, digest in ORIGINAL_FAILURES.items():
    assert sha(ROOT / name) == digest
    record = read(name)
    codes = [record[k] for k in ('actual_exit_code', 'exit_code') if k in record]
    assert codes and all(type(c) is int and c == 1 for c in codes)
    assert record['actual_command'] == ['python3', ORIGINAL_HELPER]
    assert record['helper_sha256_before'] == record['helper_sha256_after'] == {ORIGINAL_HELPER: ORIGINAL_HELPER_SHA}
    logs = [record[k] for k in ('log', 'raw_log') if k in record]
    hashes = [record[k] for k in ('log_sha256', 'raw_log_sha256') if k in record]
    assert logs and hashes and all(n == logs[0] for n in logs) and all(h == hashes[0] for h in hashes)
    assert sha(ROOT / logs[0]) == hashes[0]
    original_failed_evidence[name] = digest; original_failed_evidence[logs[0]] = hashes[0]
PREVIOUS_NATIVE = 'reports/full-coverage/pages25-config-preparation-v1.json'
PREVIOUS_NATIVE_SHA = 'ef52945f281b02bc37db3971e2ae8a21f6901cb98f0323b864e825a0e4849104'
PREVIOUS_HELPER = 'book/coverage/checks/root_prepare_pages25_config_v2.py'
PREVIOUS_HELPER_SHA = 'fb5086deddeb83fbca5e1523e6764ee9391f8dc2e8d1c6e0196b4678084402ce'
PREVIOUS_CODE_PEER = 'book/coverage/checks/pages25-config-helper-independent-modules-review-v2.json'
PREVIOUS_CODE_PEER_SHA = '8db37cf8629fadad440d0cac42e9e739fc725c8f2215da52668bff80a2e1ad05'
assert sha(ROOT / PREVIOUS_NATIVE) == PREVIOUS_NATIVE_SHA
previous_native = read(PREVIOUS_NATIVE)
assert previous_native['status'] == 'passed_exact_pages25_archival_configuration_preparation_requires_actual_pages_build'
assert previous_native['config_sha256'] == BEFORE and previous_native['excluded_count'] == 99
assert previous_native['helper'] == {'file': PREVIOUS_HELPER, 'sha256': PREVIOUS_HELPER_SHA}
assert sha(ROOT / PREVIOUS_HELPER) == PREVIOUS_HELPER_SHA
assert sha(ROOT / PREVIOUS_CODE_PEER) == PREVIOUS_CODE_PEER_SHA
previous_peer = read(PREVIOUS_CODE_PEER)
assert 'passed' in previous_peer['status'] and previous_peer.get('errors', []) == []
assert previous_peer['helper_sha256'] == PREVIOUS_HELPER_SHA
previous_execution_name = 'reports/full-coverage/pages25-config-execution-v3.json'
assert sha(ROOT / previous_execution_name) == '450fc68c73585836ebb60b948fb10dbea3c5971d8e1600786c781e590293905b'
previous_execution = read(previous_execution_name); zero(previous_execution)
assert previous_execution['actual_command'] == ['python3', PREVIOUS_HELPER]
assert previous_execution['helper_sha256_before'] == previous_execution['helper_sha256_after'] == {PREVIOUS_HELPER: PREVIOUS_HELPER_SHA}
assert sha(ROOT / previous_execution['log']) == previous_execution['log_sha256']
retained_original_native_files = {
 PREVIOUS_NATIVE: PREVIOUS_NATIVE_SHA,
 'reports/full-coverage/pages25-config-previous-original-v1.yml': '11ac06530cbae6f0c63e84afb63d2a85e60ad6c666899044a50c3b799a293965',
 'reports/full-coverage/pages25-config-previous-original-v1.json': '16b67f4b238d9ee10d04ae353d31f2b4f4648b601bc46035891198f35f937c01'}
for n,h in retained_original_native_files.items(): assert sha(ROOT / n) == h,n
assert sha(CFG) == BEFORE
old = CFG.read_bytes()
exclusions = {line[4:] for line in old.decode().splitlines() if line.startswith('  - ')}
header = '# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'
assert len(exclusions) == 99 and set(previous_native['exclusions']) == exclusions and old.decode() == header + ''.join('  - ' + n + '\n' for n in sorted(exclusions))
assert sha(ROOT / 'reports/full-coverage/checkpoint-24-manifest.json') == BASELINE_MANIFEST
manifest = read('reports/full-coverage/checkpoint-25-manifest.json')
selection = read('reports/full-coverage/checkpoint-25-selection.json')
audit = read('reports/full-coverage/lean-checkpoint-25/verification-original.json')
assert manifest['status'] == 'formal_verification_passed_partial_coverage'
assert manifest['selection_sha256'] == sha(ROOT / 'reports/full-coverage/checkpoint-25-selection.json')
assert len(manifest['proof_files']) == selection['proof_file_count'] == audit['proof_file_count'] == 1156
assert selection['new_file_count'] == 12 and audit['status'] == 'passed' and audit['theorem_count'] == 9369
assert all(type(c['exit_code']) is int and c['exit_code'] == 0 for c in audit['checks'])
assert sum(c.get('evidence_mode') == 'fresh_kernel_replay' for c in audit['checks']) == 12
assert sum(c.get('evidence_mode') == 'reused_identical_module_and_transitive_local_imports' for c in audit['checks']) == 1144
for stem in ('verify-checkpoint25', 'export-checkpoint25', 'prepare-publication25'): actual(stem)
assets = {n: h for n, h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets) == 31
assert assets['SafeLearning/nn-in-the-loop.html'] == '1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'
required = dict(assets)
working_ledgers = {}; published_ledgers = {}
for name, digest in assets.items(): assert sha(ROOT / name) == sha(PUB / name) == digest
for name in ('book/coverage/inventory.json', 'book/coverage/material-corrections.json'):
    digest = manifest['frozen_inputs_sha256'][name]
    assert sha(ROOT / name) == sha(PUB / name) == sha(ROOT / manifest['snapshot'] / name) == digest
    required[name] = digest
assert required['book/coverage/inventory.json'] == '38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
for owner in ('core', 'foundations', 'applied', 'modules'):
    name = 'book/coverage/' + owner + '.json'
    working = manifest['working_inputs_sha256'][name]; frozen = manifest['frozen_inputs_sha256'][name]
    assert sha(ROOT / name) == working and sha(PUB / name) == sha(ROOT / manifest['snapshot'] / name) == frozen
    normalized = copy.deepcopy(read(name)); removed = manifest['excluded_unreferenced_ledger_metadata'][owner]
    baseline_removed = read('reports/full-coverage/checkpoint-24-manifest.json')['excluded_unreferenced_ledger_metadata'][owner]
    assert removed == baseline_removed and len(removed) == (3 if owner == 'applied' else 0)
    for source in removed:
        assert source in normalized['proof_files'] and source not in manifest['proof_files']
        normalized['proof_files'].pop(source)
    assert normalized == json.loads((PUB / name).read_text())
    required[name] = frozen; working_ledgers[name] = working; published_ledgers[name] = frozen
for name in ('reports/full-coverage/integration-25.json', 'reports/full-coverage/browser-checkpoint-25.json',
             'reports/full-coverage/checkpoint-25-manifest.json', 'reports/full-coverage/checkpoint-25-selection.json',
             'reports/full-coverage/lean-checkpoint-25/verification-original.json',
             'reports/full-coverage/lean-checkpoint-25/verification.json', 'reports/full-coverage/lean-checkpoint-25/ledger-audit.json',
             'reports/full-coverage/checkpoint-24-manifest.json', 'reports/full-coverage/checkpoint-24-selection.json',
             'reports/full-coverage/lean-checkpoint-24/verification-original.json'):
    assert sha(ROOT / name) == sha(PUB / name); required[name] = sha(PUB / name)
retired_audit = {p.relative_to(ROOT).as_posix(): sha(p) for p in (ROOT / RETIRED_DIR).rglob('*') if p.is_file()}
assert retired_audit and RETIRED_DIR + '/verification-original.json' in retired_audit
assert {p.relative_to(PUB).as_posix(): sha(p) for p in (PUB / RETIRED_DIR).rglob('*') if p.is_file()} == retired_audit
tracked_exact(RETIRED_DIR, retired_audit)
for name, digest in RETIRED_FILES.items(): tracked_exact(name, {name: digest})
added = set(RETIRED_FILES)
assert not added & exclusions
exclusions.update(added)
assert len(exclusions) == 101
assert all(n and not Path(n).is_absolute() and '..' not in Path(n).parts and not any(c in n for c in '*?[{') for n in exclusions)
def kept(name): return not any(name == e or name.startswith(e + '/') for e in exclusions)
assert all(kept(n) for n in required)
assert all(not kept(n) for n in retired_audit) and all(not kept(n) for n in RETIRED_FILES)
after = (header + ''.join('  - ' + n + '\n' for n in sorted(exclusions))).encode()
included = sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix())) - len(old) + len(after)
audit_fingerprint = hashlib.sha256(json.dumps(retired_audit, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
report = {'status': 'passed_exact_pages25_archival_configuration_preparation_requires_actual_pages_build',
    'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'helper': ref(str(Path(__file__).relative_to(ROOT))),
    'previous_configuration': {'file': BACKUP, 'sha256': BEFORE}, 'config_sha256': hashlib.sha256(after).hexdigest(),
    'exclusions': sorted(exclusions), 'excluded_count': len(exclusions), 'new_literal_exclusions': sorted(added),
    'retired_older_audit_dir': RETIRED_DIR, 'retired_older_audit_file_count': len(retired_audit),
    'retired_older_audit_sorted_exact_path_sha256_map_fingerprint': audit_fingerprint,
    'retired_older_manifest_selection_exact_sha256': RETIRED_FILES,
    'retired_older_archives_exact_in_root_publication_and_tracked_HEAD': True,
    'required_publication_files_sha256': required, 'working_ledger_sha256': working_ledgers,
    'published_frozen_ledger_sha256': published_ledgers, 'exact_original_metadata_removals': manifest['excluded_unreferenced_ledger_metadata'],
    'prospective_included_website_bytes_before_new_native_records': included,
    'selected_sources': 1156, 'public_theorems': 9369, 'all31_source52_assets_exact': True,
    'original_configuration_preparation': {'file': PREVIOUS_NATIVE, 'sha256': PREVIOUS_NATIVE_SHA},
    'entire_original_configuration_preparation_body_and_time': previous_native,
    'retained_original_native_files_sha256': retained_original_native_files,
    'previous_successful_helper': {'file': PREVIOUS_HELPER, 'sha256': PREVIOUS_HELPER_SHA},
    'previous_successful_code_peer': {'file': PREVIOUS_CODE_PEER, 'sha256': PREVIOUS_CODE_PEER_SHA},
    'previous_successful_execution': ref(previous_execution_name),
    'original_prewrite_failed_execution_evidence_sha256': original_failed_evidence,
    'original_helper': {'file': ORIGINAL_HELPER, 'sha256': ORIGINAL_HELPER_SHA},
    'original_code_peer': {'file': ORIGINAL_CODE_PEER, 'sha256': ORIGINAL_CODE_PEER_SHA},
    'coverage_complete': False, 'scope': 'Literal archival website exclusions only. Exact old configuration and retired archives remain in Git. Only the exact older checkpoint19 pair is additionally retired from the already passed 99-exclusion configuration in this version. Current25 and baseline24 manifest, selection and audits remain included. Root working and publication frozen ledgers normalize only the original three declared unused Applied metadata rows. No Pages build or live delivery is inferred.'}
report_bytes = (json.dumps(report, indent=2, ensure_ascii=False) + '\n').encode()
backup_record = {'status': 'original_pages25_initial_configuration_bytes_retained_unchanged',
    'original_configuration': {'file': BACKUP, 'sha256': BEFORE}, 'original_excluded_count': 99,
    'scope': 'Byte preservation only; no new build or delivery.'}
backup_bytes = (json.dumps(backup_record, indent=2) + '\n').encode()
# Account for these later explicitly staged native reports and backup bytes too.
retained_native_replacements = sum((ROOT / n).stat().st_size - ((PUB / n).stat().st_size if (PUB / n).is_file() else 0) for n in retained_original_native_files if kept(n))
prospective = included + retained_native_replacements + len(report_bytes) + len(backup_bytes) + len(old)
assert prospective < 850_000_000, prospective
with (ROOT / BACKUP).open('xb') as out: out.write(old)
assert sha(ROOT / BACKUP) == BEFORE
with (ROOT / BACKUP_RECORD).open('xb') as out: out.write(backup_bytes)
with CFG.open('wb') as out: out.write(after)
with (ROOT / REPORT).open('xb') as out: out.write(report_bytes)
print(json.dumps({'status': report['status'], 'config_sha256': sha(CFG), 'excluded_count': 101,
                  'prospective_included_website_bytes_including_new_native_records': prospective,
                  'selected_sources': 1156, 'public_theorems': 9369, 'coverage_complete': False}))

from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path('/home/oxrexkevin/SafetyBased')
SELF = 'book/coverage/checks/modules_finalize_metadata27_completion_review_v1.py'
HELPER = 'book/coverage/checks/root_finish_metadata27_v1.py'
READER = 'book/coverage/checks/modules-metadata27-staged-completion-reader-v1.json'
EXECUTION = 'book/coverage/checks/modules-metadata27-staged-completion-reader-execution-v1.json'
OUT = 'book/coverage/checks/modules-metadata27-staged-completion-independent-review-v1.json'

def sha(name):
    return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()

assert not (ROOT / OUT).exists()
reader = json.loads((ROOT / READER).read_bytes())
actual = json.loads((ROOT / EXECUTION).read_bytes())
assert reader['status'] == 'passed_independent_metadata27_staged_completion_reader'
assert reader['errors'] == reader['remaining_risks_or_missing_review'] == []
assert reader['helper_sha256'] == sha(HELPER)
assert actual['status'] == 'passed'
assert type(actual['actual_exit_code']) is int and actual['actual_exit_code'] == 0
assert type(actual['actual_runner_exit_code']) is int and actual['actual_runner_exit_code'] == 0
assert actual['protection_errors'] == []
assert actual['actual_command'] == ['python3', 'book/coverage/checks/modules_review_metadata27_completion_v1.py']
assert actual['actual_workdir'] == str(ROOT)
assert actual['helper_sha256_before'] == actual['helper_sha256_after']
assert sha(actual['log']) == actual['log_sha256'] == actual['raw_log_sha256']
evidence = {n: sha(n) for n in (SELF,
    'book/coverage/checks/modules_review_metadata27_completion_v1.py',
    'book/coverage/checks/modules_run_metadata27_completion_review_v1.py',
    READER, EXECUTION, actual['log'])}
assert all((ROOT / n).stat().st_size < 100_000_000 for n in evidence)
peer = {
    'status': 'passed_independent_metadata27_staged_completion_review',
    'errors': [], 'reviewer': '/root/modules_finish28',
    'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
    'helper_sha256': sha(HELPER),
    'actual_reader_execution': {'file': EXECUTION, 'sha256': sha(EXECUTION)},
    'publication_evidence_sha256': evidence,
    'full_finisher_original_delivery5_and_index_guard4_read': True,
    'actual_reader_result': {'file': READER, 'sha256': sha(READER)},
    'actual_real_guard_calls': reader['actual_current_guard_calls'],
    'negative_fixture_count': len(reader['meaningful_negative_fixtures']),
    'all_meaningful_negative_fixtures_rejected': all(r['rejected'] for r in reader['meaningful_negative_fixtures']),
    'only_whitespace_exception': reader['only_exact_whitespace_exception'],
    'original_failed_stage_body_and_time_unchanged': True,
    'actual_staged_blob_count': reader['actual_staged_blob_count'],
    'exact_metadata_paths_checked': len(reader['exact_original_expected_metadata_paths_sha256']),
    'native_all_other_staged_whitespace_check_exit_code': 0,
    'publication_index_HEAD_and_status_unchanged': True,
    'all1175_sources_31_assets_five_owners_unchanged': True,
    'coverage_complete': False,
    'scope': 'Approved exact bounded metadata additions and preservation of the one individually pinned native GitHub push log. This review made no PUB/index changes and does not claim a later metadata commit, push, Pages build or live closure.'
}
with (ROOT / OUT).open('x') as handle:
    handle.write(json.dumps(peer, indent=2) + '\n')
print(json.dumps({'status': peer['status'], 'review': {'file': OUT, 'sha256': sha(OUT),
                  'bytes': (ROOT / OUT).stat().st_size}, 'actual_reader_execution': peer['actual_reader_execution']}))

from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, subprocess, time

ROOT = Path('/home/oxrexkevin/SafetyBased')
HELPER = 'book/coverage/checks/modules_review_metadata27_completion_v1.py'
SELF = 'book/coverage/checks/modules_run_metadata27_completion_review_v1.py'
RECORD = 'book/coverage/checks/modules-metadata27-staged-completion-reader-execution-v1.json'
LOG = 'book/coverage/checks/modules-metadata27-staged-completion-reader-execution-v1.log'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

assert not (ROOT / RECORD).exists() and not (ROOT / LOG).exists()
held = {ROOT / p: sha(ROOT / p) for p in (HELPER, SELF,
    'book/coverage/checks/root_finish_metadata27_v1.py',
    'book/coverage/checks/root_close_publication27_delivery_v5.py',
    'book/coverage/checks/root_finish_staged_publication27_v4.py',
    'reports/full-coverage/checkpoint-27-selection.json',
    'book/coverage/inventory.json', 'book/coverage/material-corrections.json')}
started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
command = ['python3', HELPER]
environment = dict(os.environ)
environment['GIT_OPTIONAL_LOCKS'] = '0'
with (ROOT / LOG).open('xb') as handle:
    result = subprocess.run(command, cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT, env=environment)
finished = datetime.now(timezone.utc).isoformat()
errors = [str(p.relative_to(ROOT)) for p, h in held.items() if sha(p) != h]
body = {'status': 'passed' if result.returncode == 0 and not errors else 'failed',
        'actual_exit_code': result.returncode, 'actual_runner_exit_code': 0 if result.returncode == 0 and not errors else 1,
        'actual_command': command, 'actual_workdir': str(ROOT),
        'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': time.monotonic() - tick,
        'helper_sha256_before': {str(p.relative_to(ROOT)): h for p, h in held.items()},
        'helper_sha256_after': {str(p.relative_to(ROOT)): sha(p) for p in held},
        'log': LOG, 'log_sha256': sha(ROOT / LOG), 'raw_log': LOG, 'raw_log_sha256': sha(ROOT / LOG),
        'read_only_git_environment': {'GIT_OPTIONAL_LOCKS': '0'}, 'protection_errors': errors,
        'publication_index_mutation_commit_push_pages_or_live_mutation_claimed': False}
with (ROOT / RECORD).open('x') as handle:
    handle.write(json.dumps(body, indent=2) + '\n')
print(json.dumps({'status': body['status'], 'actual_exit_code': result.returncode,
                  'execution': {'file': RECORD, 'sha256': sha(ROOT / RECORD)}, 'protection_errors': errors}))
raise SystemExit(body['actual_runner_exit_code'])

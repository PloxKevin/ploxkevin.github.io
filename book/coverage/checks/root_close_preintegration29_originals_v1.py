"""Close exact real Root29 executions, including failed attempts, as history."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT/'book/coverage/checks/future29-core/original-root29-preintegration-native-v1'
RECORDS = [
    'source61-64-contract-preparation29-execution-v1', 'source61-64-corrections-application29-execution-v1',
    'source65-readiness29-execution-v1', 'source65-correction-application29-execution-v1',
    'source65-owner28-tmp-context-preparation29-execution-v1',
    'current65-canonical-plan10-preparation29-execution-v1', 'current65-canonical-pairs10-readiness29-execution-v1',
    'current65-canonical-pairs10-application29-execution-v1',
    'monitoring29-canonical-plan-preparation-execution-v1', 'current65-monitoring29-canonical-pair-application-execution-v1',
    'integration29-source65-static-execution-v1', 'browser29-source65-helper-execution-v1', 'browser29-source65-helper-execution-v2',
    'source65-four-page-math-scroll29-execution-v1', 'source65-four-page-math-scroll29-execution-v2',
    'browser29-evidence-merge-execution-v1']

def path(n):
    p = Path(n) if Path(n).is_absolute() else ROOT/n
    assert '..' not in p.parts and not p.is_symlink() and p.is_file()
    assert p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to('/tmp')
    return p
def sha(n): return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n): return {'file': str(n), 'sha256': sha(n)}

def main():
    assert not BASE.exists()
    inputs = {}; executions = []
    for stem in RECORDS:
        n = 'reports/full-coverage/'+stem+'.json'; d = json.loads(path(n).read_bytes())
        assert type(d['actual_exit_code']) is int and d['helper_sha256_before'] == d['helper_sha256_after']
        assert d['actual_workdir'] == str(ROOT) and d['elapsed_seconds'] >= 0
        inputs[n] = sha(n)
        assert sha(d['log']) == d['log_sha256']; inputs[d['log']] = d['log_sha256']
        for p, h in d['helper_sha256_after'].items(): assert sha(p) == h; inputs[p] = h
        executions.append({'original_native': ref(n), 'actual_exit_code': d['actual_exit_code'], 'original_status': d['status'],
                           'original_actual_command': d['actual_command'], 'original_actual_workdir': d['actual_workdir'],
                           'original_started_at_utc': d['started_at_utc'], 'original_finished_at_utc': d['finished_at_utc']})
    for n in ['/tmp/root_actual_step27_v1.py', '/tmp/root_tmp_lean_current65_owner28_context_v1.json', '/tmp/root_tmp_lean_current65_owner28_runner_v1.py']:
        inputs[n] = sha(n)
    for n in ['reports/full-coverage/browser-source65-29-v2-execution.json', 'reports/full-coverage/browser-source65-29-v2.json',
              'reports/full-coverage/browser-checkpoint-29.json', 'reports/full-coverage/browser-corrections-29-inputs.json',
              'reports/full-coverage/source65-eight-captured-regions-manual-review29-v1.json',
              'reports/full-coverage/source65-four-page-math-scroll29-v1.json', 'reports/full-coverage/source65-four-page-math-scroll29-v2.json']:
        inputs[n] = sha(n)
    aliases = {}
    for n, h in inputs.items():
        p = path(n); target = BASE/'original-closed-bytes'/h/p.name
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists(): assert hashlib.sha256(target.read_bytes()).hexdigest() == h
        else:
            with target.open('xb') as f: f.write(p.read_bytes())
        assert sha(n) == hashlib.sha256(target.read_bytes()).hexdigest() == h
        aliases[n] = {'file': target.relative_to(ROOT).as_posix(), 'sha256': h}
    result = {'status': 'original_root29_preintegration_true_native_bodies_commands_logs_and_times_closed',
              'closed_at_utc': datetime.now(timezone.utc).isoformat(), 'actual_executions': executions, 'aliases': aliases,
              'exact_original_input_count': len(inputs), 'true_failed_attempt_count': sum(r['actual_exit_code'] != 0 for r in executions),
              'scope': 'Historical record only. Original recorded selection26/27 footer fields remain original and are not current65/29 authority. Failed and successful actual exits, bodies, commands, workdirs, warnings and times are unchanged.',
              'coverage_complete': False}
    target = BASE/'original-closed-byte-aliases-v1.json'
    with target.open('xb') as f: f.write((json.dumps(result, indent=2)+'\n').encode())
    print(json.dumps({'status': result['status'], 'closure': ref(target.relative_to(ROOT).as_posix()), 'original_inputs': len(inputs), 'true_failed_attempts': result['true_failed_attempt_count']}))

if __name__ == '__main__': main()

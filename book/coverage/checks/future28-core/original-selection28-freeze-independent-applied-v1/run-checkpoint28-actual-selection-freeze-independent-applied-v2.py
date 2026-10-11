from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time

ROOT = Path('/home/oxrexkevin/SafetyBased')
CHECKER = Path('/tmp/check-checkpoint28-actual-selection-freeze-independent-applied-v2.py')
OUT = Path('/tmp/checkpoint28-actual-selection-freeze-independent-applied-findings-v2.json')
ACTUAL = Path('/tmp/checkpoint28-actual-selection-freeze-independent-applied-actual-v2.json')
LOG = ACTUAL.with_suffix('.log')
assert not any(p.exists() for p in [OUT, ACTUAL, LOG])
def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda: f.read(1024*1024), b''):
            h.update(b)
    return h.hexdigest()
names = ['book/coverage/'+n+'.json' for n in ['core','foundations','applied','applied-promotions','modules']]
names += ['book/coverage/inventory.json','book/coverage/material-corrections.json', 'reports/full-coverage/checkpoint-28-selection.json', 'book/coverage/checks/frozen27-input-content-bindings28-v1.json']
names += [p.relative_to(ROOT).as_posix() for p in (ROOT/'SafeLearning').iterdir() if p.suffix in {'.html','.css','.js'}]
selection = json.loads((ROOT/'reports/full-coverage/checkpoint-28-selection.json').read_bytes())
names += list(selection['proof_files'])
names += ['book/coverage/checks/future28-core/original-selection28-freeze-independent-applied-v1/initial-unverified-checkpoint28-manifest.json','reports/full-coverage/freeze-checkpoint28-execution-v1.json']
before = {n: sha(ROOT/n) for n in names}
helpers = {str(CHECKER): sha(CHECKER), str(Path(__file__)): sha(__file__)}
command = ['/usr/bin/python3', str(CHECKER), '--selection-execution', 'reports/full-coverage/selection28-production-application-execution-v1.json', '--freeze-execution', 'reports/full-coverage/freeze-checkpoint28-execution-v1.json', '--manifest', 'book/coverage/checks/future28-core/original-selection28-freeze-independent-applied-v1/initial-unverified-checkpoint28-manifest.json', '--out', str(OUT)]
started = datetime.now(timezone.utc).isoformat(); tick = time.perf_counter()
process = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
with LOG.open('xb') as f: f.write(process.stdout)
after = {n: sha(ROOT/n) for n in names}
after_helpers = {n: sha(n) for n in helpers}
errors = [n for n in before if before[n] != after[n]] + [n for n in helpers if helpers[n] != after_helpers[n]]
record = {'status':'passed' if process.returncode == 0 and not errors else 'failed', 'actual_exit_code':process.returncode, 'actual_command':command, 'actual_workdir':str(ROOT), 'started_at_utc':started, 'finished_at_utc':datetime.now(timezone.utc).isoformat(), 'elapsed_seconds':time.perf_counter()-tick, 'helper_sha256_before':helpers, 'helper_sha256_after':after_helpers, 'log':str(LOG), 'log_sha256':sha(LOG), 'protection_errors':errors, 'protected_current60_source_proof_and_owner_count':len(before), 'native_producer_or_compiler_executed':False}
with ACTUAL.open('x') as f: json.dump(record, f, indent=2); f.write('\n')
print(json.dumps({'actual':str(ACTUAL),'actual_exit_code':process.returncode,'protection_errors':errors,'raw':str(LOG),'elapsed_seconds':record['elapsed_seconds']}))
raise SystemExit(process.returncode or bool(errors))

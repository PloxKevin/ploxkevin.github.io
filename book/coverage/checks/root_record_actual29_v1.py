"""Record a real Root command, its binary output and unchanged helper bytes."""
from pathlib import Path
from datetime import datetime, timezone
import sys, json, subprocess, time, hashlib

ROOT = Path(__file__).resolve().parents[3]
def safe(n):
    p = Path(n)
    assert not p.is_absolute() and '..' not in p.parts and p.as_posix() == n
    p = ROOT/p
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    return p
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file': p.relative_to(ROOT).as_posix(), 'sha256': sha(p)}

name, command = sys.argv[1], json.loads(sys.argv[2])
helpers = json.loads(sys.argv[3]) if len(sys.argv) > 3 else []
assert type(command) is list and command and all(type(x) is str for x in command)
assert type(helpers) is list and all(type(x) is str for x in helpers)
record = safe(name); log = record.with_suffix('.log')
assert not record.exists() and not log.exists()
record.parent.mkdir(parents=True, exist_ok=True)
baseline = safe('reports/full-coverage/checkpoint-28-selection.json')
baseline_before = ref(baseline)
selection = safe('reports/full-coverage/checkpoint-29-selection.json')
selection_before = ref(selection) if selection.exists() else None
before = {n: sha(safe(n)) for n in helpers}
started = datetime.now(timezone.utc).isoformat(); tick = time.monotonic()
with log.open('xb') as output:
    process = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
after = {n: sha(safe(n)) for n in helpers}
passed = process.returncode == 0 and before == after and ref(baseline) == baseline_before
result = dict(status='passed' if passed else 'failed', actual_exit_code=process.returncode,
    actual_command=command, actual_workdir=str(ROOT), started_at_utc=started,
    finished_at_utc=datetime.now(timezone.utc).isoformat(), elapsed_seconds=time.monotonic()-tick,
    helper_sha256_before=before, helper_sha256_after=after,
    log=log.relative_to(ROOT).as_posix(), log_sha256=sha(log),
    recorder=ref(Path(__file__)), baseline_selection=baseline_before,
    selection29_before=selection_before, selection29_after=ref(selection) if selection.exists() else None,
    scope='Actual command execution only. Selection references identify exact bytes; no unexecuted compiler or delivery success is inferred.')
with record.open('x') as output: output.write(json.dumps(result, indent=2)+'\n')
print(json.dumps(result))
raise SystemExit(0 if passed else 1)

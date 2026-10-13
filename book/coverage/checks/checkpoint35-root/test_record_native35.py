"""Exercise the actual recorder in isolated roots; retain a JSON command report."""
from pathlib import Path
import argparse
import contextlib
import hashlib
import importlib.util
import io
import json
import os
import signal
import subprocess
import sys
import tempfile
import time
import traceback

HERE = Path(__file__).resolve().parent
RECORDER = HERE / 'record_native35.py'
CHILD = '''from pathlib import Path
import os, signal, subprocess, sys, time
counter=Path(sys.argv[2])
counter.write_text(str(int(counter.read_text())+1) if counter.exists() else "1")
mode=sys.argv[1]
if mode=="raw":
 os.write(1,b"native stdout\\x00\\xff\\n")
 os.write(2,b"native stderr\\n")
elif mode=="fail":
 print("native failure",flush=True)
 raise SystemExit(7)
elif mode=="mutate":
 Path(sys.argv[3]).write_bytes(b"changed by actual child\\n")
elif mode=="selfsignal":
 os.kill(os.getpid(),signal.SIGTERM)
elif mode in ("slow","tree"):
 descendant=None
 if mode=="tree":
  descendant=subprocess.Popen([sys.executable,"-B","-c","import time; time.sleep(60)"])
 Path(sys.argv[3]).write_text(str(os.getpid())+" "+str(descendant.pid if descendant else 0))
 print("native ready",flush=True)
 time.sleep(60)
else:
 raise SystemExit("bad test mode")
'''


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def eventually(predicate, message):
    deadline = time.monotonic() + 10
    while time.monotonic() < deadline:
        if predicate():
            return
        time.sleep(0.02)
    raise AssertionError(message)


def alive(pid):
    try:
        # A terminated orphan may remain a zombie until its outside parent reaps it.
        return Path('/proc', str(pid), 'stat').read_text().split(') ', 1)[1][0] != 'Z'
    except FileNotFoundError:
        return False


class Fixture:
    def __init__(self, root, events):
        self.root, self.events = root, events
        self.script = root / 'book/coverage/checks/checkpoint35-root/record_native35.py'
        self.script.parent.mkdir(parents=True)
        self.script.write_bytes(RECORDER.read_bytes())
        self.native = root / 'native_fixture.py'
        self.native.write_text(CHILD)
        self.input = root / 'input.txt'
        self.input.write_bytes(b'original fixture input\n')
        (root / '.lake/packages/mathlib').mkdir(parents=True)
        self.counter = root / 'counter.txt'
        self.processes, self.groups = [], []

    def argv(self, name='attempt', mode='raw', cwd='.', inputs=None, tail=()):
        inputs = ['native_fixture.py', 'input.txt'] if inputs is None else inputs
        argv = [sys.executable, '-B', str(self.script), '--record', 'receipts/' + name + '.json', '--cwd', cwd]
        for item in inputs:
            argv.extend(['--input', item])
        return argv + ['--', sys.executable, '-B', str(self.native), mode, str(self.counter), *map(str, tail)]

    def run(self, argv, expected):
        p = subprocess.run(argv, cwd=self.root, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=15)
        self.events.append(dict(actual_command=argv, actual_workdir=str(self.root), actual_exit_code=p.returncode,
            stdout=p.stdout.decode(), stderr=p.stderr.decode()))
        assert p.returncode == expected, (p.returncode, expected, p.stdout, p.stderr)
        return json.loads(p.stdout)

    def start(self, argv):
        p = subprocess.Popen(argv, cwd=self.root, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.processes.append((p, argv))
        return p

    def collect(self, p, expected):
        stdout, stderr = p.communicate(timeout=10)
        argv = next(argv for process, argv in self.processes if process is p)
        self.events.append(dict(actual_command=argv, actual_workdir=str(self.root), actual_exit_code=p.returncode,
            stdout=stdout.decode(), stderr=stderr.decode()))
        assert p.returncode == expected, (p.returncode, expected, stdout, stderr)
        return json.loads(stdout) if stdout else None

    def receipt(self, name='attempt'):
        return self.root / 'receipts' / (name + '.json')

    def cleanup(self):
        for group in self.groups:
            try:
                os.killpg(group, signal.SIGKILL)
            except ProcessLookupError:
                pass
        for p, _ in self.processes:
            if p.poll() is None:
                p.kill()
            p.wait()


def completed_replay(f):
    argv = f.argv(cwd='.lake/packages/mathlib')
    assert f.run(argv, 0)['reused'] is False
    receipt, original = f.receipt(), f.receipt().read_bytes()
    d = json.loads(original)
    assert d['actual_command'] == argv[argv.index('--') + 1:]
    assert d['actual_workdir'] == str(f.root / '.lake/packages/mathlib')
    assert d['helper_sha256_before'] == d['helper_sha256_after']
    assert set(d['helper_sha256_before']) == {'native_fixture.py', 'input.txt', f.script.relative_to(f.root).as_posix()}
    assert receipt.with_suffix('.log').read_bytes() == b'native stdout\x00\xff\nnative stderr\n'
    assert d['log_sha256'] == sha(receipt.with_suffix('.log'))
    assert d['started_receipt_sha256'] == sha(receipt.with_suffix('.started.json'))
    assert f.run(argv, 0)['reused'] is True
    assert receipt.read_bytes() == original and f.counter.read_text() == '1'


def failures_preserved(f):
    argv = f.argv(mode='fail')
    f.run(argv, 7)
    original = f.receipt().read_bytes()
    assert json.loads(original)['actual_exit_code'] == 7
    assert f.run(argv, 7)['reused'] is True
    assert f.counter.read_text() == '1' and f.receipt().read_bytes() == original
    f.run(f.argv(name='retry', mode='fail'), 7)
    assert f.counter.read_text() == '2' and f.receipt().read_bytes() == original
    f.run(f.argv(name='native-signal', mode='selfsignal'), 143)
    d = json.loads(f.receipt('native-signal').read_bytes())
    assert d['status'] == 'failed' and d['actual_exit_code'] == -signal.SIGTERM and d['interruption_signal'] is None


def corruption_rejected(f):
    argv = f.argv()
    f.run(argv, 0)
    receipt, original = f.receipt(), f.receipt().read_bytes()
    for p in (receipt.with_suffix('.log'), receipt.with_suffix('.started.json'), f.input, f.native, f.script):
        before = p.read_bytes()
        p.write_bytes(before + (b'\n# injected fixture corruption\n' if p.suffix == '.py' else b'corruption\n'))
        try:
            f.run(argv, 65)
            assert receipt.read_bytes() == original and f.counter.read_text() == '1'
        finally:
            p.write_bytes(before)
    for changed in (f.argv(mode='fail'), f.argv(cwd='.lake/packages/mathlib'), f.argv(inputs=['native_fixture.py'])):
        f.run(changed, 65)
    d = json.loads(original)
    d['actual_exit_code'] = 9
    receipt.write_text(json.dumps(d))
    f.run(argv, 65)
    receipt.write_bytes(original)
    assert f.run(argv, 0)['reused'] is True and f.counter.read_text() == '1'


def mutation_failed(f):
    argv = f.argv(mode='mutate', tail=(f.input,))
    f.run(argv, 1)
    d = json.loads(f.receipt().read_bytes())
    assert d['status'] == 'failed' and d['actual_exit_code'] == 0
    assert d['helper_sha256_before'] != d['helper_sha256_after']
    assert f.run(argv, 1)['reused'] is True and f.counter.read_text() == '1'


def concurrent_and_interrupted(f):
    ready = f.root / 'ready.txt'
    argv = f.argv(mode='tree', tail=(ready,))
    p = f.start(argv)
    eventually(ready.exists, 'native child never became ready')
    child, descendant = map(int, ready.read_text().split())
    f.groups.append(child)
    f.run(argv, 75)
    assert f.counter.read_text() == '1' and not f.receipt().exists()
    p.send_signal(signal.SIGTERM)
    f.collect(p, 143)
    eventually(lambda: not alive(child) and not alive(descendant), 'interrupted process group still alive')
    original = f.receipt().read_bytes()
    d = json.loads(original)
    assert d['status'] == 'interrupted' and d['actual_exit_code'] == -signal.SIGTERM
    assert d['interruption_signal'] == signal.SIGTERM and d['log_bytes'] > 0
    assert f.run(argv, 143)['reused'] is True
    assert f.receipt().read_bytes() == original and f.counter.read_text() == '1'


def hard_kill_refuses_restart(f):
    ready = f.root / 'ready.txt'
    argv = f.argv(mode='slow', tail=(ready,))
    p = f.start(argv)
    eventually(ready.exists, 'native child never became ready')
    child = int(ready.read_text().split()[0])
    f.groups.append(child)
    p.kill()
    f.collect(p, -signal.SIGKILL)
    assert not f.receipt().exists() and f.receipt().with_suffix('.started.json').exists()
    f.run(argv, 75)  # The real child still owns the inherited lock.
    os.killpg(child, signal.SIGKILL)
    eventually(lambda: not alive(child), 'killed native child still alive')
    started = f.receipt().with_suffix('.started.json').read_bytes()
    log = f.receipt().with_suffix('.log').read_bytes()
    f.run(argv, 65)
    assert f.counter.read_text() == '1' and not f.receipt().exists()
    assert f.receipt().with_suffix('.started.json').read_bytes() == started
    assert f.receipt().with_suffix('.log').read_bytes() == log
    f.run(f.argv(name='retry'), 0)
    assert f.counter.read_text() == '2'
    orphan = f.receipt('orphan').with_suffix('.log')
    orphan.write_bytes(b'preserved unclosed attempt\n')
    f.run(f.argv(name='orphan'), 65)
    assert orphan.read_bytes() == b'preserved unclosed attempt\n'


def before_final_injection(f):
    spec = importlib.util.spec_from_file_location('recorder_fixture', f.script)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    original_atomic = m.atomic_new

    def fail_final(p, value):
        if p == f.receipt():
            raise OSError('injected interruption before final receipt publication')
        return original_atomic(p, value)

    m.atomic_new = fail_final
    argv = f.argv()
    output = io.StringIO()
    with contextlib.redirect_stdout(output):
        code = m.main(argv[3:])
    f.events.append(dict(actual_command=argv, actual_workdir=str(f.root), actual_exit_code=code,
        invocation='actual main with injected final-publication OSError', stdout=output.getvalue()))
    assert code == 74 and not f.receipt().exists()
    assert f.receipt().with_suffix('.started.json').exists() and f.receipt().with_suffix('.log').stat().st_size > 0
    f.run(argv, 65)
    assert f.counter.read_text() == '1'
    f.run(f.argv(name='retry'), 0)


def active_log_and_paths_rejected(f):
    for protected in ['receipts/attempt.log', 'receipts/attempt.json', 'receipts/attempt.started.json', 'receipts/attempt.lock', '../escape', '.git/config']:
        f.run(f.argv(inputs=[protected]), 64)
    f.run(f.argv(cwd='/'), 64)
    (f.root / 'escaped').symlink_to('/tmp', target_is_directory=True)
    f.run(f.argv(cwd='escaped'), 64)
    assert not f.counter.exists()
    f.run(f.argv(), 0)


def spawn_failure(f):
    argv = f.argv()
    argv[argv.index('--') + 1:] = ['/nonexistent-checkpoint35-native-executable']
    f.run(argv, 127)
    d = json.loads(f.receipt().read_bytes())
    assert d['status'] == 'spawn_failed' and d['actual_exit_code'] is None and not d['child_started']
    assert f.run(argv, 127)['reused'] is True and not f.counter.exists()


CASES = (completed_replay, failures_preserved, corruption_rejected, mutation_failed,
         concurrent_and_interrupted, hard_kill_refuses_restart, before_final_injection,
         active_log_and_paths_rejected, spawn_failure)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    report = Path(args.report).resolve()
    if report.exists():
        raise SystemExit('Existing test report preserved; use a new report filename')
    before = {p.name: sha(p) for p in (RECORDER, Path(__file__).resolve())}
    cases = []
    for case in CASES:
        events, error = [], None
        with tempfile.TemporaryDirectory(prefix='checkpoint35-native-fixture-') as temporary:
            f = Fixture(Path(temporary), events)
            try:
                case(f)
            except Exception:
                error = traceback.format_exc()
            finally:
                f.cleanup()
        cases.append(dict(case=case.__name__, status='passed' if error is None else 'failed',
            actual_commands=events, **({'error': error} if error else {})))
    after = {p.name: sha(p) for p in (RECORDER, Path(__file__).resolve())}
    code = 0 if all(c['status'] == 'passed' for c in cases) and before == after else 1
    value = dict(status='passed' if code == 0 else 'failed', actual_exit_code=code,
        actual_command=[sys.executable, '-B', str(Path(__file__).resolve()), *sys.argv[1:]],
        actual_workdir=str(Path.cwd()), helper_sha256_before=before, helper_sha256_after=after,
        fixtures='isolated ephemeral synthetic roots; no production proofs, owners, sources or selection modified', cases=cases)
    report.parent.mkdir(parents=True, exist_ok=True)
    with report.open('x') as output:
        json.dump(value, output, indent=2)
        output.write('\n')
        output.flush()
        os.fsync(output.fileno())
    print(json.dumps(dict(status=value['status'], cases=len(cases), failed_cases=[c['case'] for c in cases if c['status'] != 'passed'], report=str(report))))
    return code


if __name__ == '__main__':
    raise SystemExit(main())

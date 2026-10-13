"""Record one native attempt; verify completed attempts without executing again.

Usage: python3 -B record_native35.py --record ROOT/attempt.json --cwd .
       --input ROOT/input ... -- executable argument ...
All paths before -- are root relative. The log is raw merged stdout/stderr.
Started receipts and logs without a final receipt require a new attempt name.
"""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import fcntl
import hashlib
import json
import os
import signal
import subprocess
import sys
import tempfile
import time

SELF = Path(__file__).resolve()
ROOT = SELF.parents[4]
SCHEMA = 'checkpoint35.native-command.v1'
SIGNALS = (signal.SIGINT, signal.SIGTERM, signal.SIGHUP, signal.SIGQUIT)


class Refusal(Exception):
    def __init__(self, message, code=65):
        super().__init__(message)
        self.code = code


def path(name, *, directory=False, record=False):
    p = Path(name)
    if not isinstance(name, str) or not name or len(name) > 4096:
        raise Refusal('Invalid root-relative path', 64)
    if p.is_absolute() or p.as_posix() != name or '..' in p.parts or '.git' in p.parts:
        raise Refusal('Path must be canonical and root relative: ' + name, 64)
    if name == '.' and not directory or record and '.lake' in p.parts:
        raise Refusal('Invalid record/input path: ' + name, 64)
    p = ROOT / p
    if not p.resolve().is_relative_to(ROOT):
        raise Refusal('Path escapes ROOT: ' + name, 64)
    for item in (p, *p.parents):
        if item.is_relative_to(ROOT) and item.is_symlink():
            raise Refusal('Symlink path is not a bound input/output: ' + name, 64)
    if directory and not p.is_dir():
        raise Refusal('Working directory does not exist: ' + name, 64)
    return p


def digest(p):
    if not p.is_file():
        raise Refusal('Not a regular input/log: ' + str(p.relative_to(ROOT)))
    with p.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def fsync_dir(p):
    fd = os.open(p, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def atomic_new(p, value):
    """Publish complete, durable JSON atomically, without replacing any receipt."""
    data = (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()
    fd, temporary = tempfile.mkstemp(prefix='.' + p.name + '-', dir=p.parent)
    try:
        with os.fdopen(fd, 'wb') as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.link(temporary, p)  # Atomic publication with no existing-file overwrite.
        fsync_dir(p.parent)
    finally:
        os.unlink(temporary)


def hashes(names, *, strict=False):
    result, errors = {}, {}
    for name in names:
        try:
            result[name] = digest(path(name))
        except (OSError, Refusal) as error:
            if strict:
                raise Refusal('Cannot bind input ' + name + ': ' + str(error)) from error
            result[name] = None
            errors[name] = str(error)
    return result, errors


def read(p):
    if not p.is_file() or p.stat().st_size > 2_000_000:
        raise Refusal('Missing or oversized receipt: ' + p.name)
    try:
        value = json.loads(p.read_bytes())
    except (ValueError, OSError) as error:
        raise Refusal('Unreadable receipt: ' + p.name) from error
    if not isinstance(value, dict):
        raise Refusal('Receipt must contain an object: ' + p.name)
    return value


def outcome(record):
    status, raw = record.get('status'), record.get('actual_exit_code')
    if raw is not None and (type(raw) is not int or not -127 <= raw <= 255):
        raise Refusal('Invalid native exit code')
    if status == 'interrupted':
        received = record.get('interruption_signal')
        if type(received) is not int or received not in SIGNALS:
            raise Refusal('Invalid interruption signal')
        return 128 + received
    if record.get('interruption_signal') is not None:
        raise Refusal('Non-interrupted receipt contains an interruption signal')
    if status == 'spawn_failed' and raw is None and not record.get('child_started') and record.get('spawn_error'):
        return 127
    if status == 'recorder_failed' and record.get('recorder_error'):
        return 70
    if status not in {'passed', 'failed'} or type(raw) is not int or not record.get('child_started'):
        raise Refusal('Receipt has no completed native outcome')
    stable = record['helper_sha256_before'] == record['helper_sha256_after'] and not record['binding_errors_after']
    expected = 'passed' if raw == 0 and stable else 'failed'
    if status != expected:
        raise Refusal('Receipt status disagrees with actual native outcome/bindings')
    return (raw if raw >= 0 else 128 - raw) or (0 if stable else 1)


def replay(record, started, log, request, names):
    value = read(record)
    for key, expected in request.items():
        if value.get(key) != expected:
            raise Refusal('Completed receipt request differs: ' + key)
    initial = read(started)
    for key, expected in request.items():
        if initial.get(key) != expected:
            raise Refusal('Started receipt request differs: ' + key)
    if initial.get('status') != 'started' or value.get('started_receipt_sha256') != digest(started):
        raise Refusal('Started receipt integrity differs')
    if initial.get('helper_sha256_before') != value.get('helper_sha256_before'):
        raise Refusal('Started and final bound input hashes differ')
    if set(value.get('helper_sha256_before', {})) != set(names) or set(value.get('helper_sha256_after', {})) != set(names):
        raise Refusal('Completed bound input names differ')
    current, errors = hashes(names)
    if errors or current != value['helper_sha256_after']:
        raise Refusal('Completed recorder/protected input bytes differ')
    if value.get('log_sha256') != digest(log) or value.get('log_bytes') != log.stat().st_size:
        raise Refusal('Completed raw log integrity differs')
    code = outcome(value)
    if value.get('recorder_exit_code') != code:
        raise Refusal('Saved recorder exit code disagrees with actual outcome')
    return value, code


def kill_group(process, sig):
    if process is not None:
        try:
            os.killpg(process.pid, sig)
        except ProcessLookupError:
            pass


def execute(record, started, log, request, names, lock_fd):
    before, _ = hashes(names, strict=True)
    tick = time.monotonic()
    initial = {**request, 'status': 'started', 'started_at_utc': datetime.now(timezone.utc).isoformat(),
               'runner_pid': os.getpid(), 'helper_sha256_before': before}
    process, received, spawn_error, recorder_error, raw = None, None, None, None, None

    def interrupted(sig, frame):
        nonlocal received
        received = received or sig
        kill_group(process, sig)

    old_handlers = {sig: signal.signal(sig, interrupted) for sig in SIGNALS}
    try:
        fd = os.open(log, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
        with os.fdopen(fd, 'wb') as output:
            output.flush()
            os.fsync(output.fileno())
            fsync_dir(log.parent)
            atomic_new(started, initial)
            if received is None:
                try:
                    process = subprocess.Popen(request['actual_command'], cwd=request['actual_workdir'],
                        stdout=output, stderr=subprocess.STDOUT, start_new_session=True,
                        pass_fds=(lock_fd,))
                except OSError as error:
                    spawn_error = str(error)
                if process is not None:
                    stopping = None
                    try:
                        while True:
                            if received is not None:
                                if stopping is None:
                                    stopping = time.monotonic()
                                    kill_group(process, received)
                                elif time.monotonic() - stopping > 2:
                                    kill_group(process, signal.SIGKILL)
                            try:
                                raw = process.wait(timeout=0.1)
                                break
                            except subprocess.TimeoutExpired:
                                pass
                    except Exception as error:
                        recorder_error = type(error).__name__ + ': ' + str(error)
                        kill_group(process, signal.SIGKILL)
                        raw = process.wait()
                    if received is not None:
                        kill_group(process, signal.SIGKILL)  # Include surviving descendants.
            output.flush()
            os.fsync(output.fileno())
        after, errors = hashes(names)
        status = ('interrupted' if received is not None else 'spawn_failed' if spawn_error is not None
                  else 'recorder_failed' if recorder_error is not None
                  else 'passed' if raw == 0 and before == after and not errors else 'failed')
        value = {**initial, 'status': status, 'finished_at_utc': datetime.now(timezone.utc).isoformat(),
            'elapsed_seconds': time.monotonic() - tick, 'actual_exit_code': raw,
            'child_started': process is not None, 'interruption_signal': received,
            'helper_sha256_after': after, 'binding_errors_after': errors,
            'log_sha256': digest(log), 'log_bytes': log.stat().st_size,
            'started_receipt_sha256': digest(started)}
        if spawn_error is not None:
            value['spawn_error'] = spawn_error
        if recorder_error is not None:
            value['recorder_error'] = recorder_error
        value['recorder_exit_code'] = outcome(value)
        atomic_new(record, value)
        return value, value['recorder_exit_code']
    finally:
        # A receipt-write failure still must not leave an active child behind.
        if process is not None and process.poll() is None:
            kill_group(process, signal.SIGKILL)
            process.wait()
        for sig, handler in old_handlers.items():
            signal.signal(sig, handler)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', required=True)
    parser.add_argument('--cwd', default='.')
    parser.add_argument('--input', action='append', default=[])
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    lock_fd = None
    try:
        if not args.command or args.command[0] != '--' or len(args.command) == 1:
            raise Refusal('Expected -- followed by native argv', 64)
        command = args.command[1:]
        if len(command) > 1024 or sum(map(len, command)) > 131072 or len(args.input) > 256:
            raise Refusal('Command/protected input count exceeds bounded limits', 64)
        record, cwd = path(args.record, record=True), path(args.cwd, directory=True)
        if record.suffix != '.json':
            raise Refusal('Record filename must end in .json', 64)
        started, log, lock = record.with_suffix('.started.json'), record.with_suffix('.log'), record.with_suffix('.lock')
        active = {args.record, *(p.relative_to(ROOT).as_posix() for p in (started, log, lock))}
        inputs = sorted(set(args.input))
        if active.intersection(inputs):
            raise Refusal('The attempt receipt/log/lock cannot be its own protected input', 64)
        for name in inputs:
            path(name)
        names = sorted(set(inputs) | {SELF.relative_to(ROOT).as_posix()})
        request = dict(schema=SCHEMA, actual_command=command, actual_workdir=str(cwd),
            protected_input_names=inputs, recorder=SELF.relative_to(ROOT).as_posix(),
            log=log.relative_to(ROOT).as_posix(), started_receipt=started.relative_to(ROOT).as_posix())
        record.parent.mkdir(parents=True, exist_ok=True)
        for p in (record, started, log, lock):
            path(p.relative_to(ROOT).as_posix(), record=True)
        lock_fd = os.open(lock, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
        try:
            fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise Refusal('Attempt is still locked by a native recorder/child', 75) from error
        reused = record.exists()
        if reused:
            value, code = replay(record, started, log, request, names)
        else:
            if started.exists() or log.exists():
                raise Refusal('Incomplete attempt preserved; use a new record filename')
            value, code = execute(record, started, log, request, names, lock_fd)
        print(json.dumps(dict(status=value['status'], record=args.record, reused=reused,
            actual_exit_code=value['actual_exit_code'], recorder_exit_code=code), separators=(',', ':')))
        return code
    except (Refusal, OSError, KeyError, TypeError, ValueError) as error:
        code = error.code if isinstance(error, Refusal) else 74
        print(json.dumps(dict(status='refused', record=args.record, error=str(error), recorder_exit_code=code), separators=(',', ':')))
        return code
    finally:
        if lock_fd is not None:
            os.close(lock_fd)


if __name__ == '__main__':
    raise SystemExit(main())

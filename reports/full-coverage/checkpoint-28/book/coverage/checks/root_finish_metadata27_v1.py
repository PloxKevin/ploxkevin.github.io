"""Check the actual staged delivery metadata and preserve the native push log.

The previous staging execution remains failed. Only the individually hashed
GitHub push log is excluded from whitespace lint; its original bytes remain.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, importlib.util, json, re

ROOT = Path('/home/oxrexkevin/SafetyBased')
SELF = 'book/coverage/checks/root_finish_metadata27_v1.py'
FAILED = 'reports/full-coverage/publication27-delivery-metadata-stage-execution-v1.json'
NATIVE = 'reports/full-coverage/publication27-delivery-metadata-prestage-v1.json'
LOG = 'reports/full-coverage/publication27-content-push-execution-v1.log'
LOG_SHA = '289ccd457f2fb72a8508e42685881bb1dcd9e5d8ae2c964e9dd87da1e9dacd5f'
REPORT = 'reports/full-coverage/publication27-delivery-metadata-staged-completion-v1.json'

def module(name, file):
    spec = importlib.util.spec_from_file_location(name, ROOT / file)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value

d = module('metadata27_original_delivery', 'book/coverage/checks/root_close_publication27_delivery_v5.py')
s = module('metadata27_original_index_check', 'book/coverage/checks/root_finish_staged_publication27_v4.py')

def guard():
    assert d.sha(ROOT / d.SELF) == 'f09f881b61313f847be329410eaabfc9d26a99bbd498a297229adb74bef3c561'
    assert d.sha(ROOT / s.SELF) == '1dd2fb895b1776eed921145db20b16053e6a67105fba18981545e49fa8da4951'
    assert d.sha(d.safe(NATIVE)) == '029c39996d6dc2630d2366ac83322d41240ad6b76d0fbfe80105e41f3c75dde6'
    assert d.sha(d.safe(FAILED)) == '4087fb816c984616cceb1a7c5b184dfec313c11a829c1dc54c92463a3fabcef8'
    assert not d.safe(REPORT).exists() and not d.safe(REPORT, d.PUB).exists()
    content, run, _ = d.delivery()
    native, failed = d.read(NATIVE), d.read(FAILED)
    assert native['status'] == 'passed_explicit_completed27_delivery_metadata'
    assert native['content_commit'] == content == '8607bd45ce4a4c81697c5ac92aa1e554ea5c16b6'
    assert native['pages_run'] == run and native['coverage_complete'] is False
    assert failed['status'] == 'failed' and type(failed['actual_exit_code']) is int and failed['actual_exit_code'] == 1
    assert failed['actual_command'] == ['python3', d.SELF, 'stage', '--supplement', native['supplement']['file'], '--supplement-sha', native['supplement']['sha256'], '--apply']
    assert failed['actual_workdir'] == str(ROOT)
    assert failed['helper_sha256_before'] == failed['helper_sha256_after'] == {d.SELF: d.sha(ROOT / d.SELF)}
    assert d.sha(d.safe(failed['log'])) == failed['log_sha256']
    assert "Command '['git', 'diff', '--cached', '--check']' returned non-zero exit status 2." in d.safe(failed['log']).read_text()
    expected = {**native['paths_sha256'], NATIVE: d.sha(d.safe(NATIVE))}
    assert len(expected) == 56
    for n, h in expected.items():
        d.metadata(n)
        assert d.sha(d.safe(n)) == d.sha(d.safe(n, d.PUB)) == h
    names = s.staged()
    assert names and names <= expected.keys()
    assert not s.git(['diff', '--name-only', '-z']).stdout
    for row in s.git(['status', '--porcelain', '-z', '--untracked-files=all']).stdout.decode().split('\0'):
        if row:
            assert row[:2] in ('M ', 'A ') and row[3:] in names
    s.index_exact(names)
    lint = s.git(['diff', '--cached', '--check'], check=False)
    assert lint.returncode == 2 and not lint.stderr
    lines = lint.stdout.decode().splitlines()
    assert len(lines) == 16 and LOG in names
    for i in range(8):
        assert lines[2*i] == f'{LOG}:{i+1}: trailing whitespace.'
        assert lines[2*i+1].startswith('+remote:')
    assert d.sha(d.safe(LOG)) == d.sha(d.safe(LOG, d.PUB)) == LOG_SHA
    scoped = ['diff', '--cached', '--check', '--', '.', ':(literal,exclude)' + LOG]
    clean = s.git(scoped)
    assert not clean.stdout and not clean.stderr
    return native, failed, expected, names, scoped

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--review', required=True)
    parser.add_argument('--review-sha256', required=True)
    args = parser.parse_args()
    assert Path(__file__).resolve() == ROOT / SELF
    native, failed, expected, names, scoped = guard()
    peer = d.read(args.review)
    assert d.sha(d.safe(args.review)) == args.review_sha256
    assert peer['status'] == 'passed_independent_metadata27_staged_completion_review'
    assert peer['errors'] == [] and peer['helper_sha256'] == d.sha(d.safe(SELF))
    reader = peer['actual_reader_execution']
    extras = dict(peer['publication_evidence_sha256'])
    assert extras[reader['file']] == reader['sha256']
    d.zero(d.read(reader['file']))
    extras.update({SELF: d.sha(d.safe(SELF)), args.review: args.review_sha256,
                   FAILED: d.sha(d.safe(FAILED)), failed['log']: failed['log_sha256']})
    for n, h in extras.items():
        d.metadata(n)
        assert d.sha(d.safe(n)) == h and d.safe(n).stat().st_size < 100_000_000
    report = {'status': 'passed_exact_metadata27_staged_bytes_and_native_push_log_preservation',
              'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'helper_sha256': d.sha(d.safe(SELF)), 'content_commit': native['content_commit'],
              'original_failed_stage': d.ref(FAILED), 'original_failed_stage_body_and_time_unchanged': True,
              'staged_paths_before_completion': len(names), 'exact_native_push_log': {'file': LOG, 'sha256': LOG_SHA},
              'archival_diagnostics': 8, 'actual_remaining_whitespace_check_command': ['git', *scoped],
              'actual_remaining_whitespace_check_exit_code': 0, 'additional_evidence_sha256': extras,
              'coverage_complete': False, 'metadata_commit_push_pages_and_live_pending': True}
    payload = d.encoded(report)
    # All additions are bounded metadata; use the unchanged exact133 config.
    config = d.safe('_config.yml', d.PUB).read_text()
    assert d.sha(d.safe('_config.yml', d.PUB)) == 'cc1f0f9cf93b0d9ffdff6e422bfb6b85f073e4efb0d705378adc32a46a40af23'
    excluded = [line[4:] for line in config.splitlines()[2:]]
    assert len(excluded) == len(set(excluded)) == 133
    kept = lambda n: not any(n == e or n.startswith(e+'/') for e in excluded)
    total = sum(p.stat().st_size for p in d.PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(d.PUB).parts and kept(p.relative_to(d.PUB).as_posix()))
    delta = sum(d.safe(n).stat().st_size - (d.safe(n, d.PUB).stat().st_size if d.safe(n, d.PUB).is_file() else 0) for n in extras if kept(n))
    assert 0 <= total + delta + len(payload) < 850_000_000
    for n, h in extras.items():
        p = d.safe(n, d.PUB); p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(d.safe(n).read_bytes()); assert d.sha(p) == h
    with d.safe(REPORT).open('xb') as f:
        f.write(payload)
    d.safe(REPORT, d.PUB).write_bytes(payload)
    s.git(['add', '-f', '--', *sorted({*extras, REPORT})])
    final = s.staged()
    assert names <= final <= expected.keys() | extras.keys() | {REPORT}
    s.index_exact(final)
    assert not s.git(scoped).stdout
    assert not s.git(['diff', '--name-only', '-z']).stdout
    for n, h in {**expected, **extras, REPORT: d.sha(d.safe(REPORT))}.items():
        assert d.sha(d.safe(n, d.PUB)) == h
    print(json.dumps({'status': 'passed', 'staged_paths': len(final), 'native_log_exceptions': 1, 'coverage_complete': False}))

if __name__ == '__main__':
    main()

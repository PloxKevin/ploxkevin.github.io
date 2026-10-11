"""Verify the staged checkpoint27 and preserve exact archival whitespace.

The failed staging execution stays failed. This separate completion checks
every staged blob and excludes only individually pinned historical files
from Git's whitespace lint. It does not commit, push, or claim delivery.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, re, subprocess

ROOT = Path('/home/oxrexkevin/SafetyBased')
PUB = ROOT / 'reports/book/publication-repo'
SELF = 'book/coverage/checks/root_finish_staged_publication27_v2.py'
PLAN = 'book/coverage/checks/future27-core/root-explicit-audited27-publication-stage-plan-v3.json'
FAILED = 'reports/full-coverage/stage-publication27-execution-v3.json'
NATIVE = 'reports/full-coverage/publication27-prestage-v1.json'
REPORT = 'reports/full-coverage/publication27-staged-byte-and-archival-whitespace-completion-v1.json'

def safe(n, base=ROOT):
    assert type(n) is str and n and str(Path(n)) == n
    assert not Path(n).is_absolute() and '..' not in Path(n).parts
    assert not any(c in n for c in '\0\n\r*?[')
    p = base / n
    assert p.resolve().is_relative_to(base.resolve()) and not p.is_symlink()
    return p

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def read(n):
    return json.loads(safe(n).read_bytes())

def git(args, data=None, check=True):
    return subprocess.run(['git', *args], cwd=PUB, input=data,
                          capture_output=True, check=check)

def staged():
    return {n.decode() for n in git(['diff', '--cached', '--name-only', '-z']).stdout.split(b'\0') if n}

def index_exact(names):
    entries = {}
    for row in git(['ls-files', '--stage', '-z']).stdout.split(b'\0'):
        if not row:
            continue
        header, name = row.split(b'\t', 1)
        mode, oid, stage = header.split()
        assert stage == b'0'
        entries[name.decode()] = (mode, oid.decode())
    ordered = sorted(names)
    for n in ordered:
        p = safe(n, PUB)
        assert p.is_file() and p.stat().st_size < 100_000_000
        assert entries[n][0] in (b'100644', b'100755')
    raw = git(['hash-object', '--stdin-paths', '--no-filters'],
              ''.join(str(safe(n, PUB)) + '\n' for n in ordered).encode()).stdout.decode().splitlines()
    assert len(raw) == len(ordered)
    assert all(entries[n][1] == oid for n, oid in zip(ordered, raw))

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--review', required=True)
    parser.add_argument('--review-sha256', required=True)
    args = parser.parse_args()
    assert Path(__file__).resolve() == ROOT / SELF
    assert not safe(REPORT).exists() and not safe(REPORT, PUB).exists()
    assert sha(safe(PLAN)) == '3c07e15e716470f64b9ceb7e07931d87c60b9623c6562498aa15ce0830274ca3'
    plan, failed, native = map(read, (PLAN, FAILED, NATIVE))
    assert type(failed['actual_exit_code']) is int and failed['actual_exit_code'] == 1
    assert failed['status'] == 'failed'
    assert failed['actual_command'] == ['python3', 'book/coverage/checks/root_stage_publication27_v7.py', '--plan', PLAN]
    assert failed['actual_workdir'] == str(ROOT)
    assert failed['helper_sha256_before'] == failed['helper_sha256_after'] == {plan['helper']['file']: plan['helper']['sha256']}
    assert sha(safe(failed['log'])) == failed['log_sha256']
    old_log = safe(failed['log']).read_text()
    assert "Command '['git', 'diff', '--cached', '--check']' returned non-zero exit status 2." in old_log
    assert native['status'] == 'passed_explicit_audited_checkpoint27_publication_whitelist_ready_to_stage'
    assert native['coverage_complete'] is False and native['publication_still_awaits_actual_commit_push_pages_and_live_checks'] is True
    assert (native['sources'], native['public_theorems'], native['new_sources']) == (1175, 9644, 8)
    expected = native['additional_closed_paths_sha256']
    assert all(sha(safe(n)) == sha(safe(n, PUB)) == h for n, h in expected.items())
    assert sha(safe('_config.yml', PUB)) == native['config_sha256']
    allowed = set(native['staged_paths'])
    names = staged()
    assert names and names <= allowed
    assert not git(['diff', '--name-only', '-z']).stdout
    for row in git(['status', '--porcelain', '-z', '--untracked-files=all']).stdout.decode().split('\0'):
        if row:
            assert row[:2] in ('M ', 'A ') and row[3:] in names, row
    index_exact(names)
    # Only the exact original whitespace diagnostics may be exempted. No live
    # HTML or selected Lean source is eligible for this archival exception.
    current = git(['diff', '--cached', '--check'], check=False)
    assert current.returncode == 2 and not current.stderr
    assert old_log.startswith(current.stdout.decode())
    violations = {}
    lines = current.stdout.decode().splitlines()
    assert len(lines) % 2 == 0
    for i in range(0, len(lines), 2):
        match = re.fullmatch(r'(.+):([0-9]+): (trailing whitespace\.|new blank line at EOF\.|space before tab in indent\.)', lines[i])
        assert match and lines[i+1].startswith('+'), lines[i]
        n = match.group(1)
        safe(n)
        assert n in names and not n.startswith(('SafeLearning/', 'verification/lean/'))
        assert n.endswith('.log') or '/source-history/' in n or '/original-documentation27-foundations-review-v1/' in n
        assert n in allowed
        assert sha(safe(n)) == sha(safe(n, PUB)), n
        violations.setdefault(n, []).append({'line': int(match.group(2)), 'kind': match.group(3)})
    assert len(violations) == 99 and sum(map(len, violations.values())) == 389
    pinned = {n: {'sha256': sha(safe(n, PUB)), 'diagnostics': rows} for n, rows in sorted(violations.items())}
    scoped = ['diff', '--cached', '--check', '--', '.', *[':(literal,exclude)' + n for n in sorted(violations)]]
    clean = git(scoped)
    assert not clean.stdout and not clean.stderr
    review = read(args.review)
    assert sha(safe(args.review)) == args.review_sha256
    assert review['status'] == 'passed_independent_full_checkpoint27_staged_completion_code_review'
    assert review['errors'] == [] and review['helper_sha256'] == sha(safe(SELF))
    extras = dict(review['publication_evidence_sha256'])
    extras.update({SELF: sha(safe(SELF)), args.review: args.review_sha256, FAILED: sha(safe(FAILED)), failed['log']: failed['log_sha256']})
    for n, h in extras.items():
        safe(n, PUB)
        assert n.startswith(('book/coverage/checks/', 'reports/full-coverage/'))
        assert sha(safe(n)) == h and safe(n).stat().st_size < 100_000_000
    config = read('reports/full-coverage/pages27-supplemental-archive-configuration-v1.json')
    excluded = config['exclusions']
    assert config['config_sha256'] == native['config_sha256'] and len(excluded) == 133
    kept = lambda n: not any(n == e or n.startswith(e + '/') for e in excluded)
    total = 0
    for p in PUB.rglob('*'):
        n = p.relative_to(PUB).as_posix()
        if '.git' in p.relative_to(PUB).parts or not kept(n):
            continue
        assert not p.is_symlink(), n
        if p.is_file():
            total += p.stat().st_size
    delta = sum(safe(n).stat().st_size - (safe(n, PUB).stat().st_size if safe(n, PUB).is_file() else 0) for n in extras if kept(n))
    report = {'status': 'passed_exact_staged_checkpoint27_bytes_and_scoped_archival_whitespace',
              'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'helper_sha256': sha(safe(SELF)), 'original_failed_stage': {'file': FAILED, 'sha256': sha(safe(FAILED))},
              'original_failed_stage_body_and_time_unchanged': True,
              'staged_blob_count_checked_before_completion': len(names),
              'exact_immutable_archival_whitespace_files': pinned,
              'additional_exact_failed_stage_raw_log_exception': {'file': failed['log'], 'sha256': failed['log_sha256']},
              'archival_diagnostic_count': 389, 'actual_remaining_whitespace_check_command': ['git', *scoped],
              'actual_remaining_whitespace_check_exit_code': 0,
              'included_website_bytes_before_completion': total, 'additional_publication_evidence_sha256': extras,
              'coverage_complete': False, 'actual_commit_push_pages_and_live_checks_pending': True}
    payload = (json.dumps(report, indent=2) + '\n').encode()
    assert 0 <= total + delta + (len(payload) if kept(REPORT) else 0) < 850_000_000
    for n, h in extras.items():
        p = safe(n, PUB)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(safe(n).read_bytes())
        assert sha(p) == h
    with safe(REPORT).open('xb') as f:
        f.write(payload)
    safe(REPORT, PUB).write_bytes(payload)
    completion = set(extras) | {REPORT}
    git(['add', '-f', '--', *sorted(completion)])
    final = staged()
    assert names <= final <= allowed | completion
    index_exact(final)
    # Added review/helper/report bytes must also pass the same scoped lint.
    final_scoped = [*scoped, ':(literal,exclude)' + failed['log']]
    assert sha(safe(failed['log'], PUB)) == failed['log_sha256']
    assert not git(final_scoped).stdout
    assert not git(['diff', '--name-only', '-z']).stdout
    for n, h in extras.items():
        assert sha(safe(n, PUB)) == h
    print(json.dumps({'status': 'passed', 'staged_paths': len(final), 'archival_files': 100,
                      'remaining_whitespace_check_exit_code': 0, 'coverage_complete': False}))

if __name__ == '__main__':
    main()

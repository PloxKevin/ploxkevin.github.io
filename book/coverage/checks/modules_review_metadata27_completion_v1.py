"""Independent read-only review of the actual checkpoint27 metadata finisher."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, importlib.util, json, subprocess

ROOT = Path('/home/oxrexkevin/SafetyBased')
SELF = 'book/coverage/checks/modules_review_metadata27_completion_v1.py'
HELPER = 'book/coverage/checks/root_finish_metadata27_v1.py'
OUT = 'book/coverage/checks/modules-metadata27-staged-completion-reader-v1.json'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def ref(p):
    return {'file': str(p.relative_to(ROOT)), 'sha256': sha(p), 'bytes': p.stat().st_size}

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

assert not (ROOT / OUT).exists()
started = datetime.now(timezone.utc).isoformat()
f = load('independent_modules_metadata27_finisher', ROOT / HELPER)
d, s = f.d, f.s
selected = json.loads((ROOT / 'reports/full-coverage/checkpoint-27-selection.json').read_bytes())
assert selected['proof_file_count'] == len(selected['proof_files']) == 1175
held = {ROOT / n: row['sha256'] for n, row in selected['proof_files'].items()}
held.update({p: sha(p) for p in (ROOT / 'SafeLearning').glob('*') if p.is_file()})
held.update({ROOT / 'book/coverage' / n: sha(ROOT / 'book/coverage' / n)
             for n in ('modules.json', 'core.json', 'foundations.json', 'applied.json', 'applied-promotions.json',
                       'inventory.json', 'material-corrections.json', 'progress.json')})
for n in (SELF, HELPER, d.SELF, s.SELF, f.FAILED, f.NATIVE, f.LOG,
          'reports/full-coverage/checkpoint-27-selection.json', 'reports/full-coverage/README.md'):
    held[ROOT / n] = sha(ROOT / n)
pub = d.PUB
index_path = pub / '.git/index'
index_before = sha(index_path)
head_before = s.git(['rev-parse', 'HEAD']).stdout
status_before = s.git(['status', '--porcelain', '-z', '--untracked-files=all']).stdout
for p, h in held.items():
    assert sha(p) == h

# This is the real guard: native delivery, actual remote HEAD, 56 exact paths,
# current staged blobs, eight pinned native diagnostics and scoped native lint.
native, failed, expected, names, scoped = f.guard()
assert len(expected) == 56 and not (ROOT / f.REPORT).exists()
assert not (pub / f.REPORT).exists()
expected_pub = {pub / n: h for n, h in expected.items()}
delivery_original = d.delivery
delivery_validated = delivery_original()
read_original, sha_original, git_original, staged_original = d.read, d.sha, s.git, s.staged
fixtures = []

def restore():
    d.delivery = lambda: delivery_validated
    d.read, d.sha, s.git, s.staged = read_original, sha_original, git_original, staged_original

def reject(name, setup):
    restore()
    setup()
    try:
        f.guard()
    except (AssertionError, subprocess.CalledProcessError, KeyError) as error:
        fixtures.append({'fixture': name, 'rejected': True, 'exception_type': type(error).__name__,
                         'scope': 'Isolated in-memory mutation of guard inputs; real files/index untouched.'})
    else:
        raise AssertionError('Guard accepted negative fixture: ' + name)
    finally:
        restore()

def alter_record(path, change):
    def read_fixture(n):
        value = copy.deepcopy(read_original(n))
        if n == path:
            change(value)
        return value
    d.read = read_fixture

def changed_git(command, transform):
    def git_fixture(args, data=None, check=True):
        result = git_original(args, data=data, check=check)
        if args == command:
            return transform(result)
        return result
    s.git = git_fixture

def cp(r, stdout=None, returncode=None, stderr=None):
    return subprocess.CompletedProcess(r.args, r.returncode if returncode is None else returncode,
                                      r.stdout if stdout is None else stdout,
                                      r.stderr if stderr is None else stderr)

reject('failed native exit boolean must not count as integer one',
       lambda: alter_record(f.FAILED, lambda x: x.update(actual_exit_code=True)))
reject('historical failed status cannot be upgraded',
       lambda: alter_record(f.FAILED, lambda x: x.update(status='passed')))
reject('historical staging command must match exact native command',
       lambda: alter_record(f.FAILED, lambda x: x.update(actual_command=['python3', d.SELF, 'stage'])))
reject('historical helper after-hash must retain identity',
       lambda: alter_record(f.FAILED, lambda x: x.update(helper_sha256_after={d.SELF: '0' * 64})))
reject('historical raw log hash must retain identity',
       lambda: alter_record(f.FAILED, lambda x: x.update(log_sha256='0' * 64)))
reject('coverage cannot silently become complete',
       lambda: alter_record(f.NATIVE, lambda x: x.update(coverage_complete=True)))
reject('metadata content commit must match actual delivered commit',
       lambda: alter_record(f.NATIVE, lambda x: x.update(content_commit='0' * 40)))
reject('exact prospective whitelist must contain all 56 paths',
       lambda: alter_record(f.NATIVE, lambda x: x['paths_sha256'].pop(next(iter(x['paths_sha256'])))))
reject('HTML outside metadata whitelist cannot be staged',
       lambda: setattr(s, 'staged', lambda: staged_original() | {'SafeLearning/lipsdp.html'}))
reject('unstaged worktree change cannot be concealed',
       lambda: changed_git(['diff', '--name-only', '-z'], lambda r: cp(r, stdout=b'unexpected.txt\0')))
reject('untracked publication file is rejected',
       lambda: changed_git(['status', '--porcelain', '-z', '--untracked-files=all'],
                           lambda r: cp(r, stdout=r.stdout + b'?? unexpected.txt\0')))

def index_edit(r, field, value):
    lines = r.stdout.split(b'\0')
    target = next(i for i, line in enumerate(lines) if line and line.split(b'\t', 1)[1].decode() in names)
    header, path = lines[target].split(b'\t', 1)
    fields = header.split()
    fields[field] = value
    lines[target] = b' '.join(fields) + b'\t' + path
    return cp(r, stdout=b'\0'.join(lines))

reject('symlink index mode is rejected',
       lambda: changed_git(['ls-files', '--stage', '-z'], lambda r: index_edit(r, 0, b'120000')))
reject('unmerged index stage is rejected',
       lambda: changed_git(['ls-files', '--stage', '-z'], lambda r: index_edit(r, 2, b'1')))
reject('staged blob must equal actual worktree bytes',
       lambda: changed_git(['ls-files', '--stage', '-z'], lambda r: index_edit(r, 1, b'0' * 40)))
reject('native push log may not change under whitespace exception',
       lambda: setattr(d, 'sha', lambda p: '0' * 64 if Path(p) in (ROOT / f.LOG, pub / f.LOG) else sha_original(p)))
reject('whitespace exception cannot move to another file',
       lambda: changed_git(['diff', '--cached', '--check'],
                           lambda r: cp(r, stdout=r.stdout.replace(f.LOG.encode(), b'SafeLearning/lipsdp.html', 1))))
reject('only native remote diagnostic continuation is accepted',
       lambda: changed_git(['diff', '--cached', '--check'],
                           lambda r: cp(r, stdout=r.stdout.replace(b'+remote:', b'+invented:', 1))))
reject('a ninth whitespace diagnostic is rejected',
       lambda: changed_git(['diff', '--cached', '--check'],
                           lambda r: cp(r, stdout=r.stdout + b'unexpected.txt:1: trailing whitespace.\n+bad \n')))
reject('remaining files must pass scoped whitespace lint',
       lambda: changed_git(scoped, lambda r: cp(r, stdout=b'unexpected.txt:1: trailing whitespace.\n+bad \n', returncode=2)))
restore()
d.delivery = delivery_original
assert len(fixtures) == 19 and all(x['rejected'] for x in fixtures)
# A second genuine guard confirms that fixtures left no altered module state.
native2, failed2, expected2, names2, scoped2 = f.guard()
assert (native2, failed2, expected2, names2, scoped2) == (native, failed, expected, names, scoped)
for p, h in {**held, **expected_pub}.items():
    assert sha(p) == h, str(p)
assert sha(index_path) == index_before
assert s.git(['rev-parse', 'HEAD']).stdout == head_before
assert s.git(['status', '--porcelain', '-z', '--untracked-files=all']).stdout == status_before
assert not (ROOT / f.REPORT).exists() and not (pub / f.REPORT).exists()
result = {
    'status': 'passed_independent_metadata27_staged_completion_reader', 'errors': [],
    'reviewer': '/root/modules_finish28', 'started_at_utc': started,
    'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
    'helper_sha256': sha(ROOT / HELPER),
    'full_helpers_read': [ref(ROOT / n) for n in (HELPER, d.SELF, s.SELF)],
    'actual_current_guard_calls': 2, 'actual_remote_and_local_content_commit': native['content_commit'],
    'exact_original_expected_metadata_paths_sha256': expected,
    'actual_staged_paths': sorted(names), 'actual_staged_blob_count': len(names),
    'native_scoped_whitespace_command': ['git', *scoped], 'native_scoped_whitespace_exit_code': 0,
    'only_exact_whitespace_exception': {'file': f.LOG, 'sha256': f.LOG_SHA, 'native_diagnostics': 8},
    'original_failed_stage': ref(ROOT / f.FAILED),
    'original_failed_stage_body_and_time_preserved': True,
    'meaningful_negative_fixtures': fixtures,
    'protected_selected_sources': 1175, 'protected_source_assets': 31, 'protected_owners': 5,
    'all_current_source_owner_progress_selection_metadata_bytes_unchanged': True,
    'publication_index_sha256_before_after': index_before,
    'publication_HEAD_and_status_unchanged': True,
    'remaining_risks_or_missing_review': [],
    'semantic_decision': 'Approved for exact bounded metadata additions only. The individually pinned original native push log is preserved, original failed stage stays failed, all other staged bytes pass native lint. Final metadata commit/push/Pages/live checks remain Root work.',
    'canonical_publication_index_commit_push_or_source_changes_made': False,
    'coverage_complete': False
}
with (ROOT / OUT).open('x') as handle:
    handle.write(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'reader': ref(ROOT / OUT), 'negative_fixtures_rejected': len(fixtures)}))

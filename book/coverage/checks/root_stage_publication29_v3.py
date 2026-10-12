"""Check exact audited checkpoint29 publication bytes and stage an explicit list."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, re, subprocess
import root_prepare_checkpoint29_documents_v1 as docs

ROOT = Path('/home/oxrexkevin/SafetyBased')
PUB = ROOT/'reports/book/publication-repo'
HEAD = 'fa1e92e55ea0b8fac9ba30ef2b0450b5e5281702'
REPORT = 'reports/full-coverage/publication29-staged-byte-check-v3.json'

def safe(root, n):
    assert type(n) is str and n and Path(n).as_posix() == n
    assert not Path(n).is_absolute() and '..' not in Path(n).parts
    assert not any(c in n for c in '\0\n\r*?[')
    p = root/n
    assert p.resolve().is_relative_to(root) and not p.is_symlink()
    return p

def sha(root, n):
    return hashlib.sha256(safe(root, n).read_bytes()).hexdigest()

def read(root, n):
    return json.loads(safe(root, n).read_bytes())

def checked(r):
    assert set(r) == {'file', 'sha256'} and sha(ROOT, r['file']) == r['sha256']
    return read(ROOT, r['file'])

def git(args, data=None, check=True):
    return subprocess.run(['git', *args], cwd=PUB, input=data, capture_output=True, check=check)

def website_size():
    exclusions = [line[4:] for line in safe(PUB, '_config.yml').read_text().splitlines() if line.startswith('  - ')]
    assert len(exclusions) == len(set(exclusions)) == 177
    total = 0
    for p in PUB.rglob('*'):
        n = p.relative_to(PUB).as_posix()
        if '.git' in p.relative_to(PUB).parts or any(n == e or n.startswith(e+'/') for e in exclusions):
            continue
        assert not p.is_symlink(), n
        if p.is_file(): total += p.stat().st_size
    return total

def prepare(plan_name, plan_sha):
    assert re.fullmatch('[0-9a-f]{64}', plan_sha) and sha(ROOT, plan_name) == plan_sha
    plan = read(ROOT, plan_name)
    docs.readiness()
    helper_names = [
        'book/coverage/checks/root_prepare_checkpoint29_documents_v1.py',
        'book/coverage/checks/root_copy_publication29_supplements_v2.py',
        'book/coverage/checks/root_prepare_publication29_stage_plan_v3.py',
        'book/coverage/checks/root_stage_publication29_v3.py']
    helper_inputs = {n: sha(ROOT, n) for n in helper_names}
    assert plan['helper_inputs_sha256'] == helper_inputs
    staging_peer = checked(plan['independent_staging_helper_review'])
    assert staging_peer['errors'] == [] and staging_peer['status'].startswith('passed_')
    assert staging_peer['reviewed_helpers_sha256'] == helper_inputs
    pages_peer = checked(plan['independent_pages_helper_review'])
    assert pages_peer['errors'] == [] and pages_peer['status'].startswith('passed_')
    configuration = checked(plan['configuration_preparation'])
    config_helper = configuration['helper']
    assert re.fullmatch(r'book/coverage/checks/root_prepare_pages29_config_v[1-9][0-9]*\.py', config_helper['file'])
    assert sha(ROOT, config_helper['file']) == config_helper['sha256']
    assert pages_peer['helper'] == config_helper
    audit_peer = checked(plan['independent_actual_audit_review'])
    assert audit_peer['errors'] == [] and audit_peer['status'].startswith('passed_')
    assert audit_peer['unchanged_exported_original_report'] == plan['original_audit']
    assert plan['status'] == 'explicit_actual_audited_checkpoint29_publication_plan'
    assert git(['rev-parse', 'HEAD']).stdout.decode().strip() == HEAD == plan['baseline_publication_head']
    assert not git(['diff', '--cached', '--name-only', '-z']).stdout
    manifest = checked(plan['manifest']); selection = checked(plan['selection']); audit = checked(plan['original_audit'])
    assert manifest['status'] == 'formal_verification_passed_partial_coverage' and manifest['coverage_complete'] is False
    assert manifest['proof_files'] == selection['proof_files'] and audit['proof_sha256'] == {n: r['sha256'] for n, r in selection['proof_files'].items()}
    assert len(selection['proof_files']) == len(manifest['proof_files']) == 1197 and selection['new_file_count'] == 11
    baseline_name = 'reports/full-coverage/checkpoint-28-selection.json'
    assert sha(ROOT, baseline_name) == docs.PRIOR_SELECTION
    baseline = read(ROOT, baseline_name)['proof_files']
    assert len(baseline) == 1186 and set(baseline) <= set(selection['proof_files'])
    assert all(selection['proof_files'][n]['sha256'] == r['sha256'] for n, r in baseline.items())
    added = set(selection['proof_files']) - set(baseline)
    assert len(added) == 11 and len([d for d in audit['declarations'] if d['file'] in added]) == 218
    assert audit['status'] == 'passed' and audit['proof_file_count'] == selection['proof_file_count'] == 1197 and audit['theorem_count'] == 10114
    assert manifest['successful_verification']['report_sha256'] == plan['original_audit']['sha256']
    assert len(audit['declarations']) == len({d['name'] for d in audit['declarations']}) == len(audit['axiom_dependencies']) == 10114
    assert {d['name'] for d in audit['declarations']} == set(audit['axiom_dependencies'])
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert set(audit['allowed_standard_axioms']) == allowed and all(set(a) <= allowed for a in audit['axiom_dependencies'].values())
    for c in audit['checks']:
        codes = [c[k] for k in ['exit_code', 'actual_exit_code', 'actual_runner_exit_code'] if k in c]
        assert codes and all(type(v) is int and v == 0 for v in codes)
        commands = [c[k] for k in ['command', 'actual_command'] if k in c]
        assert commands and all(type(v) is list and v == commands[0] for v in commands)
        cwds = [c[k] for k in ['cwd', 'workdir', 'working_directory', 'actual_workdir'] if k in c]
        assert all(type(v) is str and v == cwds[0] for v in cwds)
        assert 'status' not in c or c['status'] == 'passed'
    assert sum(c.get('evidence_mode') == 'fresh_kernel_replay' for c in audit['checks']) == 11
    assert sum(c.get('evidence_mode') == 'reused_identical_module_and_transitive_local_imports' for c in audit['checks']) == 1186
    prerequisites = {
        'verify-checkpoint29-execution-v1': ['python3', 'reports/full-coverage/checkpoint-29/verification/lean/verify.py', '--reuse-kernel-from', str(ROOT/'reports/full-coverage/checkpoint-28')],
        'export-checkpoint29-execution-v1': ['python3', 'book/coverage/export_audit29_v1.py', '--snapshot', 'reports/full-coverage/checkpoint-29', '--output', 'reports/full-coverage/lean-checkpoint-29'],
        'export-integrity29-execution-v1': ['python3', 'book/coverage/checks/root_check_export29_integrity_v1.py'],
        'static-checkpoint29-execution-v1': ['python3', 'book/validate28_v1.py', '--allow-reviewed-corrections', '--output', 'reports/full-coverage/integration-29.json'],
        'frozen-ledger-checkpoint29-execution-v1': ['python3', 'reports/full-coverage/checkpoint-29/book/coverage/validate.py', '--output', 'reports/full-coverage/lean-checkpoint-29/ledger-audit.json'],
        'prepare-publication29-execution-v1': ['python3', 'book/coverage/prepare_publication.py', '29'],
        'publication29-ledger-check-execution-v1': ['python3', 'reports/book/publication-repo/book/coverage/validate.py', '--output', 'reports/full-coverage/publication-checks/ledger-checkpoint-29.json'],
        'pages29-config-application-execution-v2': ['python3', config_helper['file'], '--apply'],
        'prepare-documents29-execution-v1': ['python3', 'book/coverage/checks/root_prepare_checkpoint29_documents_v1.py']}
    assert set(plan['actual_prerequisites']) == set(prerequisites)
    for key, command in prerequisites.items():
        r = plan['actual_prerequisites'][key]
        assert r['file'] == 'reports/full-coverage/'+key+'.json'
        d = checked(r)
        assert d['status'] == 'passed'
        codes = [d[k] for k in ['actual_exit_code', 'exit_code', 'actual_runner_exit_code'] if k in d]
        assert codes and all(type(v) is int and v == 0 for v in codes)
        commands = [d[k] for k in ['command', 'actual_command'] if k in d]
        assert commands and all(v == command for v in commands)
        cwds = [d[k] for k in ['cwd', 'workdir', 'working_directory', 'actual_workdir'] if k in d]
        assert cwds and all(v == str(ROOT) for v in cwds)
        logs = [d[k] for k in ['log', 'raw_log'] if k in d]
        hashes = [d[k] for k in ['log_sha256', 'raw_log_sha256'] if k in d]
        assert logs and hashes and all(v == logs[0] for v in logs) and all(v == hashes[0] for v in hashes)
        assert sha(ROOT, logs[0]) == hashes[0]
        assert d['helper_sha256_before'] == d['helper_sha256_after'] == {command[1]: sha(ROOT, command[1])}
    frozen = manifest['frozen_inputs_sha256']
    prepared = checked(plan['prepared_file_list'])
    assert type(prepared) is list and prepared and len(prepared) == len(set(prepared))
    extra = plan['supplementary_paths_sha256']
    assert plan_name not in extra
    overrides = {'book/coverage/progress.json', 'reports/full-coverage/README.md'}
    expected = {}
    for n in prepared:
        if n in overrides:
            h = extra[n]
        elif n in frozen:
            h = frozen[n]
        elif n.startswith('reports/full-coverage/checkpoint-29/reports/full-coverage/source-history/'):
            h = frozen[n.removeprefix('reports/full-coverage/checkpoint-29/')]
        else:
            h = sha(ROOT, n)
        assert sha(PUB, n) == h, n
        expected[n] = h
    for n, h in extra.items():
        assert sha(ROOT, n) == sha(PUB, n) == h, n
        assert n not in expected or expected[n] == h
        expected[n] = h
    assert sha(PUB, plan_name) == plan_sha
    expected[plan_name] = plan_sha
    assert set(frozen) <= set(expected)
    for n, r in selection['proof_files'].items():
        assert sha(ROOT, n) == sha(PUB, n) == r['sha256']
    assets = {n: h for n, h in frozen.items() if n.startswith('SafeLearning/')}
    assert len(assets) == 31
    assert all(sha(ROOT, n) == sha(PUB, n) == h for n, h in assets.items())
    for domain in ['core', 'foundations', 'applied', 'modules', 'applied-promotions']:
        n = 'book/coverage/'+domain+'.json'
        assert sha(ROOT, n) == manifest['working_inputs_sha256'][n]
        assert sha(PUB, n) == frozen[n]
    progress = read(PUB, 'book/coverage/progress.json')
    assert progress['publication_status'] == 'prepared_source_exact_checkpoint_29_awaiting_delivery'
    assert progress['verified_checkpoint']['coverage_complete'] is False
    assert progress['working_next_checkpoint_preparation']['exercise_counts'] == {'complete': 526, 'partial': 11, 'pending': 19}
    assert progress['working_next_checkpoint_preparation']['material_review_units'] == {'reviewed': 4663, 'pending': 8111}
    publedger = checked(plan['publication_ledger'])
    assert publedger['integrity_status'] == 'passed' and publedger['errors'] == [] and publedger['mathematical_coverage_complete'] is False
    assert publedger['inventory_sha256'] == frozen['book/coverage/inventory.json']
    for d in publedger['domains']:
        assert d['ledger_sha256'] == frozen['book/coverage/'+d['domain']+'.json']
    config = checked(plan['configuration_preparation'])
    assert config['status'] == 'passed_exact_pages29_archival_configuration_requires_actual_pages_and_live_checks'
    assert config['website_budget_bytes'] == 850000000
    actual_exclusions = [line[4:] for line in safe(PUB, '_config.yml').read_text().splitlines() if line.startswith('  - ')]
    assert actual_exclusions == config['exclusions'] == sorted(set(actual_exclusions))
    assert config['excluded_count'] == len(actual_exclusions) == 177 and config['included_website_bytes_including_configuration_evidence'] < 850000000
    assert sha(PUB, '_config.yml') == config['config_sha256']
    expected['_config.yml'] = config['config_sha256']
    assert config['exact_selected_lean_sources_in_git_archive_sha256'] == audit['proof_sha256']
    for n, h in config['required_publication_files_sha256'].items():
        assert expected[n] == h
    assert not safe(ROOT, REPORT).exists() and not safe(PUB, REPORT).exists()
    for row in git(['status', '--porcelain', '-z', '--untracked-files=all']).stdout.decode().split('\0'):
        if row:
            assert row[:2] in (' M', '??') and row[3:] in expected, row
    assert all(safe(PUB, n).stat().st_size < 100000000 for n in expected)
    assert website_size() < 850000000
    return expected, plan

def stage(plan_name, plan_sha):
    expected, plan = prepare(plan_name, plan_sha)
    git(['--literal-pathspecs', 'add', '-f', '--pathspec-from-file=-', '--pathspec-file-nul'], b'\0'.join(n.encode() for n in sorted(expected))+b'\0')
    names = {n.decode() for n in git(['diff', '--cached', '--name-only', '-z']).stdout.split(b'\0') if n}
    assert names and names <= set(expected) and not git(['diff', '--name-only', '-z']).stdout
    entries = {}
    for row in git(['ls-files', '--stage', '-z']).stdout.split(b'\0'):
        if row:
            header, n = row.split(b'\t', 1); mode, oid, index_stage = header.split()
            assert index_stage == b'0'
            entries[n.decode()] = (mode, oid.decode())
    ordered = sorted(names)
    oids = git(['hash-object', '--stdin-paths', '--no-filters'], ''.join(str(safe(PUB, n))+'\n' for n in ordered).encode()).stdout.decode().splitlines()
    assert len(oids) == len(ordered)
    assert all(entries[n][0] in (b'100644', b'100755') and entries[n][1] == oid for n, oid in zip(ordered, oids))
    lint = git(['diff', '--cached', '--check'], check=False)
    assert lint.returncode in (0, 2) and not lint.stderr
    violations = {}; lines = lint.stdout.decode().splitlines(); i = 0
    while i < len(lines):
        m = re.fullmatch(r'(.+):([0-9]+): (trailing whitespace\.|new blank line at EOF\.|space before tab in indent\.)', lines[i])
        assert m, lines[i]; i += 1
        if m.group(3) != 'new blank line at EOF.':
            assert i < len(lines) and lines[i].startswith('+'); i += 1
        n = m.group(1)
        assert n in names and not n.startswith(('SafeLearning/', 'verification/lean/'))
        assert n.endswith('.log') or '/source-history/' in n or '/original-' in n
        assert sha(ROOT, n) == sha(PUB, n) == expected[n]
        violations.setdefault(n, {'sha256': expected[n], 'diagnostics': []})['diagnostics'].append({'line': int(m.group(2)), 'kind': m.group(3)})
    git(['diff', '--cached', '--check', '--', '.', *[':(literal,exclude)'+n for n in sorted(violations)]])
    result = {'status': 'passed_exact_audited_checkpoint29_staged_bytes', 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'baseline_head': HEAD, 'plan': {'file': plan_name, 'sha256': plan_sha}, 'staged_paths_sha256': {n: expected[n] for n in ordered},
        'exact_original_archival_whitespace': violations, 'sources': 1197, 'public_theorems': 10114, 'coverage_complete': False,
        'delivery_pending': True}
    assert all(sha(PUB, n) == h for n, h in expected.items())
    manifest = checked(plan['manifest'])
    for n, h in manifest['working_inputs_sha256'].items():
        if n.startswith(('SafeLearning/', 'verification/lean/')) or n in {'book/coverage/core.json', 'book/coverage/foundations.json', 'book/coverage/applied.json', 'book/coverage/modules.json', 'book/coverage/applied-promotions.json'}:
            assert sha(ROOT, n) == h
    data = (json.dumps(result, separators=(',', ':'))+'\n').encode()
    assert website_size() + len(data) < 850000000
    for root in [ROOT, PUB]:
        with safe(root, REPORT).open('xb') as f:
            f.write(data)
    git(['--literal-pathspecs', 'add', '-f', '--', REPORT])
    assert hashlib.sha256(git(['show', ':'+REPORT]).stdout).hexdigest() == sha(ROOT, REPORT)
    print(json.dumps({'status': result['status'], 'staged_paths': len(names)+1, 'archival_whitespace_files': len(violations)}))

if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--plan', required=True); p.add_argument('--plan-sha256', required=True); p.add_argument('--apply', action='store_true'); a = p.parse_args()
    if a.apply:
        stage(a.plan, a.plan_sha256)
    else:
        expected, _ = prepare(a.plan, a.plan_sha256)
        print(json.dumps({'status': 'passed_exact_checkpoint29_publication_preflight_no_writes', 'paths': len(expected)}))

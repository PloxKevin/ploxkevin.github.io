from pathlib import Path
from datetime import datetime, timezone
import ast, copy, hashlib, importlib.util, json, sys, tempfile

BASE = Path('/home/oxrexkevin/SafetyBased/book/coverage/checks')
OUT = Path('/tmp/checkpoint29-publication-four-helpers-independent-applied-findings-v4.json')
EXPECTED = {
    'root_prepare_checkpoint29_documents_v1.py': '849fae0db6feacdaa10576a4b6efafea1dc8532a748b1d290c29cbcd6821f308',
    'root_copy_publication29_supplements_v2.py': '7407e438560403d643860f2a3976901983ea4771d60e0919f2e76daa652ead3d',
    'root_prepare_publication29_stage_plan_v3.py': '06d4e26fa23163c7e27c36f00f73742e14a923cc0956c4e00a32084740662abc',
    'root_stage_publication29_v3.py': '6fa9b65e44d4ce6d9e3a21c8f734a920ebca5d0a381373061ca6bebefaa61ecd'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert not OUT.exists()
sys.dont_write_bytecode = True
sys.path.insert(0, str(BASE))
mods = {}
for name, h in EXPECTED.items():
    p = BASE/name
    assert sha(p) == h
    ast.parse(p.read_text())
    key = p.stem
    spec = importlib.util.spec_from_file_location(key, p)
    module = importlib.util.module_from_spec(spec)
    sys.modules[key] = module
    spec.loader.exec_module(module)
    mods[key] = module
docs = mods['root_prepare_checkpoint29_documents_v1']
copier = mods['root_copy_publication29_supplements_v2']
planner = mods['root_prepare_publication29_stage_plan_v3']
stager = mods['root_stage_publication29_v3']
cases = []
def accepts(name, function):
    function(); cases.append({'case': name, 'disposition': 'accepted'})
def rejects(name, function):
    try: function()
    except (AssertionError, KeyError, ValueError, FileNotFoundError):
        cases.append({'case': name, 'disposition': 'rejected'}); return
    raise AssertionError('Failed rejection: '+name)

accepts('equal integer exit aliases', lambda: docs.zero({'status': 'passed', 'exit_code': 0, 'actual_exit_code': 0}))
for label, row in [
    ('missing exit', {'status': 'passed'}),
    ('boolean exit', {'status': 'passed', 'exit_code': False}),
    ('actual failure', {'status': 'passed', 'exit_code': 1}),
    ('conflicting exit aliases', {'status': 'passed', 'exit_code': 0, 'actual_exit_code': 1}),
    ('failed status with zero code', {'status': 'failed', 'exit_code': 0})]:
    rejects(label, lambda row=row: docs.zero(row))
rejects('missing required command aliases', lambda: docs.aliases({}, ['command', 'actual_command'], True, list))
rejects('conflicting command aliases', lambda: docs.aliases({'command': ['x'], 'actual_command': ['y']}, ['command', 'actual_command'], True, list))
rejects('command scalar type', lambda: docs.aliases({'command': 'x'}, ['command'], True, list))

original_read, original_sha = docs.read, docs.sha
command = ['python3', 'book/coverage/checks/example.py']
helper_hash, log_hash = 'a'*64, 'b'*64
base = {'status': 'passed', 'actual_exit_code': 0, 'actual_command': command,
        'actual_workdir': str(docs.ROOT), 'log': 'reports/actual.log', 'log_sha256': log_hash,
        'helper_sha256_before': {command[1]: helper_hash}, 'helper_sha256_after': {command[1]: helper_hash}}
active = copy.deepcopy(base)
docs.read = lambda n: active
docs.sha = lambda n, base=docs.ROOT: {command[1]: helper_hash, 'reports/actual.log': log_hash}.get(n, 'c'*64)
try:
    accepts('synthetic native exact command/cwd/helper/log', lambda: docs.native('synthetic-only.json', command))
    for label, key, value in [
        ('wrong native command', 'actual_command', ['python3', 'wrong.py']),
        ('wrong native cwd', 'actual_workdir', '/tmp'),
        ('wrong native helper before', 'helper_sha256_before', {command[1]: 'c'*64}),
        ('wrong native helper after', 'helper_sha256_after', {command[1]: 'c'*64}),
        ('wrong native log hash', 'log_sha256', 'c'*64),
        ('extra native helper without command equality', 'helper_sha256_before', {command[1]: helper_hash, 'extra.py': 'c'*64}),
        ('conflicting native raw command alias', 'command', ['wrong']),
        ('conflicting native raw cwd alias', 'cwd', '/tmp'),
        ('conflicting native raw log alias', 'raw_log', 'different.log'),
        ('conflicting native raw hash alias', 'raw_log_sha256', 'c'*64)]:
        active = {**copy.deepcopy(base), key: value}
        rejects(label, lambda: docs.native('synthetic-only.json', command))
finally:
    docs.read, docs.sha = original_read, original_sha

with tempfile.TemporaryDirectory(prefix='checkpoint29-publication-independent-') as folder:
    root = Path(folder)
    (root/'ordinary.txt').write_text('exact bytes\n')
    (root/'link.txt').symlink_to(root/'ordinary.txt')
    accepts('canonical physical path', lambda: stager.safe(root, 'ordinary.txt'))
    for label, name in [('absolute path', str(root/'ordinary.txt')), ('parent traversal', '../ordinary.txt'),
                        ('glob path', '*.txt'), ('newline path', 'ordinary.txt\n'), ('symlink path', 'link.txt'),
                        ('noncanonical path', './ordinary.txt')]:
        rejects(label, lambda name=name: stager.safe(root, name))
    exclusions = [f'archives/{i:03d}' for i in range(177)]
    (root/'_config.yml').write_text('exclude:\n'+''.join('  - '+n+'\n' for n in exclusions))
    (root/'archives').mkdir()
    (root/'archives/000').mkdir()
    (root/'archives/000/excluded-link').symlink_to('/tmp')
    (root/'link.txt').unlink()
    original_pub = stager.PUB
    stager.PUB = root
    try:
        accepts('excluded archive symlink omitted before included-tree scan', stager.website_size)
        (root/'included-link').symlink_to('/tmp')
        rejects('included directory symlink', stager.website_size)
        (root/'included-link').unlink()
        (root/'_config.yml').write_text('exclude:\n'+''.join('  - '+n+'\n' for n in exclusions[:-1]))
        rejects('wrong website exclusion count', stager.website_size)
    finally: stager.PUB = original_pub

# Inspect the real AST: no Git operation is executed in this review.
tree = ast.parse((BASE/'root_stage_publication29_v3.py').read_text())
adds = []
for node in ast.walk(tree):
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'git' and node.args and isinstance(node.args[0], ast.List):
        values = [x.value for x in node.args[0].elts if isinstance(x, ast.Constant) and isinstance(x.value, str)]
        if 'add' in values: adds.append(values)
assert len(adds) == 2 and all(v[:2] == ['--literal-pathspecs', 'add'] and '-f' in v for v in adds)
cases.append({'case': 'both actual Git add calls use literal paths and force explicit ignored entries', 'disposition': 'static_verified'})
assert planner.HELPERS == ['book/coverage/checks/'+n for n in EXPECTED]
copy_source = (BASE/'root_copy_publication29_supplements_v2.py').read_text()
assert "plan_name = selection['selection_plan']" in copy_source and "selection['selection_plan_sha256']" in copy_source
assert all('selection29-preflight-execution-v'+str(i) in copier.EXPLICIT_RECORDS for i in (1, 2, 3))
assert all('selection29-plan-preparation-execution-v'+str(i) in copier.EXPLICIT_RECORDS for i in (1, 2, 3))
cases.append({'case': 'real selection plan pointer and all preserved failed/preparation histories', 'disposition': 'static_verified'})
# Entire new plan/stager bodies have been read; these checks pin the exact changes.
root = BASE.parents[2]
old_stager = (BASE/'root_stage_publication29_v2.py').read_text()
normalized = old_stager.replace('root_prepare_publication29_stage_plan_v2.py',
    'root_prepare_publication29_stage_plan_v3.py').replace('root_stage_publication29_v2.py',
    'root_stage_publication29_v3.py').replace('publication29-staged-byte-check-v2.json',
    'publication29-staged-byte-check-v3.json').replace('pages29-config-application-execution-v1',
    'pages29-config-application-execution-v2')
assert normalized == (BASE/'root_stage_publication29_v3.py').read_text()
cases.append({'case':'stager3 preserves entire prior gating body with only exact helper/report/config-native version updates',
              'disposition':'static_verified'})
plan_body=(BASE/'root_prepare_publication29_stage_plan_v3.py').read_text()
assert planner.DEST.endswith('root-explicit-audited29-publication-stage-plan-v3.json')
assert stager.REPORT.endswith('publication29-staged-byte-check-v3.json')
assert 'pages29-config-preparation-v2.json' in plan_body
assert 'pages29-config177-previous-original-v2.yml' in plan_body
assert "'pages29-config-application-execution-v2':" in plan_body
assert "for kind in ['staging', 'pages', 'audit', 'delivery']:" in plan_body
assert "assert peers['delivery']['helper'] == docs.ref(DELIVERY_HELPER)" in plan_body
assert planner.DELIVERY_HELPER=='book/coverage/checks/root_close_publication29_delivery_v4.py'
assert "'independent_delivery_helper_review': docs.ref(args.delivery_peer)" in plan_body
assert "'original_failed_stage_plan_executions':" in plan_body
for n,h in planner.HISTORICAL_READONLY_INPUTS_SHA256.items(): assert sha(root/n)==h,n
history=[]
for i in [1,2]:
    p=root/('reports/full-coverage/prepare-publication29-stage-plan-execution-v'+str(i)+'.json')
    d=json.loads(p.read_bytes())
    assert d['status']=='failed' and type(d['actual_exit_code']) is int and d['actual_exit_code']==1
    assert sha(root/d['log'])==d['log_sha256']
    assert 'started_at_utc' in d and 'finished_at_utc' in d and type(d['elapsed_seconds']) in [int,float]
    history.append({'file':p.relative_to(root).as_posix(),'sha256':sha(p),
       'actual_exit_code':d['actual_exit_code'],'original_started_at_utc':d['started_at_utc'],
       'original_finished_at_utc':d['finished_at_utc'],'original_elapsed_seconds':d['elapsed_seconds'],
       'raw_log':{'file':d['log'],'sha256':d['log_sha256']}})
assert [x['actual_exit_code'] for x in history]==[1,1]
cases.append({'case':'both genuine failed Root plan natives and original config1 history are exact readonly extras, not successful prerequisites',
              'disposition':'verified_original_bytes'})
cases.append({'case':'fresh config2 report/177-backup/application2 and delivery4 peer are bound before plan3 output',
              'disposition':'static_verified'})
# A file exclusion is effective even when the preserved Git archive contains that file.
with tempfile.TemporaryDirectory(prefix='checkpoint29-independent-archive-index-') as folder:
    isolated=Path(folder)
    exclusions=[f'archives/{i:03d}' for i in range(176)]+['reports/full-coverage/publication-prepared-29-files.json']
    (isolated/'_config.yml').write_text('exclude:\n'+''.join('  - '+n+'\n' for n in exclusions))
    old_pub=stager.PUB;stager.PUB=isolated
    try:
        before=stager.website_size()
        index=isolated/'reports/full-coverage/publication-prepared-29-files.json'
        index.parent.mkdir(parents=True);index.write_bytes(b'original archive index bytes\n'*100)
        assert stager.website_size()==before
        cases.append({'case':'excluded exact archive-index filename contributes zero included-site bytes in an isolated fixture',
                      'disposition':'accepted'})
    finally:stager.PUB=old_pub
assert all(sha(BASE/n) == h for n, h in EXPECTED.items())
result = {'status': 'passed_conditional_full_checkpoint29_publication_four_helper_code_review',
          'observed_at_utc': datetime.now(timezone.utc).isoformat(), 'errors': [],
          'reviewed_helpers_sha256': {'book/coverage/checks/'+n: h for n, h in EXPECTED.items()},
          'focused_cases': cases, 'case_count': len(cases), 'original_failed_plan_native_history': history, 'original_readonly_history_sha256': planner.HISTORICAL_READONLY_INPUTS_SHA256,
          'full_bodies_read': True, 'full_native_production_prepare_executed': False,
          'producer_invoked': False, 'git_invoked': False, 'publication_mutated': False,
          'scope': 'Full docs/copy/plan/stager code and native schemas read. Focused tests execute actual pure guard functions using isolated explicitly synthetic native records and TMP files. Actual config2 application and Root plan3/stager3 execution remain prerequisite obligations; all four helpers are code/schema reviewed only, not claimed by this code review.'}
OUT.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'status': result['status'], 'case_count': len(cases), 'findings': str(OUT)}))

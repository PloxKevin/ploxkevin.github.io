from pathlib import Path
from datetime import datetime, timezone
import ast, copy, hashlib, importlib.util, json, sys, tempfile

BASE = Path('/tmp/checkpoint29-publication-helpers-v1')
OUT = Path('/tmp/checkpoint29-publication-four-helpers-independent-applied-findings-v2.json')
EXPECTED = {
    'root_prepare_checkpoint29_documents_v1.py': '849fae0db6feacdaa10576a4b6efafea1dc8532a748b1d290c29cbcd6821f308',
    'root_copy_publication29_supplements_v2.py': 'c65a2802563ee84b201f9b0a8d9ae8bc41b6c1ec5ae7a4075550afaf86737185',
    'root_prepare_publication29_stage_plan_v2.py': 'd3c2aa89c0e17cb05f6af7207c1c8de5b66dcbf6162f7c06854d21b06d3f4223',
    'root_stage_publication29_v2.py': '4b91d66704db7bf0677a3f9d8ca3f941a9ca9a1b3e20b405578c57d28da9fc36'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert not OUT.exists()
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
planner = mods['root_prepare_publication29_stage_plan_v2']
stager = mods['root_stage_publication29_v2']
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
tree = ast.parse((BASE/'root_stage_publication29_v2.py').read_text())
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
assert all(sha(BASE/n) == h for n, h in EXPECTED.items())
result = {'status': 'passed_conditional_full_checkpoint29_publication_four_helper_code_review',
          'observed_at_utc': datetime.now(timezone.utc).isoformat(), 'errors': [],
          'reviewed_helpers_sha256': {'book/coverage/checks/'+n: h for n, h in EXPECTED.items()},
          'focused_cases': cases, 'case_count': len(cases),
          'full_bodies_read': True, 'full_native_production_prepare_executed': False,
          'producer_invoked': False, 'git_invoked': False, 'publication_mutated': False,
          'scope': 'Full docs/copy/plan/stager code and native schemas read. Focused tests execute actual pure guard functions using isolated explicitly synthetic native records and TMP files. Successful checkpoint29 audit/export/docs/config/prepared-PUB production remain prerequisite obligations, not claimed by this code review.'}
OUT.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'status': result['status'], 'case_count': len(cases), 'findings': str(OUT)}))

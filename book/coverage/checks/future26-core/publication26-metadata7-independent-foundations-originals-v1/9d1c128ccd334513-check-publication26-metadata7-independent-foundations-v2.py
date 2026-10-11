from pathlib import Path
from datetime import datetime, timezone
import ast, copy, hashlib, json, subprocess, tempfile

R = Path('/home/oxrexkevin/SafetyBased')
PUB = R / 'reports/book/publication-repo'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
name = 'book/coverage/checks/root_stage_publication26_delivery_metadata_v7.py'
digest = 'ea694c6177e60ed41601db2f0ac3c915fc823cd3578857a98742ae168ba6a0f1'
assert H(R/name) == digest
oldname = 'book/coverage/checks/root_stage_publication26_delivery_metadata_v4.py'
assert H(R/oldname) == '8e7392e2d7096ee32ca384c556a702392269418ee102df3e821de5e3a5756d66'
src = (R/name).read_text()
tree = ast.parse(src)
oldtree = ast.parse((R/oldname).read_text())
functions = [x for x in tree.body if isinstance(x, ast.FunctionDef) and x.name != 'main']
oldfunctions = [x for x in oldtree.body if isinstance(x, ast.FunctionDef) and x.name != 'main']
assert [ast.dump(x, include_attributes=False) for x in functions] == [ast.dump(x, include_attributes=False) for x in oldfunctions]
constants = {}
oldconstants = {}
for t, result in [(tree, constants), (oldtree, oldconstants)]:
    for x in t.body:
        if isinstance(x, ast.Assign) and len(x.targets) == 1 and isinstance(x.targets[0], ast.Name):
            try: result[x.targets[0].id] = ast.literal_eval(x.value)
            except (ValueError, TypeError): pass
assert {k for k in oldconstants if oldconstants[k] != constants[k]} == {'PEER', 'UPDATER', 'UPDATER_PEER'}
assert constants['UPDATER'] == 'book/coverage/checks/root_update_publication26_delivery_progress_v4.py'
assert H(R/constants['UPDATER']) == '5e83c67bcf7c1db046cde691de0137e7fd9a30f0254afbd7ec9282db59e21a78'
main = next(x for x in tree.body if isinstance(x, ast.FunctionDef) and x.name == 'main')
oldmain = next(x for x in oldtree.body if isinstance(x, ast.FunctionDef) and x.name == 'main')
added = {
 'book/coverage/checks/root_stage_publication26_delivery_metadata_v4.py',
 'book/coverage/checks/future26-core/publication26-delivery-metadata-stager-independent-foundations-review-v4.json',
 'book/coverage/checks/root_update_publication26_delivery_progress_v1.py',
 'book/coverage/checks/future26-core/publication26-delivery-updater-independent-applied-review-v1.json',
 'book/coverage/checks/root_update_publication26_delivery_progress_v2.py',
 'book/coverage/checks/root_stage_publication26_delivery_metadata_v5.py',
 'book/coverage/checks/root_update_publication26_delivery_progress_v3.py',
 'book/coverage/checks/root_stage_publication26_delivery_metadata_v6.py',
}
class Undo(ast.NodeTransformer):
    def visit_Set(self, node):
        node = self.generic_visit(node)
        node.elts = [x for x in node.elts if not (isinstance(x, ast.Constant) and x.value in added)]
        return node
    def visit_Constant(self, node):
        if isinstance(node.value, str):
            value = node.value.replace('live-checkpoint-26-attempt2.json', 'live-checkpoint-26-attempt1.json').replace('pages-checkpoint-26-attempt2.json', 'pages-checkpoint-26-attempt1.json').replace('pages-checkpoint-26-attempt2.log', 'pages-checkpoint-26-attempt1.log').replace('live26-attempt2-execution-v1', 'live26-attempt1-execution-v1')
            return ast.copy_location(ast.Constant(value=value), node)
        return node
assert ast.dump(Undo().visit(copy.deepcopy(main)), include_attributes=False) == ast.dump(oldmain, include_attributes=False)
for n in added: assert (R/n).is_file() and not (R/n).is_symlink()
prior = {}
for key, n, h in [
 ('main4', 'book/coverage/checks/future26-core/publication26-stage-independent-review-v4.json', 'a3ac3f6ce372beb7084cd298c4a330b23acbc399879ca36f1bdd837b9661350e'),
 ('metadata4', 'book/coverage/checks/future26-core/publication26-delivery-metadata-stager-independent-foundations-review-v4.json', '85a35be4285e3745bf2033bd266b16b73d9d78fd47651d604936339d0f62d518'),
]:
    assert H(R/n) == h
    d = json.loads((R/n).read_text()); assert 'passed' in d['status'] and d['errors'] == []
    prior[key] = {'file': n, 'sha256': h, 'entire_original_body_and_time': d}
assert prior['main4']['entire_original_body_and_time']['fixture_count'] + prior['metadata4']['entire_original_body_and_time']['fixture_count'] == 137
ns = {'ROOT': R, 'PUB': PUB, 'Path': Path, 'hashlib': hashlib, 'json': json, 'subprocess': subprocess, **constants}
exec(compile(ast.Module(body=functions, type_ignores=[]), name, 'exec'), ns)
cases = []
def case(label, fn, reject=False, synthetic=True):
    try: fn()
    except (AssertionError, KeyError, ValueError, TypeError, FileNotFoundError):
        assert reject, label; outcome = 'rejected'
    else: assert not reject, label; outcome = 'accepted'
    cases.append({'fixture': label, 'observed': outcome, 'synthetic_guard_fixture': synthetic})
case('exact complete metadata7 to metadata4 AST inverse', lambda: None)
case('all reusable metadata functions remain byte-equivalent AST', lambda: None)
for bad in ['/tmp/file', '../escape', './book/coverage/a', 'book//coverage/a', 'x\0a', 'x\na', 'x\ra']:
    case('reject unsafe path '+repr(bad), lambda bad=bad: ns['safe'](bad), True)
case('actual live1 failure is retained as strict1', lambda: ns['actual']('reports/full-coverage/live26-attempt1-execution-v1.json', 1), synthetic=False)
case('actual live1 failure cannot satisfy success gate', lambda: ns['actual']('reports/full-coverage/live26-attempt1-execution-v1.json'), True, False)
case('actual live2 successful wrapper is strict0', lambda: ns['actual']('reports/full-coverage/live26-attempt2-execution-v1.json'), synthetic=False)
original_read = ns['read']
for field, value in [('actual_exit_code', False), ('exit_code', 0.0), ('exit_code', 1), ('log_sha256', '0'*64), ('raw_log', '../escape')]:
    d = original_read('reports/full-coverage/live26-attempt2-execution-v1.json'); d[field] = value
    env = dict(ns); env['read'] = lambda n, d=d: d
    exec(compile(ast.Module(body=functions, type_ignores=[]), name, 'exec'), env); env['read'] = lambda n, d=d: d
    case('reject live2 wrapper conflict '+field+repr(value), lambda env=env: env['actual']('fixture'), True)
# Actual read-only initial delivery guards stop before the audit/progress-update region.
stop = next(i for i, x in enumerate(main.body) if isinstance(x, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'audit_name' for t in x.targets))
prefix = compile(ast.fix_missing_locations(ast.Module(body=copy.deepcopy(main.body[:stop]), type_ignores=[])), name, 'exec')
case('actual content attempt2 Pages and31 live hashes pass exact prefix guards', lambda: exec(prefix, dict(ns)), synthetic=False)
def prefixcase(edits):
    env = dict(ns)
    def read(n):
        d = original_read(n)
        if n in edits: edits[n](d)
        return d
    env['read'] = read
    exec(prefix, env)
live2 = 'reports/full-coverage/live-checkpoint-26-attempt2.json'
pages2 = 'reports/full-coverage/pages-checkpoint-26-attempt2.json'
workflow = 'reports/full-coverage/publication26-pages-view-execution-v1.log'
first = original_read('reports/full-coverage/live-checkpoint-26-attempt1.json')
assert first['status'] == 'delivery_not_yet_verified' and sum(x['matches'] for x in first['assets']) == 24
assert all('Temporary failure in name resolution' in x.get('error', '') for x in first['assets'] if not x['matches'])
case('first DNS failure cannot be substituted for successful live2', lambda: prefixcase({live2: lambda d: (d.clear(), d.update(copy.deepcopy(first)))}), True)
for field, value in [('status', 'delivery_not_yet_verified'), ('remote_main', 'wrong'), ('commit', 'wrong')]:
    case('live2 reject '+field, lambda field=field,value=value: prefixcase({live2: lambda d: d.update({field:value})}), True)
for field, value in [('http_status', 503), ('matches', False), ('actual_sha256', '0'*64), ('expected_sha256', '0'*64)]:
    case('live2 row reject '+field, lambda field=field,value=value: prefixcase({live2: lambda d: d['assets'][0].update({field:value})}), True)
case('duplicate source cannot masquerade as31 distinct hashes', lambda: prefixcase({live2: lambda d: d['assets'].__setitem__(1, copy.deepcopy(d['assets'][0]))}), True)
for field, value in [('status', 'pending'), ('commit', 'wrong'), ('expected_commit', 'wrong')]:
    case('pages2 reject '+field, lambda field=field,value=value: prefixcase({pages2: lambda d: d.update({field:value})}), True)
for field, value in [('status', 'in_progress'), ('conclusion', 'failure'), ('headSha', 'wrong')]:
    case('actual workflow reject '+field, lambda field=field,value=value: prefixcase({workflow: lambda d: d.update({field:value})}), True)
case('actual workflow failed job rejected', lambda: prefixcase({workflow: lambda d: d['jobs'][0].update(conclusion='failure')}), True)
closures = {}
for key in prior:
    paths = set(); ns['peer_evidence'](prior[key]['file'], paths)
    for n in paths: closures[n] = H(R/n)
    case('read-only entire original '+key+' typed peer closure', lambda: None, synthetic=False)
for n in ['reports/full-coverage/live-checkpoint-26-attempt1.json', live2, 'reports/full-coverage/pages-checkpoint-26-attempt1.json', pages2, workflow, 'reports/full-coverage/live26-attempt1-execution-v1.json', 'reports/full-coverage/live26-attempt1-execution-v1.log', 'reports/full-coverage/live26-attempt2-execution-v1.json', 'reports/full-coverage/live26-attempt2-execution-v1.log']:
    closures[n] = H(R/n)
# Future update evidence is a required explicit closure; these source checks run no updater.
up = (R/constants['UPDATER']).read_text()
for required in ["all(type(code) is int and code==1 for code in failed_codes)", "sum(row['matches'] is True for row in first_live['assets'])==24", "'Temporary failure in name resolution'", "'retained_first_live_attempt_failure'", "'live26-attempt1-execution-v1.log'"]:
    assert required in up, required
for required in ["names.update(update['evidence_sha256'])", "for n,h in update['evidence_sha256'].items():assert sha(safe(n))==h,n", "d['actual_command']==['python3',UPDATER]", "0<=included_now+replacements", "<850_000_000", "['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul']"]:
    assert required in src, required
firstcopy = next(i for i, x in enumerate(main.body) if isinstance(x, ast.For) and 'shutil.copyfile' in ast.unparse(x))
assert not any(isinstance(x, ast.Call) and ast.unparse(x.func) in ['shutil.copyfile', 'shutil.copytree'] for n in main.body[:firstcopy] for x in ast.walk(n))
assert not any(isinstance(x, ast.Call) and ast.unparse(x.func) == 'subprocess.run' and any(t in ast.unparse(x) for t in ["'commit'", "'push'"]) for x in ast.walk(main))
# Slice only the actual updater's prewrite guards, stopping before mutable progress.
# This confirms its two-attempt evidence; its separate Applied peer remains mandatory.
uptree=ast.parse(up)
upstop=next(i for i,x in enumerate(uptree.body) if isinstance(x,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='progress_path' for t in x.targets))
upbody=[]
for x in uptree.body[:upstop]:
    if isinstance(x,ast.Assign) and any(isinstance(t,ast.Name) and t.id in ('ROOT','REPORTS','PUB','SELF') for t in x.targets): continue
    upbody.append(copy.deepcopy(x))
upcode=compile(ast.fix_missing_locations(ast.Module(body=upbody,type_ignores=[])),constants['UPDATER'],'exec')
upenv={'ROOT':R,'REPORTS':R/'reports/full-coverage','PUB':PUB,'SELF':constants['UPDATER'],'__file__':str(R/constants['UPDATER'])}
case('actual updater4 read-only prewrite evidence includes exact first-failure and retry-success',lambda:exec(upcode,dict(upenv)),synthetic=False)
# Directly exercise the exact original failed-record/first-live assertions after
# giving them native immutable objects, without touching the updater writes.
start=next(i for i,x in enumerate(uptree.body) if isinstance(x,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='failed_name' for t in x.targets))
failbody=[]
for x in uptree.body[start:upstop]:
    if isinstance(x,ast.Assign): continue
    failbody.append(copy.deepcopy(x))
failcode=compile(ast.fix_missing_locations(ast.Module(body=failbody,type_ignores=[])),'updater4-exact-first-failure-guards','exec')
realfailed=original_read('reports/full-coverage/live26-attempt1-execution-v1.json')
realfirst=original_read('reports/full-coverage/live-checkpoint-26-attempt1.json')
assetmap={n:h for n,h in original_read('reports/full-coverage/checkpoint-26-manifest.json')['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
def failedcase(failchange=None,livechange=None):
    d=copy.deepcopy(realfailed);f=copy.deepcopy(realfirst)
    if failchange:failchange(d)
    if livechange:livechange(f)
    env=dict(ns,failed=d,first_live=f,commit=original_read(live2)['commit'],assets=assetmap,
       failed_codes=[d[k] for k in ('actual_exit_code','exit_code') if k in d])
    exec(failcode,env)
case('actual complete first-failure invariants accept exact native bytes',failedcase,synthetic=False)
for field,value in [('actual_exit_code',True),('exit_code',0),('exit_code',1.0),('log_sha256','0'*64),('actual_command',realfailed['actual_command'][:-1]+['2'])]:
    case('first-failure reject '+field+repr(value),lambda field=field,value=value:failedcase(lambda d:d.update({field:value})),True)
for field,value in [('commit','wrong'),('status','passed_all31_asset_sha256')]:
    case('first live reject '+field,lambda field=field,value=value:failedcase(livechange=lambda d:d.update({field:value})),True)
case('first live rejects duplicate source even with31 rows',lambda:failedcase(livechange=lambda d:d['assets'].__setitem__(1,copy.deepcopy(d['assets'][0]))),True)
matchedindex=next(i for i,r in enumerate(realfirst['assets']) if r['matches'] is True)
failedindex=next(i for i,r in enumerate(realfirst['assets']) if r['matches'] is False)
for field,value in [('http_status',404),('http_status',200.0),('actual_sha256','0'*64),('expected_sha256','0'*64),('matches',1)]:
    case('first matched row rejects '+field+repr(value),lambda field=field,value=value:failedcase(livechange=lambda d:d['assets'][matchedindex].update({field:value})),True)
for field,value in [('error','another failure'),('actual_sha256','0'*64),('http_status',404)]:
    case('first DNS row rejects '+field,lambda field=field,value=value:failedcase(livechange=lambda d:d['assets'][failedindex].update({field:value})),True)
for n in added|{name,constants['UPDATER']}:closures[n]=H(R/n)

case('first failed attempt stays in updater exact evidence and metadata closure', lambda: None)
case('all future update gates and pre-copy850M budget remain original strict flow', lambda: None)
with tempfile.TemporaryDirectory(prefix='foundations26-meta6-force-log-') as td:
    p = Path(td); subprocess.run(['git', 'init', '-q'], cwd=p, check=True)
    (p/'.gitignore').write_text('*.log\n'); (p/'actual.log').write_text('exact'); (p/'unrelated.txt').write_text('unstaged')
    subprocess.run(['git', 'add', '-f', '--pathspec-from-file=-', '--pathspec-file-nul'], cwd=p, input=b'.gitignore\0actual.log\0', check=True)
    staged = set(subprocess.run(['git', 'diff', '--cached', '--name-only', '-z'], cwd=p, check=True, capture_output=True).stdout.split(b'\0')) - {b''}
    assert staged == {b'.gitignore', b'actual.log'}
case('real isolated force NUL ignored-log whitelist excludes unrelated path', lambda: None)
out = Path('/tmp/publication26-metadata7-independent-foundations-observations-v2.json'); assert not out.exists()
body = {'status': 'independent_publication26_metadata7_full_code_delta_native_fixtures_passed', 'errors': [], 'reviewer': 'Independent Foundations agent; Root authored metadata7', 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(), 'helper': {'file': name, 'sha256': digest}, 'helper_sha256': digest, 'full_code_and_metadata4_to7_delta_read': True, 'exact_main_inverse_to_entire_metadata4_verified': True, 'all_reusable_functions_unchanged_from_metadata4': True, 'entire_original137_fixture_bodies_and_times_preserved': prior, 'new_fixture_count': len(cases), 'fixtures': cases, 'actual_read_only_native_closed_evidence_sha256': closures, 'actual_first_live_attempt_failure': {'matched': 24, 'DNS_failures': 7, 'original_status': 'delivery_not_yet_verified', 'original_wrapper_exit': 1}, 'actual_second_live_attempt_success': {'matched': 31, 'original_status': 'passed_all31_asset_sha256', 'original_wrapper_exit': 0}, 'scope': 'Full metadata7 code/delta/native-guard review only. Read-only actual successful content Pages/live2 and first DNS failure were inspected. Metadata updater4, metadata production staging, Git commit/push and the future metadata deployment are not executed or approved as existing results. The independent updater4 peer remains a mandatory producer gate.'}
out.write_text(json.dumps(body, indent=2, ensure_ascii=False)+'\n')
print(json.dumps({'status': 'passed', 'fixtures': len(cases), 'observation': str(out), 'sha256': H(out)}))

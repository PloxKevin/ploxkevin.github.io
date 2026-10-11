"""Independent Root code checks and isolated Git regressions for Config-authored metadata4."""
from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,subprocess,tempfile
ROOT=Path(__file__).resolve().parents[4]
META='book/coverage/checks/root_stage_publication24_delivery_metadata_v4.py'
UPD='book/coverage/checks/root_update_publication24_delivery_progress_v1.py'
OUT=ROOT/'book/coverage/checks/future24-core/metadata24-helper4-independent-root-findings-v2.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not OUT.exists()
assert sha(ROOT/META)=='a2820e41a14d4cc4fa143787b61cef112ae71702eb09ba21e83b272ccd661177'
assert sha(ROOT/UPD)=='a1bf7711dbe29157b7ea187e17a05d9d3ea6d79483a69dcc7d2ff6c130a3718c'
code=(ROOT/META).read_text();tree=ast.parse(code)
oldpeer=ROOT/'book/coverage/checks/future24-core/publication24-delivery-metadata-helpers-independent-foundations-review-v2.json'
assert sha(oldpeer)=='cf6de66311c0fba9914033361637664c01c56f719486c52b9a42932d650adc4b'
prior=json.loads(oldpeer.read_text());assert 'passed' in prior['status'] and prior['errors']==[]
for n,d in prior['closed_evidence_sha256'].items():assert not Path(n).is_absolute() and sha(ROOT/n)==d
recovery=ROOT/'book/coverage/checks/future24-core/publication24-stage-recovery-independent-review-v6.json'
r=json.loads(recovery.read_text());assert 'passed' in r['status'] and r['errors']==[] and r['helper_sha256']=='668af4979a6fa4f891404b5cb284691770914eb4541639c6ddf45c98fc75de74'
for n,d in r['closed_evidence_sha256'].items():assert not Path(n).is_absolute() and sha(ROOT/n)==d
# Full helper was independently read by Root. Extract actual functions/assertions
# for regressions instead of executing its real publication mutation.
defs=[n for n in tree.body if isinstance(n,ast.FunctionDef)]
addcalls=[]
for node in ast.walk(tree):
 if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute) and isinstance(node.func.value,ast.Name) and node.func.value.id=='subprocess' and node.func.attr=='run' and node.args and isinstance(node.args[0],ast.List):
  try:cmd=ast.literal_eval(node.args[0])
  except ValueError:continue
  if cmd[:2]==['git','add']:addcalls.append(node)
assert len(addcalls)==1 and ast.literal_eval(addcalls[0].args[0])==['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul']
proof_guard=next(n for n in tree.body if isinstance(n,ast.Assert) and ast.get_source_segment(code,n)=="assert all(not n.startswith('verification/lean/') for n in names)")
checks=[]
with tempfile.TemporaryDirectory(prefix='metadata24-root-independent-') as tmp:
 root=Path(tmp);pub=root/'publication';pub.mkdir();env={'Path':Path,'ROOT':root,'PUB':pub,'hashlib':hashlib,'json':json,'subprocess':subprocess}
 exec(compile(ast.Module(body=defs,type_ignores=[]),'<actual-metadata4-functions>','exec'),env)
 for good in ['book/coverage/progress.json','reports/full-coverage/actual.log','book/coverage/checks/peer.json']:
  assert env['safe'](good)==root/good;checks.append('safe_relative:'+good)
 for bad in ['', '/tmp/escape', '../escape', 'a/../../escape', 'file\nname', 'file\rname', 'file\0name']:
  try:env['safe'](bad)
  except AssertionError:checks.append('rejected_unsafe:'+repr(bad))
  else:raise AssertionError(bad)
 (root/'linked').symlink_to('/tmp',target_is_directory=True)
 try:env['safe']('linked/escape')
 except AssertionError:checks.append('rejected_symlink_escape')
 else:raise AssertionError('symlink escape')
 for names,okay in [({'book/coverage/progress.json','reports/full-coverage/actual.log'},True),({'verification/lean/SafeLearning/New.lean'},False),({'reports/full-coverage/actual.log','verification/lean/verify.py'},False)]:
  env['names']=names
  try:exec(compile(ast.Module(body=[proof_guard],type_ignores=[]),'<actual-metadata4-proof-guard>','exec'),env)
  except AssertionError:assert not okay;checks.append('rejected_proof_metadata_path')
  else:assert okay;checks.append('accepted_metadata_paths')
 subprocess.run(['git','init','-q'],cwd=pub,check=True,capture_output=True)
 (pub/'.gitignore').write_text('*.log\n');(pub/'closed-actual.log').write_text('genuine actual output\n');(pub/'unlisted.log').write_text('unlisted output\n');(pub/'progress.json').write_text('{}\n')
 names={'closed-actual.log','progress.json'};env['payload']=''.join(n+'\0' for n in sorted(names)).encode()
 exec(compile(ast.fix_missing_locations(ast.Module(body=[ast.Expr(value=addcalls[0])],type_ignores=[])),'<actual-metadata4-git-add>','exec'),env)
 actual={n.decode() for n in subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=pub,check=True,capture_output=True).stdout.split(b'\0') if n}
 assert actual==names;checks.append('actual_force_add_explicit_ignored_log');checks.append('actual_unlisted_ignored_log_not_staged')
 assert 'unlisted.log' not in actual and '.gitignore' not in actual
 assert env['dirty']()==names|{'.gitignore'};checks.append('actual_dirty_index_and_untracked_union')
 for required in ["'stage-publication24-execution-v3'","['stage-publication24-execution-v1','stage-publication24-execution-v2']","'publication24-prestage-v2.json'","'publication24-prestage-v3.json'","recovery['actual_command']==['python3','book/coverage/checks/root_stage_publication24_recovery_v6.py']","sha(safe(n))==sha(PUB/n)==d","with out.open('x')","assert dirty()<=names","assert staged and staged<=names"]:
  assert required in code;checks.append('required_closed_gate:'+required)
record={'status':'passed_independent_root_full_metadata4_review_and_actual_isolated_git_regressions',
 'errors':[],'reviewer':'/root','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'helpers_sha256':{META:sha(ROOT/META),UPD:sha(ROOT/UPD)},'checks':checks,'focused_checks':len(checks),
 'unchanged_original_code_review':{'file':oldpeer.relative_to(ROOT).as_posix(),'sha256':sha(oldpeer)},
 'scope':'Root independently read Config-authored whole metadata4 and its delta. Unchanged updater1 retains original independent Foundation reviews. Real temporary Git tests force-add only explicit ignored audit logs; no live publication helper or updater was executed.'}
with OUT.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'passed','focused_checks':len(checks),'actual_temporary_git_regression':True,'no_live_publication_mutation':True}))

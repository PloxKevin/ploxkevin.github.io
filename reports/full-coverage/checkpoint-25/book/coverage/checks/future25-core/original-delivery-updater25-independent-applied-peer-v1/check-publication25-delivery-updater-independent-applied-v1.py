from pathlib import Path
from datetime import datetime, timezone
from copy import deepcopy
from unittest.mock import patch
import ast, hashlib, json, runpy, subprocess, tempfile

ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER=ROOT/'book/coverage/checks/root_update_publication25_delivery_progress_v1.py'
EXPECTED='7adfb8e7c031973f3f538fc23b441aef0098753c3eef322d0929e7b16820e99d'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert H(HELPER)==EXPECTED
source=HELPER.read_text();ast.parse(source)
assert source.count('38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3')==1
commit='a'*40
old_commit='13d6823f7378a9d2b9737242763cf19b9b321b28'
old_readme=('Checkpoint25 has passed the local audit and awaits an actual GitHub Pages build and\n'
 'live asset checks. Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)\n')
stems=['publication25-content-commit-execution-v1','publication25-content-push-execution-v1',
 'publication25-pages-watch-execution-v1','publication25-pages-view-execution-v1',
 'publication25-pages-artifact-execution-v1','live25-attempt1-execution-v1']
selected=json.loads((ROOT/'reports/full-coverage/checkpoint-25-selection.json').read_text())
assert selected['proof_file_count']==1156
protected={n:H(ROOT/n) for n in selected['proof_files']}
protected.update({n:H(ROOT/n) for n in ['book/coverage/inventory.json','book/coverage/inventory-after-correction52.json',
 'book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions19.json']})
protected.update({str(p.relative_to(ROOT)):H(p) for p in (ROOT/'SafeLearning').glob('*.html')})
protected['book/coverage/checks/root_update_publication25_delivery_progress_v1.py']=EXPECTED
fixtures=[]

def write(p,d):
 p.parent.mkdir(parents=True,exist_ok=True)
 p.write_text(json.dumps(d,indent=2)+'\n')

def execute(name,mutate=None,accept=False,aliases=False):
 with tempfile.TemporaryDirectory(prefix='updater25-independent-') as td:
  base=Path(td);reports=base/'reports/full-coverage';pub=base/'reports/book/publication-repo';pub.mkdir(parents=True)
  reports.mkdir(parents=True)
  inv=base/'book/coverage/inventory.json';write(inv,{'fixture':'synthetic independent inventory'})
  helper=base/'book/coverage/checks/root_update_publication25_delivery_progress_v1.py'
  helper.parent.mkdir(parents=True,exist_ok=True)
  # This is the only fixture-only operational substitution: the immutable production inventory digest.
  helper.write_text(source.replace('38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3',H(inv)))
  assets={}
  rows=[]
  for i in range(31):
   n=f'SafeLearning/fixture-{i:02d}.html';p=base/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(f'fixture {i}\n')
   digest=H(p);assets[n]=digest;rows.append({'source':n,'expected_sha256':digest,'actual_sha256':digest,'http_status':200,'matches':True})
  docs={
   'live-checkpoint-25-attempt1.json':{'status':'passed_all31_asset_sha256','commit':commit,'remote_main':commit,'assets':rows},
   'pages-checkpoint-25-attempt1.json':{'status':'passed','commit':commit,'expected_commit':commit},
   'checkpoint-25-manifest.json':{'status':'formal_verification_passed_partial_coverage','proof_files':{str(i):{} for i in range(1156)},'frozen_inputs_sha256':assets,'successful_verification':{}},
   'lean-checkpoint-25/verification-original.json':{'status':'passed','proof_file_count':1156,'theorem_count':9369,'checks':[{'exit_code':0} for _ in range(1156)]},
   'frozen-ledger-checkpoint25-v1.json':{'integrity_status':'passed','errors':[],'mathematical_coverage_complete':False,'counts':{'statuses':{'exercise:complete_math':514,'exercise:partial':19,'exercise:pending':23},'material_review_statuses':{'reviewed':4500,'pending':8274}}},
  }
  workflow={'headSha':commit,'status':'completed','conclusion':'success','jobs':[{'conclusion':'success'}]}
  for s in stems:
   log=reports/(s+'.log')
   log.write_text(json.dumps(workflow)+'\n' if 'pages-view' in s else 'synthetic actual fixture log\n')
   d={'actual_exit_code':0,'log':str(log.relative_to(base)),'log_sha256':H(log),'actual_command':['gh','run','view','123456','--json','headSha,status,conclusion,jobs'] if 'pages-view' in s else ['synthetic-fixture-command']}
   if aliases:d['exit_code']=0
   docs[s+'.json']=d
  progress={'verified_checkpoint':{'proof_files':1156,'theorems':9369,'coverage_complete':False},
   'publication_status':'checkpoint25_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks',
   'last_published_content_commit':old_commit,'last_published_commit':old_commit,
   'live_delivery_status':'checkpoint25_awaiting_actual_pages_and_live_checks','live_delivery_evidence':'old-evidence',
   'working_next_checkpoint_preparation':{'status':'old-status','untouched':'nested value'},'unrelated':{'preserve':[1,2,3]}}
  readme='Independent fixture header\n'+old_readme+'Untouched fixture footer\n'
  state={'base':base,'reports':reports,'docs':docs,'workflow':workflow,'progress':progress,'readme':readme,'head':commit}
  if mutate:mutate(state)
  (reports/'publication25-pages-view-execution-v1.log').write_text(json.dumps(state['workflow'])+'\n')
  # A changed legitimate workflow fixture also needs its native wrapper hash updated.
  if not state.get('do_not_refresh_workflow_hash'):
   docs['publication25-pages-view-execution-v1.json']['log_sha256']=H(reports/'publication25-pages-view-execution-v1.log')
  for n,d in docs.items():write(reports/n,d)
  manifest=docs['checkpoint-25-manifest.json']
  if not state.get('do_not_refresh_audit_hash'):
   manifest['successful_verification']['report_sha256']=H(reports/'lean-checkpoint-25/verification-original.json')
  write(reports/'checkpoint-25-manifest.json',manifest)
  write(base/'book/coverage/material-corrections.json',{'corrections':[{} for _ in range(state.get('corrections_count',52))]})
  pp=base/'book/coverage/progress.json';write(pp,state['progress'])
  rp=reports/'README.md';rp.write_text(state['readme']);before={str(pp):pp.read_bytes(),str(rp):rp.read_bytes()}
  def git(cmd,**kw):
   assert cmd==['git','rev-parse','HEAD'] and kw['cwd']==pub and kw['check'] and kw['capture_output']
   return subprocess.CompletedProcess(cmd,0,stdout=(state['head']+'\n').encode())
  failed=False
  try:
   with patch('subprocess.run',git):runpy.run_path(str(helper),run_name='__main__')
  except (AssertionError,KeyError,TypeError,ValueError):failed=True
  assert failed != accept,(name,'unexpected result')
  output=reports/'progress-checkpoint25-delivery-update-v1.json'
  backups=[reports/'progress-checkpoint25-before-delivery-update-original-v1.json',reports/'README-checkpoint25-before-delivery-update-original-v1.md']
  if accept:
   assert output.is_file() and all(p.is_file() for p in backups)
   assert backups[0].read_bytes()==before[str(pp)] and backups[1].read_bytes()==before[str(rp)]
   now=json.loads(pp.read_text());original=deepcopy(state['progress'])
   for k in ['last_published_commit','last_published_content_commit','live_delivery_status','live_delivery_evidence','publication_status']:now[k]=original[k]
   now['working_next_checkpoint_preparation']['status']=original['working_next_checkpoint_preparation']['status']
   assert now==original
   final=json.loads(pp.read_text());assert final['last_published_content_commit']==commit
   assert final['verified_checkpoint']==original['verified_checkpoint'] and not final['verified_checkpoint']['coverage_complete']
   assert rp.read_text().startswith('Independent fixture header\n') and rp.read_text().endswith('Untouched fixture footer\n')
   assert '123456' in rp.read_text() and commit in rp.read_text() and old_readme not in rp.read_text()
   rec=json.loads(output.read_text());assert rec['coverage_complete'] is False and rec['pages_run']==123456
   assert rec['updated_sha256']=={str(pp.relative_to(base)):H(pp),str(rp.relative_to(base)):H(rp)}
  else:
   assert not output.exists() and not any(p.exists() for p in backups)
   assert pp.read_bytes()==before[str(pp)] and rp.read_bytes()==before[str(rp)]
  fixtures.append({'name':name,'expected':'accept' if accept else 'reject_before_metadata_write','passed':True})

execute('valid native delivery metadata and exact backups',accept=True)
execute('valid consistent dual exit aliases',accept=True,aliases=True)
cases=[
 ('failed live status',lambda s:s['docs']['live-checkpoint-25-attempt1.json'].update(status='failed')),
 ('missing live asset',lambda s:s['docs']['live-checkpoint-25-attempt1.json']['assets'].pop()),
 ('duplicate live asset',lambda s:s['docs']['live-checkpoint-25-attempt1.json']['assets'].__setitem__(30,deepcopy(s['docs']['live-checkpoint-25-attempt1.json']['assets'][0]))),
 ('different remote main',lambda s:s['docs']['live-checkpoint-25-attempt1.json'].update(remote_main='b'*40)),
 ('different PUB HEAD',lambda s:s.update(head='b'*40)),
 ('failed Pages result',lambda s:s['docs']['pages-checkpoint-25-attempt1.json'].update(status='failed')),
 ('different Pages commit',lambda s:s['docs']['pages-checkpoint-25-attempt1.json'].update(expected_commit='b'*40)),
 ('wrong workflow head',lambda s:s['workflow'].update(headSha='b'*40)),
 ('incomplete workflow',lambda s:s['workflow'].update(status='queued')),
 ('failed workflow',lambda s:s['workflow'].update(conclusion='failure')),
 ('no jobs',lambda s:s['workflow'].update(jobs=[])),
 ('failed job',lambda s:s['workflow'].update(jobs=[{'conclusion':'failure'}])),
 ('boolean native zero',lambda s:s['docs'][stems[0]+'.json'].update(actual_exit_code=False)),
 ('conflicting native aliases',lambda s:s['docs'][stems[0]+'.json'].update(exit_code=1)),
 ('missing native exit',lambda s:s['docs'][stems[0]+'.json'].pop('actual_exit_code')),
 ('failed native command',lambda s:s['docs'][stems[0]+'.json'].update(actual_exit_code=1)),
 ('bad native raw log',lambda s:s['docs'][stems[0]+'.json'].update(log_sha256='0'*64)),
 ('wrong Pages command',lambda s:s['docs'][stems[3]+'.json'].update(actual_command=['echo','123'])),
 ('invalid Pages run number',lambda s:s['docs'][stems[3]+'.json'].update(actual_command=['gh','run','view','not-an-id'])),
 ('audit failed',lambda s:s['docs']['lean-checkpoint-25/verification-original.json'].update(status='failed')),
 ('wrong proof count',lambda s:s['docs']['lean-checkpoint-25/verification-original.json'].update(proof_file_count=1155)),
 ('wrong theorem count',lambda s:s['docs']['lean-checkpoint-25/verification-original.json'].update(theorem_count=9370)),
 ('boolean kernel zero',lambda s:s['docs']['lean-checkpoint-25/verification-original.json']['checks'][0].update(exit_code=False)),
 ('bad audit fingerprint',lambda s:(s.update(do_not_refresh_audit_hash=True),s['docs']['checkpoint-25-manifest.json']['successful_verification'].update(report_sha256='0'*64))),
 ('complete coverage asserted',lambda s:s['docs']['frozen-ledger-checkpoint25-v1.json'].update(mathematical_coverage_complete=True)),
 ('ledger errors',lambda s:s['docs']['frozen-ledger-checkpoint25-v1.json'].update(errors=['x'])),
 ('different whole count',lambda s:s['docs']['frozen-ledger-checkpoint25-v1.json']['counts']['statuses'].update({'exercise:complete_math':515})),
 ('different material count',lambda s:s['docs']['frozen-ledger-checkpoint25-v1.json']['counts']['material_review_statuses'].update(reviewed=4501)),
 ('wrong current correction count',lambda s:s.update(corrections_count=51)),
 ('progress not pending',lambda s:s['progress'].update(publication_status='already published')),
 ('different preceding delivered commit',lambda s:s['progress'].update(last_published_content_commit='b'*40)),
 ('ambiguous README replacement',lambda s:s.update(readme=old_readme+old_readme)),
 ('bad live HTTP',lambda s:s['docs']['live-checkpoint-25-attempt1.json']['assets'][0].update(http_status=404)),
 ('bad live hash',lambda s:s['docs']['live-checkpoint-25-attempt1.json']['assets'][0].update(actual_sha256='0'*64)),
 ('false live match',lambda s:s['docs']['live-checkpoint-25-attempt1.json']['assets'][0].update(matches=False)),
]
for name,mutate in cases:execute(name,mutate)
for n,h in protected.items():assert H(ROOT/n)==h,n
report={'status':'passed_independent_publication25_delivery_updater_code_and_isolated_fixtures',
 'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/applied_next','helper':{'file':str(HELPER.relative_to(ROOT)),'sha256':EXPECTED},
 'helper_sha256':EXPECTED,'errors':[],'fixtures':fixtures,'fixture_count':len(fixtures),
 'protected_hashes_checked':len(protected),'selected_proofs_checked':1156,
 'code_scope':'Full top-level code read. Genuine delivery, audit, native log and coverage guards precede backups and metadata writes. Only actual delivered metadata changes; partial coverage and unrelated progress/README content remain explicit.',
 'fixture_scope':'Synthetic actual-schema evidence in isolated temporary roots only; subprocess.run is mocked solely for exact PUB git rev-parse HEAD. The sole fixture source substitution is the immutable synthetic inventory digest. No production helper execution, PUB writes, Git staging, Pages build or live delivery occurred.',
 'production_prerequisites':'Actual checkpoint25 audit, frozen ledger, successful Pages jobs, pushed commit and all31 live asset hashes remain required. This code review supplies none of those results.'}
out=Path('/tmp/publication25-delivery-updater-independent-applied-review-v1.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'fixtures':len(fixtures),'protected':len(protected),'helper_sha256':EXPECTED}))

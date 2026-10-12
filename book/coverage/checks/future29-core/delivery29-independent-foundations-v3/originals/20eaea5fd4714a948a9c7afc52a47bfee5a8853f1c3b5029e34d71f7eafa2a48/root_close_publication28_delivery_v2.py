"""Record actual checkpoint28 delivery, preserve prepared documents, and stage metadata."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,subprocess,re,importlib.util
ROOT=Path(__file__).resolve().parents[3];PUB=ROOT/'reports/book/publication-repo'
SELF='book/coverage/checks/root_close_publication28_delivery_v2.py'
REPORT='reports/full-coverage/progress-checkpoint28-delivery-update-v1.json'
STAGE='reports/full-coverage/publication28-delivery-metadata-index-v1.json'
PLAN='book/coverage/checks/future28-core/root-explicit-audited28-publication-stage-plan-v1.json'
PROGRESS='book/coverage/progress.json';README='reports/full-coverage/README.md'
BACKUPS={PROGRESS:'reports/full-coverage/progress-checkpoint28-before-delivery-update-original-v1.json',README:'reports/full-coverage/README-checkpoint28-before-delivery-update-original-v1.md'}
OLD='Checkpoint 28 is prepared; its push, actual Pages workflow and live hashes\nremain pending. Full mathematical coverage work continues.\n'
def safe(n,base=ROOT):
 assert type(n) is str and n and str(Path(n))==n and not Path(n).is_absolute() and '..' not in Path(n).parts and not any(c in n for c in '\0\n\r')
 p=base/n;assert p.resolve().is_relative_to(base) and not p.is_symlink();return p
def sha(n,base=ROOT):return hashlib.sha256(safe(n,base).read_bytes()).hexdigest()
def read(n):return json.loads(safe(n).read_bytes())
def ref(n):return {'file':n,'sha256':sha(n)}
def encode(d):return (json.dumps(d,indent=2)+'\n').encode()
def git(a,data=None,check=True):return subprocess.run(['git',*a],cwd=PUB,input=data,capture_output=True,check=check)
def actual(n,command):
 d=read(n);assert d['status']=='passed' and type(d['actual_exit_code']) is int and d['actual_exit_code']==0
 assert d['actual_command']==command and d['actual_workdir']==str(ROOT) and sha(d['log'])==d['log_sha256']
 if command[0]=='python3':assert d['helper_sha256_before']==d['helper_sha256_after']=={command[1]:sha(command[1])}
 return d

def immutable():
 plan=read(PLAN);assert sha(plan['manifest']['file'])==plan['manifest']['sha256'] and sha(plan['selection']['file'])==plan['selection']['sha256'] and sha(plan['original_audit']['file'])==plan['original_audit']['sha256']
 m=read(plan['manifest']['file']);a=read(plan['original_audit']['file']);s=read(plan['selection']['file'])
 assert m['status']=='formal_verification_passed_partial_coverage' and m['coverage_complete'] is False
 assert a['status']=='passed' and (a['proof_file_count'],a['theorem_count'])==(1186,9896)
 proof={n:r['sha256'] for n,r in s['proof_files'].items()};assert len(proof)==1186 and proof==a['proof_sha256']
 assets={n:h for n,h in m['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31 and assets==a['source_sha256']
 for n,h in {**proof,**assets}.items():assert sha(n)==sha(n,PUB)==h,n
 for owner in ['core','foundations','applied','modules','applied-promotions']:
  n='book/coverage/'+owner+'.json';assert sha(n)==m['working_inputs_sha256'][n] and sha(n,PUB)==m['frozen_inputs_sha256'][n]
 assert sha('book/coverage/inventory.json')==m['working_inputs_sha256']['book/coverage/inventory.json']
 assert len(read('book/coverage/material-corrections.json')['corrections'])==60
 c=read('reports/full-coverage/pages28-config-preparation-v1.json');assert sha('_config.yml',PUB)==c['config_sha256']
 return assets

def delivery(attempt,stem):
 assets=immutable();live_name=f'reports/full-coverage/live-checkpoint-28-attempt{attempt}.json';pages_name=f'reports/full-coverage/pages-checkpoint-28-attempt{attempt}.json'
 live=read(live_name);commit=live['commit'];assert re.fullmatch('[0-9a-f]{40}',commit)
 assert live['status']=='passed_all31_asset_sha256' and live['remote_main']==commit
 assert len(live['assets'])==31 and {r['source']:r['expected_sha256'] for r in live['assets']}==assets
 for r in live['assets']:assert type(r['http_status']) is int and r['http_status']==200 and r['matches'] is True and r['actual_sha256']==assets[r['source']]
 remote=live['remote_head_check'];assert type(remote['exit_code']) is int and remote['exit_code']==0 and remote['command']==['git','ls-remote','origin','refs/heads/main'] and remote['actual_workdir']==str(PUB) and remote['output'].split()==[commit,'refs/heads/main']
 assert git(['rev-parse','HEAD']).stdout.decode().strip()==commit and git(['ls-remote','origin','refs/heads/main']).stdout.decode().split()==[commit,'refs/heads/main']
 pages=read(pages_name);assert pages['status']=='passed' and type(pages['exit_code']) is int and pages['exit_code']==0 and pages['commit']==pages['expected_commit']==commit and pages['build_status']=='built'
 assert pages['command']==['gh','api','repos/PloxKevin/ploxkevin.github.io/pages/builds/latest'] and pages['actual_workdir']==str(PUB) and sha(pages['log'])==pages['log_sha256']
 build=read(pages['log']);assert build['status']=='built' and build['commit']==commit
 evidence={n:sha(n) for n in [live_name,pages_name,pages['log']]}
 for kind in ['commit','push','pages-view','live']:
  n='reports/full-coverage/'+(f'live28-attempt{attempt}-execution-v1' if kind=='live' else f'publication28-{stem}-{kind}-execution-v{2 if stem=="content" and kind=="push" else 1}')+'.json';d=read(n)
  if kind=='commit':
   cmd=d['actual_command'];assert cmd[:5]==['git','-C',str(PUB),'commit','-m'] and len(cmd)==6 and git(['show','-s','--format=%s',commit]).stdout.decode().rstrip('\n')==cmd[5]
  elif kind=='push':cmd=(['git','-C',str(PUB),'-c','http.version=HTTP/1.1','-c','http.postBuffer=268435456','push','origin','main'] if stem=='content' else ['git','-C',str(PUB),'push','origin','main'])
  elif kind=='pages-view':
   cmd=d['actual_command'];assert len(cmd)==8 and cmd[:3]==['gh','run','view'] and cmd[3].isdigit() and cmd[4:]==['--repo','PloxKevin/ploxkevin.github.io','--json','headSha,status,conclusion,jobs,url,databaseId']
  else:cmd=['python3','book/coverage/verify_live19.py','28',commit,'--attempt',str(attempt)]
  actual(n,cmd);evidence[n]=sha(n);evidence[d['log']]=d['log_sha256']
  if kind=='pages-view':
   w=read(d['log']);run=int(cmd[3]);assert w['headSha']==commit and w['status']=='completed' and w['conclusion']=='success' and type(w['databaseId']) is int and w['databaseId']==run
   assert w['url']==f'https://github.com/PloxKevin/ploxkevin.github.io/actions/runs/{run}' and len(w['jobs'])==3 and all(j['status']=='completed' and j['conclusion']=='success' for j in w['jobs'])
 if stem=='content':
  failed='reports/full-coverage/publication28-content-push-execution-v1.json';f=read(failed);assert f['status']=='failed' and f['actual_exit_code']==1 and sha(f['log'])==f['log_sha256']
  evidence[failed]=sha(failed);evidence[f['log']]=f['log_sha256']
 return commit,run,evidence

def update():
 commit,run,evidence=delivery(1,'content');plan=read(PLAN)
 for n in [PROGRESS,README]:assert sha(n)==sha(n,PUB)==plan['supplementary_paths_sha256'][n]
 assert all(not safe(n).exists() for n in [REPORT,*BACKUPS.values()])
 p=read(PROGRESS);old=safe(README).read_text();assert old.count(OLD)==1
 assert p['publication_status']=='prepared_source_exact_checkpoint_28_awaiting_delivery' and p['live_delivery_evidence'] is None and p['verified_checkpoint']['coverage_complete'] is False
 p.update(last_published_commit=commit,last_published_content_commit=commit,live_delivery_status='passed_all31_asset_sha256',live_delivery_evidence='reports/full-coverage/live-checkpoint-28-attempt1.json',publication_status='checkpoint28_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial')
 p['working_next_checkpoint_preparation']['status']='checkpoint28_actual_audit_and_live_delivery_passed_full_coverage_work_continues'
 new=f'Checkpoint 28 is [pushed to GitHub](https://github.com/PloxKevin/ploxkevin.github.io/commit/{commit}).\nThe [actual Pages workflow](https://github.com/PloxKevin/ploxkevin.github.io/actions/runs/{run})\ncompleted successfully, and [live delivery](live-checkpoint-28-attempt1.json)\nmatched all 31 book asset hashes and the built commit exactly. Full mathematical coverage work continues.\n'
 outputs={PROGRESS:encode(p),README:old.replace(OLD,new,1).encode()}
 for n,b in BACKUPS.items():outputs[b]=safe(n).read_bytes()
 record={'status':'passed_actual_checkpoint28_content_delivery_document_update','updated_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(SELF),'content_commit':commit,'pages_run':run,'originals':{n:{'file':b,'sha256':sha(n)} for n,b in BACKUPS.items()},'updated_sha256':{n:hashlib.sha256(outputs[n]).hexdigest() for n in [PROGRESS,README]},'evidence_sha256':evidence,'coverage_complete':False}
 outputs[REPORT]=encode(record)
 for n,b in outputs.items():
  if n in [PROGRESS,README]:safe(n).write_bytes(b)
  else:
   with safe(n).open('xb') as f:f.write(b)
 immutable();print(json.dumps({'status':record['status'],'content_commit':commit,'pages_run':run}))

def stage():
 commit,run,_=delivery(1,'content');d=read(REPORT);assert d['content_commit']==commit and d['coverage_complete'] is False and d['helper']==ref(SELF)
 n='reports/full-coverage/publication28-delivery-update-execution-v1.json';actual(n,['python3',SELF,'update'])
 expected={**d['evidence_sha256'],**d['updated_sha256']}
 for r in d['originals'].values():assert sha(r['file'])==r['sha256'];expected[r['file']]=r['sha256']
 for p in [SELF,REPORT,n,read(n)['log']]:expected[p]=sha(p)
 peer='book/coverage/checks/future28-core/publication28-staging-resume-independent-applied-code-review-v1.json';p=read(peer);assert p['status']=='passed_independent_checkpoint28_staging_resume_full_code_review' and p['errors']==[] and p['helper']['sha256']==sha(p['helper']['file'])
 expected[peer]=sha(peer);expected.update(p['publication_evidence_sha256'])
 expected.update(p['closed_evidence_sha256'])
 assert not git(['diff','--cached','--name-only','-z']).stdout and not safe(STAGE).exists() and not safe(STAGE,PUB).exists()
 for n,h in expected.items():assert sha(n)==h;target=safe(n,PUB);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(safe(n).read_bytes());assert sha(n,PUB)==h
 record={'status':'passed_explicit_checkpoint28_delivery_metadata_index','checked_at_utc':datetime.now(timezone.utc).isoformat(),'content_commit':commit,'pages_run':run,'paths_sha256':expected,'coverage_complete':False,'metadata_push_pages_live_pending':True}
 b=encode(record)
 for base in [ROOT,PUB]:
  with safe(STAGE,base).open('xb') as f:f.write(b)
 expected[STAGE]=sha(STAGE)
 spec=importlib.util.spec_from_file_location('pages28_size',ROOT/'book/coverage/checks/root_stage_publication28_v6.py');checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
 assert checker.website_size()<850000000
 git(['add','-f','--pathspec-from-file=-','--pathspec-file-nul'],b'\0'.join(n.encode() for n in sorted(expected))+b'\0')
 names={x.decode() for x in git(['diff','--cached','--name-only','-z']).stdout.split(b'\0') if x};assert names and names<=set(expected)
 for n in names:assert hashlib.sha256(git(['show',':'+n]).stdout).hexdigest()==expected[n]==sha(n,PUB)
 assert not git(['diff','--name-only','-z']).stdout
 for row in git(['status','--porcelain','-z','--untracked-files=all']).stdout.decode().split('\0'):
  if row:assert row[:2] in ('M ','A ') and row[3:] in names
 logs=[n for n in names if n.endswith('.log')]
 git(['diff','--cached','--check','--','.',*[':(literal,exclude)'+n for n in logs]])
 immutable();print(json.dumps({'status':record['status'],'staged_paths':len(names),'coverage_complete':False}))

def close():
 commit,run,evidence=delivery(2,'metadata');d=read(REPORT);immutable()
 evidence.update(d['evidence_sha256'])
 for n in [REPORT,STAGE,'reports/full-coverage/publication28-final-content-index-v1.json','reports/full-coverage/publication28-delivery-update-execution-v1.json','reports/full-coverage/publication28-metadata-stage-execution-v1.json']:
  evidence[n]=sha(n)
  if n.endswith('execution-v1.json'):r=read(n);assert r['status']=='passed' and type(r['actual_exit_code']) is int and r['actual_exit_code']==0 and sha(r['log'])==r['log_sha256'];evidence[r['log']]=r['log_sha256']
 closure={'status':'passed_actual_checkpoint28_content_and_metadata_delivery','closed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(SELF),'content_commit':d['content_commit'],'content_pages_run':d['pages_run'],'metadata_commit':commit,'metadata_pages_run':run,'exact_native_evidence_sha256':dict(sorted(evidence.items())),'coverage_complete':False,'scope':'Both actual commits, pushes, three-job Pages workflows, Pages build commits and two original 31-asset HTTP/SHA256 checks. Whole material coverage remains partial.'}
 dest='book/coverage/checks/future28-core/completed28-content-and-metadata-delivery-closure-v1.json'
 with safe(dest).open('xb') as f:f.write(encode(closure))
 print(json.dumps({'status':closure['status'],'closure':ref(dest),'content_commit':d['content_commit'],'metadata_commit':commit,'coverage_complete':False}))

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('mode',choices=['update','stage','close']);a=p.parse_args();{'update':update,'stage':stage,'close':close}[a.mode]()

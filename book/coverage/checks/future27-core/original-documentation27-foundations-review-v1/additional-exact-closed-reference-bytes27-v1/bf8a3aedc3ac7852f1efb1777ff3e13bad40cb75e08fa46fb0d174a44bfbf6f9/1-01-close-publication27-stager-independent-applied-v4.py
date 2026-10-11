from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,shutil
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=Path('/tmp/root_stage_publication27_v3.py')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(HELPER)=='5878ca3465dca6deec70b467cdf14c4f33fa27c0ad8e5a18c3b9d4014059d69c'
prior1=Path('/tmp/publication27-stager-independent-applied-review-v1/publication27-stager-independent-applied-review-v1.json')
prior2=Path('/tmp/publication27-stager-independent-applied-review-v2/publication27-stager-independent-applied-review-v2.json')
obsn=Path('/tmp/publication27-stager-independent-applied-observations-v3.json');actualn=Path('/tmp/publication27-stager-independent-applied-actual-v3.json')
obs=json.loads(obsn.read_bytes());a=json.loads(actualn.read_bytes());assert a['actual_exit_code']==0 and type(a['actual_exit_code']) is int and a['protection_errors']==[] and obs['fixture_count']==33
peer5n='book/coverage/checks/future27-core/pages27-config-independent-modules-output-v5.json';p=ROOT/peer5n;config_peer=json.loads(p.read_bytes());assert config_peer['status']=='passed_independent_actual_checkpoint27_pages_configuration' and config_peer['errors']==[] and config_peer['excluded_count']==129
config=json.loads((ROOT/'reports/full-coverage/pages27-config-preparation-v1.json').read_bytes());assert config_peer['helper']==config['helper'] and config_peer['config_sha256']==config['config_sha256']
ns={'__name__':'native_readonly_peer_check','__file__':str(HELPER)};exec(compile(HELPER.read_text(),str(HELPER),'exec'),ns)
# Read exact native closure, resolving only explicit typed native aliases (never globs or producer fallback).
aliases={};expected={};native_origins=[]
for sourcepeer in [config_peer,json.loads((ROOT/'book/coverage/checks/future27-core/modules-checkpoint27-production-output-independent-confirmation-v1.json').read_bytes())]:
 native_alias=sourcepeer.get('original_closed_byte_aliases')
 if native_alias is None:
  catalog_path=ROOT/'book/coverage/checks/future27-core/original-independent-module-production-output-peer-v1/original-closed-byte-aliases-v1.json'
  catalog=json.loads(catalog_path.read_bytes())
  assert catalog['canonical_original_review']=={'file':'book/coverage/checks/future27-core/modules-checkpoint27-production-output-independent-confirmation-v1.json','sha256':'d2d887d743e2760825e765580bbb0f12f83829636b6e9696e40abe33cc2830c8'}
  native_alias=catalog['original_closed_byte_aliases']
 assert type(native_alias) is dict
 for original,h in sourcepeer['closed_evidence_sha256'].items():
  if Path(original).is_absolute():
   row=native_alias[original]
   assert row['sha256']==h
   name=row['file'];assert not Path(name).is_absolute()
   aliases[original+'::'+h]={'file':name,'sha256':h}
  else:name=original
  assert sha(ns['safe'](ROOT,name))==h
  if name in expected:assert expected[name]==h
  expected[name]=h;native_origins.append({'original':original,'file':name,'sha256':h})
ns['closed_peer'](peer5n,'passed_independent_actual_checkpoint27_pages_configuration',aliases,expected)
ns['closed_peer']('book/coverage/checks/future27-core/modules-checkpoint27-production-output-independent-confirmation-v1.json','passed',aliases,expected)
nativeobs=Path('/tmp/publication27-stager-native-output5-closure-read-only-v1.json')
with nativeobs.open('x') as f:f.write(json.dumps({'scope':'Actual read-only exact current output5 and production27 peer closure; no helper main()/prepare()/PUB/Git run','checked_at_utc':datetime.now(timezone.utc).isoformat(),'output5':{'file':peer5n,'sha256':sha(p)},'config_helper':config['helper'],'config_sha256':config['config_sha256'],'excluded_count':129,'closed_native_originals':native_origins,'status':'passed','errors':[]},indent=2)+'\n')
files=[Path('/tmp/close-publication27-stager-independent-applied-v3.py'),Path('/tmp/close-publication27-stager-independent-applied-v4.py'),Path('/tmp/publication27-stager-finalizer3-native-alias-schema-observation-v1.json'),HELPER,Path('/tmp/check-publication27-stager-independent-applied-v3.py'),Path('/tmp/run-publication27-stager-independent-applied-v4.py'),obsn,actualn,actualn.with_suffix('.log'),nativeobs,prior1,prior2]
# Include every earlier closed original byte rather than modifying/re-dating its original review or execution.
for prior in [json.loads(prior1.read_bytes()),json.loads(prior2.read_bytes())]:
 for n,h in prior['closed_evidence_sha256'].items():
  f=Path(n);assert sha(f)==h
  if f not in files:files.append(f)
base=ROOT/'book/coverage/checks/future27-core/publication27-stage-independent-applied-originals-v3';base.mkdir(exist_ok=False)
closed={};copies={}
for i,p in enumerate(files):
 dest=base/(f'{i:02d}-'+p.name);shutil.copyfile(p,dest);assert sha(dest)==sha(p)
 closed[str(p)]=sha(p);copies[str(p)]={'file':dest.relative_to(ROOT).as_posix(),'sha256':sha(p)}
peer={'status':'passed_independent_checkpoint27_publication_stager_full_code_review','errors':[],'reviewer':'Applied independent of Root stager authorship','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':'book/coverage/checks/root_stage_publication27_v3.py','sha256':sha(HELPER)},'helper_sha256':sha(HELPER),'full_source_read':True,'exact_v2_to_v3_delta':'Only SELF version, strict dict maps, and membership of executed command[1] in before/after map; entire operational code otherwise byte-equivalent','native_fixture_observations':obs,'genuine_fixture_checker_execution':{'file':str(actualn),'sha256':sha(actualn)},'actual_native_output5_closure_read':json.loads(nativeobs.read_bytes()),'original_v1_requires_changes_review_body_and_time':json.loads(prior1.read_bytes()),'original_v2_requires_changes_review_body_and_time':json.loads(prior2.read_bytes()),'earlier_planned_checker_success_not_final_approval':'The v2 checker passed its 61 cases but the distinct missing designated-helper counterexample required changes. The v3 repair now rejects it; previous classifications and raw bytes remain exact.','closed_evidence_sha256':closed,'original_closed_byte_aliases':copies,'production_helper_execution':False,'production_pub_or_git_mutation':False,'actual_commit_push_pages_or_live_claim':False,'coverage_complete':False,'scope':'Independent full source/delta read, 33 fresh exact guard fixtures plus all61 prior planned observations, current17 actual native wrappers and both real peer closure maps. Synthetic full prepare adapter has explicit selection/production-peer hash and verifier-ROOT substitutions; no production prepare/main/Git/copy was run.'}
out=ROOT/'book/coverage/checks/future27-core/publication27-stager-independent-applied-review-v3.json'
with out.open('x') as f:f.write(json.dumps(peer,ensure_ascii=False,indent=2)+'\n')
catalog=base/'closed-original-byte-aliases-v1.json'
with catalog.open('x') as f:f.write(json.dumps({'status':'closed_byte_exact_originals','original_byte_aliases':{k+'::'+v['sha256']:v for k,v in copies.items()},'peer':{'file':out.relative_to(ROOT).as_posix(),'sha256':sha(out)}},indent=2)+'\n')
print(json.dumps({'peer':str(out),'sha256':sha(out),'helper_sha256':sha(HELPER),'fixture_count':33,'prior_fixture_count':61,'native_output5_sha256':sha(ROOT/peer5n),'closed_originals':len(files),'catalog':str(catalog),'catalog_sha256':sha(catalog)}))

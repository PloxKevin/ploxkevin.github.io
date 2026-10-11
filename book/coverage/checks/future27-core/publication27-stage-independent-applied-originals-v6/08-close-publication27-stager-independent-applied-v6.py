from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil
ROOT=Path('/home/oxrexkevin/SafetyBased');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
helper=Path('/tmp/root_stage_publication27_v6.py');obsn=Path('/tmp/publication27-stager-independent-applied-observations-v6.json');actualn=Path('/tmp/publication27-stager-independent-applied-actual-v6.json')
prior_n=ROOT/'book/coverage/checks/future27-core/publication27-stager-independent-applied-review-v4.json';prior=json.loads(prior_n.read_bytes());obs=json.loads(obsn.read_bytes());actual=json.loads(actualn.read_bytes())
assert obs['status']=='passed_independent_checkpoint27_publication_stager_full_code_and_native_fixture_review' and obs['errors']==[]
assert type(actual['actual_exit_code']) is int and actual['actual_exit_code']==0 and actual['protection_errors']==[]
assert sha(helper)=='cc27c980d6393367e58f90e652e8c924c174dcd7ee4e656f53bf4e3548bc0e1c' and obs['prior_v4_full_body_and_time']==prior
base=ROOT/'book/coverage/checks/future27-core/publication27-stage-independent-applied-originals-v6';base.mkdir(exist_ok=False)
closed=dict(prior['closed_evidence_sha256']);aliases=dict(prior['original_closed_byte_aliases'])
for original,row in aliases.items():assert sha(ROOT/row['file'])==row['sha256']==closed[original]
files=[Path('/tmp/root_stage_publication27_v5.py'),helper,Path('/tmp/check-publication27-stager-independent-applied-v6.py'),Path('/tmp/run-publication27-stager-independent-applied-v6.py'),obsn,actualn,actualn.with_suffix('.log'),prior_n,Path(__file__)]
for i,p in enumerate(files):
 dest=base/(f'{i:02d}-'+p.name);shutil.copyfile(p,dest);assert sha(p)==sha(dest)
 closed[str(p)]=sha(p);aliases[str(p)]={'file':dest.relative_to(ROOT).as_posix(),'sha256':sha(p)}
peer={'status':'passed_independent_checkpoint27_publication_stager_full_code_review','errors':[],'reviewer':'Applied independent of Root stager authorship','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':'book/coverage/checks/root_stage_publication27_v6.py','sha256':sha(helper)},'helper_sha256':sha(helper),'full_source_read':True,'whole_delta_and_native_fixture_observations':obs,'actual_independent_fixture_execution':{'file':str(actualn),'sha256':sha(actualn)},'prior_v4_full_review_body_and_time':prior,'preserved_unexecuted_v5_draft':{'file':'/tmp/root_stage_publication27_v5.py','sha256':sha(files[0])},'coverage_complete':False,'production_helper_execution':False,'production_pub_or_git_mutation':False,'closed_evidence_sha256':closed,'original_closed_byte_aliases':aliases,'scope':'Whole final6 source and exact5→6 reverse read; 62 new exact AST-extracted configuration/133-exclusion/budget and designated18th-family guard fixtures, with original61+33+28 review observations/body/time retained unchanged. Real17 available native wrappers and current config5/production27 closed maps rehashed read-only. The future supplemental overlay native report/outputpeer/18th execution is explicitly synthetic in fixtures and genuinely pending at reader execution; production prepare still requires all actual18 records and independent actual outputpeer. Required1284 metadata with one physical required download is a labelled fixture adapter. No production prepare/main, producer copy, PUB/Git or publication success claim.'}
out=ROOT/'book/coverage/checks/future27-core/publication27-stager-independent-applied-review-v6.json'
with out.open('x') as f:f.write(json.dumps(peer,ensure_ascii=False,indent=2)+'\n')
catalog=base/'closed-original-byte-aliases-v1.json'
with catalog.open('x') as f:f.write(json.dumps({'status':'closed_byte_exact_originals','original_byte_aliases':{k+'::'+v['sha256']:v for k,v in aliases.items()},'peer':{'file':out.relative_to(ROOT).as_posix(),'sha256':sha(out)}},indent=2)+'\n')
print(json.dumps({'peer':str(out),'sha256':sha(out),'helper_sha256':sha(helper),'new_fixture_count':obs['fixture_count'],'original_closed_files':len(aliases),'catalog':str(catalog),'catalog_sha256':sha(catalog)}))

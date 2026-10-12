from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,shutil
ROOT=Path('/home/oxrexkevin/SafetyBased');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
helper=Path('/tmp/root_stage_publication27_v4.py');obsn=Path('/tmp/publication27-stager-independent-applied-observations-v4.json');actualn=Path('/tmp/publication27-stager-independent-applied-actual-v4.json')
prior_n=ROOT/'book/coverage/checks/future27-core/publication27-stager-independent-applied-review-v3.json';prior=json.loads(prior_n.read_bytes());obs=json.loads(obsn.read_bytes());actual=json.loads(actualn.read_bytes())
assert obs['status']=='passed_independent_checkpoint27_publication_stager_full_code_and_native_fixture_review' and obs['errors']==[] and actual['actual_exit_code']==0 and type(actual['actual_exit_code']) is int and actual['protection_errors']==[]
files=[helper,Path('/tmp/check-publication27-stager-independent-applied-v4.py'),Path('/tmp/run-publication27-stager-independent-applied-v5.py'),obsn,actualn,actualn.with_suffix('.log'),Path('/tmp/close-publication27-stager-independent-applied-v5.py'),prior_n]
base=ROOT/'book/coverage/checks/future27-core/publication27-stage-independent-applied-originals-v4';base.mkdir(exist_ok=False)
closed=dict(prior['closed_evidence_sha256']);aliases=dict(prior['original_closed_byte_aliases'])
for original,row in aliases.items():assert sha(ROOT/row['file'])==row['sha256']==closed[original]
for i,p in enumerate(files):
 dest=base/(f'{i:02d}-'+p.name);shutil.copyfile(p,dest);assert sha(p)==sha(dest)
 closed[str(p)]=sha(p);aliases[str(p)]={'file':dest.relative_to(ROOT).as_posix(),'sha256':sha(p)}
peer={'status':'passed_independent_checkpoint27_publication_stager_full_code_review','errors':[],'reviewer':'Applied independent of Root stager authorship','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':'book/coverage/checks/root_stage_publication27_v4.py','sha256':sha(helper)},'helper_sha256':sha(helper),'full_source_read':True,'whole_delta_and_native_fixture_observations':obs,'actual_independent_fixture_execution':{'file':str(actualn),'sha256':sha(actualn)},'prior_v3_full_review_body_and_time':prior,'raw_owner_evidence_routing':'Current raw Applied SHA is bound to manifest working input and retained in an explicitly aliased immutable prepared byte-identical candidate. The published original owner remains frozen/pruned; prepared exact Root/PUB evidence may be referenced without copying it again. Other arbitrary current working hashes do not authorize an alternate route.','coverage_complete':False,'production_helper_execution':False,'production_pub_or_git_mutation':False,'closed_evidence_sha256':closed,'original_closed_byte_aliases':aliases,'scope':'Independent full source/delta read; 29 new exact branch/negative fixtures plus all prior61+33 source/delta observations and real native 17 wrappers. Both actual config5 and production27 closed maps pass with the exact immutable unpruned Applied body retained under a different prepared path. No production prepare/main/Git/staging action.'}
# Count comes from the actual observed checker, never its nominal description.
peer['scope']=peer['scope'].replace('29 new',str(obs['fixture_count'])+' new')
out=ROOT/'book/coverage/checks/future27-core/publication27-stager-independent-applied-review-v4.json'
with out.open('x') as f:f.write(json.dumps(peer,ensure_ascii=False,indent=2)+'\n')
catalog=base/'closed-original-byte-aliases-v1.json'
with catalog.open('x') as f:f.write(json.dumps({'status':'closed_byte_exact_originals','original_byte_aliases':{k+'::'+v['sha256']:v for k,v in aliases.items()},'peer':{'file':out.relative_to(ROOT).as_posix(),'sha256':sha(out)}},indent=2)+'\n')
print(json.dumps({'peer':str(out),'sha256':sha(out),'helper_sha256':sha(helper),'new_fixture_count':obs['fixture_count'],'original_closed_files':len(aliases),'catalog':str(catalog),'catalog_sha256':sha(catalog)}))

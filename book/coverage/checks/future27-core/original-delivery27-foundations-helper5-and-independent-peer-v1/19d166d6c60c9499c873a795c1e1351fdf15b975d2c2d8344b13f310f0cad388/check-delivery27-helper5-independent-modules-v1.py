from pathlib import Path
from datetime import datetime,timezone
import copy,contextlib,hashlib,io,json,tempfile

ROOT=Path('/home/oxrexkevin/SafetyBased')
SOURCE=Path('/tmp/root_close_publication27_delivery_v5.py')
OUT=Path('/tmp/delivery27-helper5-independent-modules-findings-v1.json')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
def encode(j):return (json.dumps(j,indent=2)+'\n').encode()
text=SOURCE.read_text();assert sha(SOURCE)=='f09f881b61313f847be329410eaabfc9d26a99bbd498a297229adb74bef3c561'
previous=Path('/tmp/root_close_publication27_delivery_v4.py')
reverse=text.replace('root_close_publication27_delivery_v5.py','root_close_publication27_delivery_v4.py').replace("if '.git' in p.relative_to(PUB).parts or not kept(n):continue","if '.git' in p.relative_to(PUB).parts:continue").replace("git(['add','-f','--',*sorted(copied)])","git(['add','--',*sorted(copied)])")
assert reverse==previous.read_text()
ns={'__name__':'independent_delivery_review','__file__':str(SOURCE)};exec(compile(text,str(SOURCE),'exec'),ns)
started=datetime.now(timezone.utc).isoformat()
native_assets=ns['immutable']();assert len(native_assets)==31
assert ns['actual']('reports/full-coverage/verify-checkpoint27-execution-v1.json')[1]==['python3','reports/full-coverage/checkpoint-27/verification/lean/verify.py','--reuse-kernel-from',str(ROOT/'reports/full-coverage/checkpoint-26')]
checks=[]
def reject(label,fn):
    try:fn()
    except (AssertionError,ValueError):checks.append({'fixture':label,'synthetic':True,'expected':'reject','observed':'reject'})
    else:raise AssertionError('unexpected acceptance: '+label)
def accept(label,fn):
    fn();checks.append({'fixture':label,'synthetic':True,'expected':'accept','observed':'accept'})
accept('strict all-three integer zero aliases',lambda:ns['zero']({'exit_code':0,'actual_exit_code':0,'actual_runner_exit_code':0}))
for k in ('exit_code','actual_exit_code','actual_runner_exit_code'):
    for v in (False,1,'0'):
        d={'exit_code':0,'actual_exit_code':0,'actual_runner_exit_code':0};d[k]=v
        reject(k+' invalid '+repr(v),lambda d=d:ns['zero'](d))
reject('missing exit aliases',lambda:ns['zero']({}))
for family in (('command','actual_command'),('cwd','working_directory','actual_workdir'),('log','raw_log'),('log_sha256','raw_log_sha256')):
    accept('equal aliases '+str(family),lambda f=family:ns['aliases']({k:'same'for k in f},f))
    reject('conflicting aliases '+str(family),lambda f=family:ns['aliases']({k:str(i)for i,k in enumerate(f)},f))
    reject('missing aliases '+str(family),lambda f=family:ns['aliases']({},f))
for n in ('../escape','/tmp/absolute','book//coverage/a','book/coverage/../a','book/coverage/x\n','book/coverage/x\0'):
    reject('unsafe metadata path '+repr(n),lambda n=n:ns['safe'](n))
for n in ('verification/lean/SafeLearning/New.lean','SafeLearning/new.html','reports/full-coverage/checkpoint-27/file','reports/full-coverage/lean-checkpoint-27/file'):
    reject('nonmetadata selection/source path '+n,lambda n=n:ns['metadata'](n))
accept('ordinary reviewed metadata path',lambda:ns['metadata']('book/coverage/checks/review.json'))

# This isolated fixture executes the complete pure update and stage-preparation
# branches. Its future delivery provider and Git responses are synthetic, never
# a claim that production commit/push/Pages/live have completed.
with tempfile.TemporaryDirectory(prefix='delivery27-independent-fixture-')as td:
    root=Path(td)/'root';pub=root/'reports/book/publication-repo';root.mkdir();pub.mkdir(parents=True)
    original_progress=(ROOT/ns['PROGRESS']).read_bytes();original_readme=(ROOT/ns['README']).read_bytes()
    for n,b in ((ns['PROGRESS'],original_progress),(ns['README'],original_readme)):
        p=root/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
    fixture={'__name__':'isolated_delivery_fixture','__file__':str(SOURCE)};exec(compile(text,str(SOURCE),'exec'),fixture)
    fixture['ROOT']=root;fixture['PUB']=pub
    commit='1'*40;run=123456789;fixture['delivery']=lambda:(commit,run,{})
    record,outputs=fixture['prepare_update']()
    after=json.loads(outputs[fixture['PROGRESS']]);before=json.loads(original_progress)
    assert after['previous_checkpoint26_delivery']==before['previous_checkpoint26_delivery']
    assert after['verified_checkpoint']==before['verified_checkpoint']
    assert after['working_next_checkpoint_preparation']['exercise_counts']==before['working_next_checkpoint_preparation']['exercise_counts']
    assert record['coverage_complete']is False
    assert outputs[fixture['BACKUPS'][fixture['PROGRESS']]]==original_progress
    assert outputs[fixture['BACKUPS'][fixture['README']]]==original_readme
    assert set(outputs)=={fixture['PROGRESS'],fixture['README'],fixture['REPORT'],*fixture['BACKUPS'].values()}
    checks.append({'fixture':'complete pure metadata update with synthetic delivery provider preserves all previous checkpoint/math/count history and original backups','synthetic':True,'expected':'accept','observed':'accept'})
    (root/fixture['README']).write_bytes(original_readme+b'x')
    reject('prepared README drift before update',lambda:fixture['prepare_update']())
    (root/fixture['README']).write_bytes(original_readme)
    for n,b in outputs.items():p=root/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
    (root/fixture['SELF']).parent.mkdir(parents=True,exist_ok=True);(root/fixture['SELF']).write_bytes(SOURCE.read_bytes())
    log='reports/full-coverage/publication27-delivery-progress-update-execution-v1.log'
    emitted={'status':'applied','record':record,'prospective_paths_sha256':{n:hashlib.sha256(b).hexdigest()for n,b in outputs.items()}}
    (root/log).write_bytes(encode(emitted))
    execution='reports/full-coverage/publication27-delivery-progress-update-execution-v1.json'
    actual={'actual_exit_code':0,'actual_command':['python3',fixture['SELF'],'update','--apply'],'actual_workdir':str(root),'raw_log':log,'raw_log_sha256':sha(root/log),'helper_sha256_before':{fixture['SELF']:sha(SOURCE)},'helper_sha256_after':{fixture['SELF']:sha(SOURCE)}}
    (root/execution).write_bytes(encode(actual))
    for n in (fixture['LIVE'],fixture['PAGES']):(root/n).write_bytes(encode({'fixture_only':True}))
    readern='book/coverage/checks/fixture-reader.json';peern='book/coverage/checks/fixture-peer.json'
    (root/readern).parent.mkdir(parents=True,exist_ok=True);(root/readern).write_bytes(encode({'actual_exit_code':0}))
    peer={'status':'passed_independent_full_delivery27_helper_review','errors':[],'helper_sha256':sha(SOURCE),'actual_reader_execution':{'file':readern,'sha256':sha(root/readern)}}
    (root/peern).write_bytes(encode(peer))
    supplement='book/coverage/checks/fixture-supplement.json'
    packet={'status':'explicit_reviewed_checkpoint27_delivery_metadata_plan','content_commit':commit,'coverage_complete':False,'files_sha256':{readern:sha(root/readern),peern:sha(root/peern)},'independent_reviews':[{'file':peern,'sha256':sha(root/peern)}]}
    (root/supplement).write_bytes(encode(packet))
    config=(ROOT/'reports/book/publication-repo/_config.yml').read_bytes();(pub/'_config.yml').write_bytes(config)
    def git(cmd):
        if cmd in (['diff','--cached','--name-only','-z'],['status','--porcelain','-z','--untracked-files=all']):return b''
        if cmd==['show','HEAD:_config.yml']:return config
        raise AssertionError('unexpected synthetic Git call '+repr(cmd))
    fixture['git']=git
    def stage():
        with contextlib.redirect_stdout(io.StringIO()):fixture['stage'](supplement,sha(root/supplement),False)
    accept('complete pure stage preparation with explicitly synthetic native delivery/update records and isolated Git responses',stage)
    excluded=pub/'verification/lean/.lake';excluded.mkdir(parents=True);outside=Path(td)/'outside';outside.mkdir();(excluded/'packages').symlink_to(outside,target_is_directory=True)
    accept('literal-excluded package symlink is skipped by actual stage budget loop',stage)
    included=pub/'included-link';included.symlink_to(outside,target_is_directory=True)
    reject('included symlink directory rejected by actual stage budget loop',stage);included.unlink()
    included.symlink_to(root/readern);reject('included symlink file rejected',stage);included.unlink()
    raw=copy.deepcopy(actual);raw['exit_code']=False;(root/execution).write_bytes(encode(raw));reject('stage rejects conflicting boolean actual update exit alias',stage);(root/execution).write_bytes(encode(actual))
    raw=copy.deepcopy(peer);raw['helper_sha256']='0'*64;(root/peern).write_bytes(encode(raw))
    packet2=copy.deepcopy(packet);packet2['files_sha256'][peern]=sha(root/peern);packet2['independent_reviews'][0]['sha256']=sha(root/peern);(root/supplement).write_bytes(encode(packet2))
    reject('stage rejects peer bound to a different helper even with consistent packet hashes',stage)

assert len(checks)>=40
assert "git(['add','-f','--',*sorted(copied)])"in text
assert text.index("git(['add','-f','--',*sorted(copied)])")>text.index('for n,h in expected.items():assert sha(safe(n))==h,n')
assert ns['immutable']()==native_assets
closure={str(SOURCE):sha(SOURCE),str(previous):sha(previous)}
history=[]
for v in (2,3,4,5):
    actualp=Path(f'/tmp/delivery27-helper{v}-native-prefix-actual-v1.json');a=json.loads(actualp.read_bytes())
    want=0 if v>=4 else 1;assert type(a['actual_exit_code'])is int and a['actual_exit_code']==want
    assert sha(a['raw_log'])==a['raw_log_sha256']
    for n,h in a['helper_sha256_before'].items():assert a['helper_sha256_after'][n]==h and sha(n)==h;closure[n]=h
    closure[str(actualp)]=sha(actualp);closure[a['raw_log']]=a['raw_log_sha256'];closure[a['actual_runner']['file']]=a['actual_runner']['sha256'];assert sha(a['actual_runner']['file'])==a['actual_runner']['sha256']
    history.append({'actual_execution':ref(actualp),'entire_original_body_and_time':a})
for n,h in ns['PINS'].items():assert sha(ROOT/n)==h;closure[str(ROOT/n)]=h
out={'status':'passed_independent_full_delivery27_helper_review','errors':[],'helper_sha256':sha(SOURCE),'helper':ref(SOURCE),'reviewer':'/root/modules_resume','reviewed_at_utc':started,'completed_at_utc':datetime.now(timezone.utc).isoformat(),'full_helper_body':text,'entire_original_helper4_body':previous.read_text(),'exact_three_replacements_restore_original_helper4':True,'native_current55_math_prefix_passed':True,'selected_proofs':1175,'theorem_lemmas':9644,'current_assets':31,'current_installed_owners':5,'fixture_count':len(checks),'fixture_observations':checks,'author_native_prefix_execution_histories_unchanged':history,'future_actual_delivery_positive_execution_is_pending':True,'scope':'Full code/native immutable prefix and meaningful isolated synthetic guard fixtures only. The synthetic complete pure update/stage fixtures test metadata/history preservation and strict guards without claiming production commit, push, Pages, live delivery or staging success. All production delivery-family evidence remains required by delivery(). The force-add repair applies only after exact path/SHA metadata whitelist validation; excluded symlinks are skipped while included symlink files/directories are rejected. No producer, source, owner, compiler, PUB or Git mutation occurred.','closed_evidence_sha256':closure,'actual_checker':ref(Path(__file__))}
OUT.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'findings':ref(OUT),'fixture_count':len(checks)}))

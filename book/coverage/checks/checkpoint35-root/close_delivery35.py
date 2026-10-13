"""Close checkpoint35 delivery from completed native observations only."""
import hashlib
import json
import os
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]
PUB=ROOT/'reports/book/publication-repo'
CONTENT='069532b78ff92ab0b5e84b246807289ca0d62574'
METADATA='36b715de808ac993a14c15a90ce95a65018d780c'
FINISH='reports/full-coverage/publication35-finish-v1.json'

def read(name):
    return json.loads((ROOT/name).read_bytes())

def ref(name):
    return {'file':name,'sha256':hashlib.sha256((ROOT/name).read_bytes()).hexdigest()}

def encode(value):
    return (json.dumps(value,indent=2,ensure_ascii=False)+'\n').encode()

def atomic(name,data):
    path=ROOT/name
    path.parent.mkdir(parents=True,exist_ok=True)
    fd,tmp=tempfile.mkstemp(prefix='.'+path.name+'-',dir=path.parent)
    try:
        with os.fdopen(fd,'wb') as stream:
            stream.write(data);stream.flush();os.fsync(stream.fileno())
        os.replace(tmp,path)
    finally:
        if os.path.exists(tmp):os.unlink(tmp)

def main():
    if (ROOT/FINISH).exists():
        raise RuntimeError('Completed closure is immutable; inspect its receipt instead of re-running')
    evidence=['reports/full-coverage/publication35-content-delivery-v1.json']
    for stem in ['publication35-metadata-add','publication35-metadata-commit','publication35-metadata-push',
                 'pages35-metadata-runs','live35-metadata']:
        name='reports/full-coverage/'+stem+'-execution-v1.json'
        d=read(name)
        assert d['status']=='passed' and d['actual_exit_code']==0
        assert ref(d['log'])['sha256']==d['log_sha256']
        evidence.extend([name,d['log'],d['started_receipt']])
    name='reports/full-coverage/pages35-metadata-jobs-execution-v3.json'
    d=read(name)
    assert d['status']=='passed' and d['actual_exit_code']==0
    assert ref(d['log'])['sha256']==d['log_sha256']
    jobs=json.loads((ROOT/d['log']).read_bytes())['jobs']
    assert len(jobs)==3 and all(j['status']=='completed' and j['conclusion']=='success' for j in jobs)
    evidence.extend([name,d['log'],d['started_receipt']])
    live=read('reports/full-coverage/live-checkpoint-35-attempt2.json')
    pages=read('reports/full-coverage/pages-checkpoint-35-attempt2.json')
    assert live['status']=='passed_all31_asset_sha256' and live['commit']==live['remote_main']==METADATA
    assert len(live['assets'])==31 and all(a['matches'] for a in live['assets'])
    assert pages['status']=='passed' and pages['commit']==pages['expected_commit']==METADATA
    evidence.extend(['reports/full-coverage/live-checkpoint-35-attempt2.json',
                     'reports/full-coverage/pages-checkpoint-35-attempt2.json',
                     'reports/full-coverage/pages-checkpoint-35-attempt2.log'])
    observations=[]
    for command in [['git','rev-parse','HEAD'],['git','ls-remote','origin','refs/heads/main'],
                    ['git','status','--porcelain=v1','--untracked-files=all']]:
        run=subprocess.run(command,cwd=PUB,capture_output=True,text=True)
        assert run.returncode==0
        observations.append({'command':command,'actual_workdir':str(PUB),'actual_exit_code':run.returncode,
                             'stdout':run.stdout,'stderr':run.stderr})
    assert observations[0]['stdout'].strip()==METADATA
    assert observations[1]['stdout'].split()[0]==METADATA
    assert not observations[2]['stdout']
    result={'status':'passed_actual_checkpoint35_content_and_metadata_push_Pages_all31_delivery',
            'content_commit':CONTENT,'metadata_commit':METADATA,
            'checked_at_utc':datetime.now(timezone.utc).isoformat(),
            'evidence':[ref(n) for n in sorted(set(evidence))],
            'actual_publication_observations':observations,'successful_pages_jobs':[j['name'] for j in jobs],
            'proof_files':1267,'public_theorems':11472,'coverage_complete':False,
            'exercise_coverage':{'complete':539,'partial':6,'pending':11,'total':556},
            'material_coverage':{'reviewed':4878,'pending':7896,'total':12774},
            'scope':'Closes checkpoint35 delivery only. Verified Source90 is immutable; subsequent solution-depth revisions require separate evidence.'}
    atomic(FINISH,encode(result))
    docs=['book/coverage/progress.json','book/coverage/CONTINUATION.md','reports/full-coverage/README.md']
    for n in docs:
        history='reports/full-coverage/source-history/checkpoint35-before-delivery-closure-v1/'+n
        if (ROOT/history).exists():raise RuntimeError('Unexpected existing document history')
        atomic(history,(ROOT/n).read_bytes())
    progress=read(docs[0])
    progress['last_published_commit']=METADATA
    progress['last_published_content_commit']=CONTENT
    progress['publication_status']='checkpoint35_content_and_metadata_Pages_all31_live_confirmed'
    progress['live_delivery_status']='passed_checkpoint35_content_and_metadata_Pages_and_all31_asset_hashes'
    progress['live_delivery_evidence']['metadata_push_and_metadata_live_check_pending']=False
    progress['live_delivery_evidence']['metadata_commit']=METADATA
    progress['live_delivery_evidence']['completed_delivery']=ref(FINISH)
    progress['working_next_checkpoint_preparation']['status']='checkpoint35_delivered_next_work_unselected'
    atomic(docs[0],encode(progress))
    for n in docs[1:]:
        text=(ROOT/n).read_text()
        text+='\nCheckpoint35 delivery is now complete: content `069532b7`, metadata `36b715de`; all three metadata Pages jobs and all 31 live asset hashes passed. See `reports/full-coverage/publication35-finish-v1.json`. Mathematical coverage remains partial (539 complete, 6 partial, 11 pending exercises). The all-exercise solution-depth work continues as separate drafts and reviews.\n'
        atomic(n,text.encode())
    print(json.dumps({'status':result['status'],'finish':ref(FINISH),'metadata_commit':METADATA}))

if __name__=='__main__':main()

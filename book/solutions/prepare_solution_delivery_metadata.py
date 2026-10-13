"""Record actual Source91 content delivery without promoting formal coverage."""
import argparse
import json
from pathlib import Path
import subprocess

import solution_review as review
import solution_release as release

PUB=review.ROOT/'reports/book/publication-repo'
HISTORY='reports/solution-review/source-history/before-source91-delivery-metadata-v1'
READY='reports/solution-review/source91-content-delivered-metadata-ready-v1.json'


def native(name, command):
    value=review.read(name)
    assert value['status']=='passed' and value['actual_exit_code']==0
    assert value['actual_command']==command
    assert value['helper_sha256_before']==value['helper_sha256_after']
    assert review.ref(value['log'])['sha256']==value['log_sha256']
    assert review.ref(value['started_receipt'])['sha256']==value['started_receipt_sha256']
    return value


def git(args):
    result=subprocess.run(['git',*args],cwd=PUB,capture_output=True)
    assert result.returncode==0,result.stderr.decode()
    return result.stdout.decode().strip()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--delivery',required=True)
    parser.add_argument('--native',required=True)
    parser.add_argument('--commit-receipt',required=True)
    parser.add_argument('--push-receipt',required=True)
    args=parser.parse_args()
    fingerprint=review.ref(release.PLAN)['sha256'];plan=release.load_plan(fingerprint)
    delivery=review.read(args.delivery)
    assert delivery['status']=='passed_source91_all31_live_assets_and_all3_Pages_jobs'
    assert delivery['phase']=='content' and delivery['plan']==review.ref(release.PLAN)
    commit=delivery['expected_commit']
    assert delivery['remote_main']==commit
    assert len(delivery['assets'])==31
    assert {r['source']:r['actual_sha256'] for r in delivery['assets']}==plan['site_source91_sha256']
    assert all(r['matches'] and r['http_status']==200 for r in delivery['assets'])
    assert delivery['Pages_build']['commit']==commit and delivery['Pages_build']['status']=='built'
    run=delivery['selected_run']
    assert run['head_sha']==commit and run['name']=='pages build and deployment'
    assert run['status']=='completed' and run['conclusion']=='success'
    assert len(delivery['jobs'])==3 and all(j['status']=='completed' and j['conclusion']=='success' for j in delivery['jobs'])
    attempt=int(Path(args.delivery).stem.rsplit('attempt',1)[1])
    assert args.delivery=='reports/solution-review/source91-content-delivery-attempt'+str(attempt)+'.json'
    command=['python3','-B','book/solutions/verify_solution_delivery.py','--plan-sha256',fingerprint,
             '--commit',commit,'--phase','content','--attempt',str(attempt)]
    execution=native(args.native,command)
    assert execution['actual_workdir']==str(review.ROOT)
    assert review.read(execution['log'])['report']==review.ref(args.delivery)
    helper=review.ref('book/solutions/verify_solution_delivery.py')
    assert delivery['helper']==helper and execution['helper_sha256_before'][helper['file']]==helper['sha256']
    for key in ['remote_observation','Pages_build_observation','actions_runs_observation','actions_jobs_observation']:
        observed=delivery[key]
        assert observed['actual_exit_code']==0 and observed['actual_workdir']==str(PUB)
        release.exact(observed['log'])
    for name,cmd in [(args.commit_receipt,['git','commit','-m','Expand 251 worked solutions and review all 556 exercises']),
                     (args.push_receipt,['git','push','origin','main'])]:
        assert native(name,cmd)['actual_workdir']==str(PUB)
    assert git(['symbolic-ref','--short','HEAD'])=='main' and git(['rev-parse','HEAD'])==commit
    assert not git(['status','--porcelain=v1','--untracked-files=all'])
    assert git(['ls-remote','origin','refs/heads/main']).split()[0]==commit
    stage=review.read('reports/solution-review/source91-content-publication-plan-v1.json')
    assert stage['phase']=='content' and git(['rev-parse',commit+'^'])==stage['expected_publication_head']
    for name,h in plan['site_source91_sha256'].items():
        assert review.ref(name)['sha256']==h and review.sha((PUB/name).read_bytes())==h
    evidence=[review.ref(n) for n in [args.delivery,args.native,args.commit_receipt,args.push_receipt]]
    documents=review.read('reports/solution-review/source91-documentation-v1.json')
    assert documents['status']=='passed_source91_completed_local_checks_and_documentation'
    originals={r['file']:r for r in documents['documents']}
    tracker='book/solutions/baseline-source90/review-tracker.json'
    originals[tracker]=plan['approved_tracker'] | {'file':tracker}
    # On a resumed run the original byte snapshots remain authoritative.
    for name,binding in originals.items():
        saved=HISTORY+'/'+name
        if not review.path(saved).exists():
            data=review.path(name).read_bytes()
            assert review.sha(data)==binding['sha256'], 'Document changed before metadata: '+name
            review.put(saved,data)
        assert review.ref(saved)['sha256']==binding['sha256']
    progress=review.read(HISTORY+'/book/coverage/progress.json')
    progress['last_published_commit']=commit
    progress['last_published_content_commit']=commit
    progress['publication_status']='Source91_content_Pages_all31_live_confirmed_metadata_pending'
    progress['live_delivery_status']='Source91_content_Pages_all31_live_confirmed_metadata_pending'
    progress['live_delivery_evidence']={'content_commit':commit,'content_delivery':review.ref(args.delivery),
        'actual_native_delivery':review.ref(args.native),'actual_commit':review.ref(args.commit_receipt),
        'actual_push':review.ref(args.push_receipt),'metadata_push_and_metadata_live_check_pending':True}
    progress['solution_depth_requirement'].update(status='all556_independently_reviewed_installed_and_content_delivered',
        content_commit=commit,content_delivery=review.ref(args.delivery),publication_metadata_pending=True)
    tracker_value=review.read(HISTORY+'/'+tracker)
    assert len(tracker_value['exercises'])==556
    for row in tracker_value['exercises']:
        assert row['status']=='independently_approved_draft_pending_adoption'
        row['status']='independently_approved_installed_and_content_delivered'
    tracker_value['counts']={'independently_approved_installed_and_content_delivered':556}
    tracker_value['canonical_adoption_claimed']=True
    tracker_value['installation']=review.ref('reports/solution-review/release-source91-installation-v1.json')
    tracker_value['content_delivery']=review.ref(args.delivery)
    tracker_value['formal_coverage_changed']=False
    tracker_value['immutable_approved_draft_snapshot']=plan['approved_tracker']
    bodies={'book/coverage/progress.json':(json.dumps(progress,indent=2)+'\n').encode(),
            tracker:(json.dumps(tracker_value,indent=2,ensure_ascii=False)+'\n').encode()}
    paragraph=(f'Source91 content is delivered at `{commit}`. All three Pages jobs and all\n'
               '31 live asset hashes pass. The publication metadata will be committed and\n'
               'checked separately; formal correspondence for expanded answers remains pending.\n'
               f'See [actual content delivery](../../{args.delivery}).\n')
    for name in originals:
        if name in bodies:continue
        text=review.path(HISTORY+'/'+name).read_text()
        if name=='book/coverage/CONTINUATION.md':
            old='Source91 publication is pending its actual commit, push, Pages jobs and live hashes.'
            assert old in text
            text=text.replace(old,f'Source91 content `{commit}` is published; all three Pages jobs and all\n31 live hashes pass. Actual delivery metadata is recorded separately.')
        elif name=='README.md':
            text+=f'\nSource91 content `{commit}` is published. All three Pages jobs and all 31\nlive asset hashes pass; delivery metadata is recorded separately.\n'
        elif name in {'book/solutions/RELEASE.md','reports/full-coverage/README.md'}:
            text+='\n'+paragraph
        bodies[name]=text.encode()
    for name,data in bodies.items():
        assert review.path(name).read_bytes() in (review.path(HISTORY+'/'+name).read_bytes(),data), 'Unplanned metadata edit: '+name
    for name,data in bodies.items():
        destination=review.path(name)
        assert destination.read_bytes() in (review.path(HISTORY+'/'+name).read_bytes(),data), 'Metadata edited after preflight: '+name
        if destination.read_bytes()!=data:release.atomic_copy(destination,data)
    assert all(review.path(n).read_bytes()==b for n,b in bodies.items()), 'Metadata edited before completion'
    ready={'status':'passed_source91_content_delivered_metadata_ready','content_commit':commit,
        'counts':plan['counts'],'site_source91_sha256':plan['site_source91_sha256'],
        'actual_content_delivery_evidence':evidence,'documents':[review.ref(n) for n in bodies],
        'preserved_document_sources':[review.ref(HISTORY+'/'+n) for n in originals],
        'helper':review.ref(Path(__file__).relative_to(review.ROOT).as_posix()),
        'formal_coverage_promoted':False,'metadata_delivery_claimed':False}
    review.json_put(READY,ready)
    print(json.dumps({'status':ready['status'],'content_commit':commit,'ready':review.ref(READY)}))


if __name__=='__main__':main()

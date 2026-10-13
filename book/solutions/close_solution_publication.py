"""Close real content and metadata delivery; keep remaining formal work explicit."""
import argparse
from datetime import datetime,timezone
import json
from pathlib import Path
import subprocess

import solution_review as review
import solution_release as release
from prepare_solution_delivery_metadata import native

PUB=review.ROOT/'reports/book/publication-repo'
FINAL='reports/solution-review/source91-publication-finish-v1.json'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--content-delivery',required=True)
    parser.add_argument('--content-native',required=True)
    parser.add_argument('--metadata-delivery',required=True)
    parser.add_argument('--metadata-native',required=True)
    args=parser.parse_args()
    fingerprint=review.ref(release.PLAN)['sha256'];plan=release.load_plan(fingerprint)
    deliveries={}
    evidence=[]
    for phase in ['content','metadata']:
        name=getattr(args,phase+'_delivery');execution=getattr(args,phase+'_native')
        value=review.read(name);commit=value['expected_commit']
        assert value['status']=='passed_source91_all31_live_assets_and_all3_Pages_jobs' and value['phase']==phase
        assert value['plan']==review.ref(release.PLAN) and value['remote_main']==commit
        assert len(value['assets'])==31 and all(r['matches'] and r['http_status']==200 for r in value['assets'])
        assert {r['source']:r['actual_sha256'] for r in value['assets']}==plan['site_source91_sha256']
        assert value['Pages_build']['commit']==commit and value['Pages_build']['status']=='built'
        run=value['selected_run'];assert run['head_sha']==commit and run['name']=='pages build and deployment'
        assert run['status']=='completed' and run['conclusion']=='success'
        assert len(value['jobs'])==3 and all(r['status']=='completed' and r['conclusion']=='success' for r in value['jobs'])
        attempt=int(Path(name).stem.rsplit('attempt',1)[1])
        assert name=='reports/solution-review/source91-'+phase+'-delivery-attempt'+str(attempt)+'.json'
        command=['python3','-B','book/solutions/verify_solution_delivery.py','--plan-sha256',fingerprint,
                 '--commit',commit,'--phase',phase,'--attempt',str(attempt)]
        completed=native(execution,command)
        assert completed['actual_workdir']==str(review.ROOT)
        assert review.read(completed['log'])['report']==review.ref(name)
        verifier=review.ref('book/solutions/verify_solution_delivery.py')
        assert value['helper']==verifier and completed['helper_sha256_before'][verifier['file']]==verifier['sha256']
        for key in ['remote_observation','Pages_build_observation','actions_runs_observation','actions_jobs_observation']:
            observed=value[key];assert observed['actual_exit_code']==0 and observed['actual_workdir']==str(PUB)
            release.exact(observed['log'])
        deliveries[phase]=value
        evidence.extend([review.ref(name),review.ref(execution)])
        for action in ['commit','push']:
            receipt='reports/solution-review/source91-'+phase+'-'+action+'-execution-v1.json'
            command=['git','push','origin','main'] if action=='push' else ['git','commit','-m',
                'Expand 251 worked solutions and review all 556 exercises' if phase=='content' else 'Record verified Source91 solution delivery']
            assert native(receipt,command)['actual_workdir']==str(PUB)
            evidence.append(review.ref(receipt))
    observations=[]
    for command in [['git','rev-parse','HEAD'],['git','rev-parse','HEAD^'],['git','ls-remote','origin','refs/heads/main'],
                    ['git','status','--porcelain=v1','--untracked-files=all'],['git','symbolic-ref','--short','HEAD']]:
        result=subprocess.run(command,cwd=PUB,capture_output=True,text=True)
        assert result.returncode==0,result.stderr
        observations.append({'actual_command':command,'actual_workdir':str(PUB),'actual_exit_code':result.returncode,
                             'stdout':result.stdout,'stderr':result.stderr})
    content=deliveries['content']['expected_commit'];metadata=deliveries['metadata']['expected_commit']
    assert observations[0]['stdout'].strip()==metadata and observations[1]['stdout'].strip()==content
    assert observations[2]['stdout'].split()[0]==metadata and not observations[3]['stdout'].strip()
    assert observations[4]['stdout'].strip()=='main'
    assert all(review.ref(n)['sha256']==h and review.sha((PUB/n).read_bytes())==h for n,h in plan['site_source91_sha256'].items())
    readiness=review.read('reports/solution-review/source91-content-delivered-metadata-ready-v1.json')
    assert readiness['content_commit']==content and readiness['counts']==plan['counts']
    local_ready=review.read('reports/solution-review/source91-release-ready-v1.json')
    assert local_ready['status']=='passed_source91_all556_release_ready_for_publication'
    for binding in local_ready['evidence']:release.exact(binding)
    audit=review.read('reports/solution-review/source91-lean-audit-export-v1.json')
    assert audit['status']=='passed_actual_source91_selected35_build_kernel_and_all_axiom_audit_export'
    assert audit['proof_files']==1267 and audit['public_theorems']==11472 and audit['fresh_build_and_all_theorem_axiom_audit']
    for binding in readiness['documents']:
        assert review.sha((PUB/binding['file']).read_bytes())==binding['sha256']
    final={'status':'passed_actual_Source91_content_and_metadata_push_Pages_all31_delivery',
        'checked_at_utc':datetime.now(timezone.utc).isoformat(),'content_commit':content,'metadata_commit':metadata,
        'counts':plan['counts'],'all556_independently_reviewed_student_solutions_delivered':True,
        'all31_live_assets_match_approved_plan':True,'successful_Pages_jobs_per_phase':3,
        'selected_proof_files':1267,'selected_public_theorems':11472,'selected_proof_audit':review.ref('reports/solution-review/source91-lean-audit-export-v1.json'),
        'release_plan':review.ref(release.PLAN),'evidence':evidence,'actual_publication_observations':observations,
        'helper':review.ref(Path(__file__).relative_to(review.ROOT).as_posix()),
        'formal_coverage_complete':False,'formal_source_correspondence_for_rewritten_answers':'pending_explicit_rebase',
        'client_application_crash_cause_diagnosed':False}
    if review.path(FINAL).exists():
        prior=review.read(FINAL)
        assert {k:v for k,v in prior.items() if k not in {'checked_at_utc','actual_publication_observations'}}=={
            k:v for k,v in final.items() if k not in {'checked_at_utc','actual_publication_observations'}}
        final=prior
    review.json_put(FINAL,final)
    name='book/coverage/progress.json';history='reports/solution-review/source-history/before-source91-final-local-closure-v1/progress.json'
    selected=next(r for r in readiness['documents'] if r['file']==name)
    if not review.path(history).exists():
        original=review.path(name).read_bytes()
        assert review.sha(original)==selected['sha256']
        review.put(history,original)
    assert review.ref(history)['sha256']==selected['sha256']
    progress=review.read(history)
    progress['last_published_commit']=metadata;progress['last_published_metadata_commit']=metadata
    progress['publication_status']='Source91_content_and_metadata_Pages_all31_live_confirmed'
    progress['live_delivery_status']='passed_Source91_content_and_metadata_Pages_all31_asset_hashes'
    progress['live_delivery_evidence'].update(metadata_commit=metadata,completed_delivery=review.ref(FINAL),
        metadata_delivery=review.ref(args.metadata_delivery),actual_metadata_delivery=review.ref(args.metadata_native),
        metadata_push_and_metadata_live_check_pending=False)
    progress['solution_depth_requirement'].update(status='all556_independently_reviewed_installed_and_delivered',
        completed_delivery=review.ref(FINAL),publication_metadata_pending=False)
    data=(json.dumps(progress,indent=2)+'\n').encode()
    destination=review.path(name)
    assert destination.read_bytes() in (review.path(history).read_bytes(),data),'Unplanned final progress edit'
    if destination.read_bytes()!=data:release.atomic_copy(destination,data)
    assert destination.read_bytes()==data
    print(json.dumps({'status':final['status'],'content_commit':content,'metadata_commit':metadata,'receipt':review.ref(FINAL)}))


if __name__=='__main__':main()

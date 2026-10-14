"""Record actual content delivery and stage its metadata as a separate commit."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h
from solution_release import atomic_copy
sys.path.insert(0,str(ROOT/'book/coverage/source91-piece01'))
import common as c

BASE='book/solutions/releases/source92-opening-v1'
PUB=ROOT/'reports/book/publication-repo'
RECEIPT='reports/solution-review/source92-delivery-v1.json'
META='reports/solution-review/source92-metadata-plan-v1.json'
HISTORY='reports/solution-review/source92-before-delivery-metadata-v1'


def close(delivery_name,native_name):
    d,n=map(h.read,[delivery_name,native_name])
    assert d['status']=='passed_all31_live_assets_and_all3_Pages_jobs' and d['phase']=='content'
    assert n['status']=='passed' and n['actual_exit_code']==0
    assert n['helper_sha256_before']==n['helper_sha256_after']
    assert h.ref(n['log'])['sha256']==n['log_sha256']
    head=d['expected_commit'];assert d['remote_main']==head
    assert len(d['assets'])==31 and all(r['matches'] for r in d['assets'])
    assert len(d['jobs'])==3 and all(j['status']=='completed' and j['conclusion']=='success' for j in d['jobs'])
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=PUB,text=True).strip()==head
    assert not subprocess.check_output(['git','status','--porcelain'],cwd=PUB).strip()
    docs=['book/coverage/progress.json','README.md','reports/full-coverage/README.md',BASE+'/README.md']
    for name in docs:c.put(HISTORY+'/'+name,c.path(name).read_bytes())
    progress=c.read(HISTORY+'/book/coverage/progress.json')
    progress['last_published_commit']=head;progress['last_published_content_commit']=head
    progress['publication_status']='Source92_content_all31_live_and_all3_Pages_jobs_confirmed'
    progress['live_delivery_status']='confirmed_Source92_content'
    progress['live_delivery_evidence']=h.ref(delivery_name)
    progress['source92_solution_refresh'].update(status='content_delivered',content_commit=head,
        content_delivery=h.ref(delivery_name))
    progress['solution_depth_requirement']['status']='source92_opening_refresh_installed_and_content_delivered'
    progress['formal_coverage_piecewise_work'].update(current_piece_publication='content_delivered',
        current_piece_commit=head,completed_delivery=h.ref(delivery_name),
        final_metadata_receipt='retained_locally_after_actual_metadata_delivery_then_published_with_next_piece')
    receipt={'status':'passed_Source92_content_delivery_metadata_receipt_pending',
        'content_commit':head,'content_delivery':h.ref(delivery_name),'native_content_delivery':h.ref(native_name),
        'content_push':h.ref('reports/solution-review/source92-content-push-native-v1.json'),
        'release':h.ref('reports/solution-review/source92-recovery-ready-v1.json'),
        'expanded_solutions':56,'reassessed_solutions':113,'selected_proof_files':1272,'selected_theorems':11522,
        'current_proved_mathematical_clauses':27,'current_complete_leaf_units':12,'complete_whole_exercises':0,
        'full_formal_coverage_complete':False,'metadata_delivery_pending':True,
        'receipt_publication_protocol':'Final metadata/live receipt is retained locally after verification and can be included in the next bounded checkpoint.'}
    h.json_put(RECEIPT,receipt)
    progress['source92_solution_refresh']['delivery_receipt']=h.ref(RECEIPT)
    progress['solution_depth_requirement']['current_release']=copy.deepcopy(progress['source92_solution_refresh'])
    notice='\nSource92 content is delivered at `'+head+'`. All three Pages jobs and all 31 live asset hashes pass. Final metadata delivery is checked separately; its receipt is retained locally for the next checkpoint.\n'
    bodies={name:(c.path(HISTORY+'/'+name).read_text()+notice).encode() for name in docs if name!='book/coverage/progress.json'}
    bodies['book/coverage/progress.json']=(json.dumps(progress,indent=2)+'\n').encode()
    for name,raw in bodies.items():
        assert c.path(name).read_bytes() in (c.path(HISTORY+'/'+name).read_bytes(),raw)
    for name,raw in bodies.items():
        if c.path(name).read_bytes()!=raw:atomic_copy(c.path(name),raw)
    files=set(docs)|{RECEIPT,delivery_name,native_name,BASE+'/verify_delivery.py',BASE+'/close_content_delivery.py',
        'reports/solution-review/source92-content-commit-v1.json','reports/solution-review/source92-final-content-index-v1.json'}
    files.update([n['log'],n['started_receipt']])
    for observation in d['observations']:files.add(observation['log']['file'])
    for filename in ['reports/solution-review/source92-content-commit-native-v1.json','reports/solution-review/source92-content-push-native-v1.json',
                     'reports/solution-review/source92-final-content-index-native-v1.json']:
        native=h.read(filename);assert native['status']=='passed' and native['actual_exit_code']==0
        files.update([filename,native['log'],native['started_receipt']])
    # Retain the first unfinished Pages observation without calling it a pass.
    for filename in ['reports/solution-review/source92-content-delivery-attempt1.json','reports/solution-review/source92-content-delivery-native-v1.json']:
        if h.path(filename).exists():
            files.add(filename)
            v=h.read(filename)
            if v.get('observations'):
                files.update(o['log']['file'] for o in v['observations'])
            if v.get('log'):files.update([v['log'],v['started_receipt']])
    records=[]
    for name in sorted(files):
        target=PUB/name
        records.append({'file':name,'source':h.ref(name),
            'before_sha256':h.sha(target.read_bytes()) if target.is_file() else None})
    h.json_put(META,{'status':'prepared_metadata_after_actual_content_delivery','expected_parent':head,
        'delivery':h.ref(delivery_name),'receipt':h.ref(RECEIPT),'files':records})
    print({'status':'content_confirmed_metadata_prepared','content_commit':head,'plan':h.ref(META)})


def stage(expected):
    assert h.ref(META)['sha256']==expected
    plan=h.read(META)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=PUB,text=True).strip()==plan['expected_parent']
    for row in plan['files']:
        assert h.ref(row['source']['file'])==row['source']
        target=PUB/row['file'];current=h.sha(target.read_bytes()) if target.is_file() else None
        assert current in {row['before_sha256'],row['source']['sha256']}
    for row in plan['files']:
        target=PUB/row['file'];target.parent.mkdir(parents=True,exist_ok=True)
        if not target.is_file() or h.sha(target.read_bytes())!=row['source']['sha256']:
            atomic_copy(target,h.path(row['source']['file']).read_bytes())
    subprocess.run(['git','add','-f','--',*[r['file'] for r in plan['files']]],cwd=PUB,check=True)
    dirty=subprocess.check_output(['git','diff','--cached','--name-only'],cwd=PUB,text=True).splitlines()
    expected_files={r['file']:r['source']['sha256'] for r in plan['files']}
    assert set(dirty)<=set(expected_files)
    assert not subprocess.check_output(['git','diff','--name-only'],cwd=PUB).strip()
    for name in dirty:assert h.sha(subprocess.check_output(['git','show',':'+name],cwd=PUB))==expected_files[name]
    for name,digest in h.read(BASE+'/plan-v1.json')['site_after_sha256'].items():
        assert h.sha((PUB/name).read_bytes())==digest
    h.json_put('reports/solution-review/source92-metadata-staged-v1.json',{
        'status':'passed_exact_metadata_index_site_assets_unchanged','plan':h.ref(META),'changed_paths':dirty,'site_assets_unchanged':31})
    print({'status':'metadata_staged','changed_paths':len(dirty),'site_assets_unchanged':31})


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('command',choices=['close','stage'])
    p.add_argument('--delivery');p.add_argument('--native');p.add_argument('--plan-sha256');a=p.parse_args()
    close(a.delivery,a.native) if a.command=='close' else stage(a.plan_sha256)

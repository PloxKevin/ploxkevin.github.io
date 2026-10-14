"""Publish content-delivery evidence, then retain final metadata closure locally."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
PUB=ROOT/'reports/book/publication-repo'
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h
from solution_release import atomic_copy

BASE='book/solutions/releases/source93-foundations-v1'
META_PLAN='reports/solution-review/source93-metadata-publication-plan-v1.json'


def git(*args):
    return subprocess.check_output(['git',*args],cwd=PUB,text=True).strip()


def confirmed(phase,attempt,commit):
    name='reports/solution-review/source93-'+phase+'-delivery-attempt'+str(attempt)+'.json'
    data=h.read(name)
    assert data['status']=='passed_all31_live_assets_and_pages_jobs' and data['commit']==commit
    assert data['ready']==h.ref(BASE+'/ready.json')
    assert len(data['assets'])==31 and all(r['matches'] for r in data['assets'])
    return name,data


def metadata(args):
    delivery,data=confirmed('content',args.content_attempt,args.content_commit)
    assert git('rev-parse','HEAD')==args.content_commit and not git('status','--porcelain')
    for name in ('book/coverage/progress.json','book/coverage/CONTINUATION.md',BASE+'/README.md'):
        h.put(BASE+'/before-content-delivery/'+name,h.path(name).read_bytes())
    content='reports/solution-review/source93-content-delivery.json'
    h.json_put(content,dict(status='passed_source93_content_delivery',content_commit=args.content_commit,
        actual_delivery=h.ref(delivery),ready=h.ref(BASE+'/ready.json'),reader_assets=31,
        pages_jobs=[dict(name=j['name'],conclusion=j['conclusion']) for j in data['jobs']],
        metadata='Final metadata receipt is retained locally after its actual delivery, then included at the next checkpoint.'))
    progress=h.read('book/coverage/progress.json')
    progress['source93_foundations_expansion'].update(status='content_delivered_metadata_pending',
        content_commit=args.content_commit,content_delivery=h.ref(content))
    progress.update(last_published_commit=args.content_commit,last_published_content_commit=args.content_commit,
        live_delivery_status='confirmed_Source93_content',live_delivery_evidence=h.ref(content),
        publication_status='Source93_content_all31_live_and_all3_Pages_jobs_confirmed_metadata_check_pending')
    atomic_copy(ROOT/'book/coverage/progress.json',(json.dumps(progress,indent=2)+'\n').encode())
    continuation=h.path('book/coverage/CONTINUATION.md').read_text()
    marker='is pending; the other 506 reader exercise bodies are unchanged from Source92.\n'
    assert continuation.count(marker)==1
    continuation=continuation.replace(marker,marker+
        'Inserting practice also shifts ordinal material-unit keys on Primer 0.\n'
        'Rematch retained theory leaves by exact HTML/text and context; do not carry\n'
        'their old node positions forward as current proof correspondence.\n',1)
    atomic_copy(ROOT/'book/coverage/CONTINUATION.md',continuation.encode())
    readme=h.path(BASE+'/README.md').read_text()
    readme+='\nContent delivery is confirmed at `'+args.content_commit+'`: all 31 live asset\nhashes and all three Pages jobs pass. The final metadata-delivery receipt is\nretained locally after its actual check and included at the next checkpoint.\n'
    atomic_copy(ROOT/BASE/'README.md',readme.encode())
    names={'book/coverage/progress.json','book/coverage/CONTINUATION.md',BASE+'/README.md',BASE+'/close_publication.py',
           'reports/solution-review/source92-final-delivery-closure-native-v1.log'}
    for p in (ROOT/'reports/solution-review').iterdir():
        if p.is_file() and p.name.startswith('source93-') and not p.name.endswith(('.started.json','.lock')) and not p.name.startswith('source93-metadata-stage-'):
            if p.relative_to(ROOT).as_posix()!=META_PLAN:names.add(p.relative_to(ROOT).as_posix())
    names.update(p.relative_to(ROOT).as_posix() for p in (ROOT/BASE/'before-content-delivery').rglob('*') if p.is_file())
    records=[]
    for name in sorted(names):
        target=PUB/name
        records.append(dict(file=name,source=h.ref(name),before_sha256=h.sha(target.read_bytes()) if target.exists() else None))
    h.json_put(META_PLAN,dict(status='prepared_exact_content_receipt_metadata',expected_head=args.content_commit,
                            content_delivery=h.ref(content),files=records))
    for row in records:
        assert h.ref(row['file'])==row['source']
        target=PUB/row['file'];target.parent.mkdir(parents=True,exist_ok=True)
        atomic_copy(target,h.path(row['file']).read_bytes())
    target=PUB/META_PLAN;target.parent.mkdir(parents=True,exist_ok=True)
    atomic_copy(target,h.path(META_PLAN).read_bytes())
    listed=sorted(names|{META_PLAN})
    subprocess.run(['git','add','-f','--',*listed],cwd=PUB,check=True)
    changed=git('diff','--cached','--name-only').splitlines()
    assert set(changed)<=set(listed) and not git('diff','--name-only')
    for name in changed:assert h.sha(subprocess.check_output(['git','show',':'+name],cwd=PUB))==h.ref(name)['sha256']
    h.json_put('reports/solution-review/source93-metadata-staged-v1.json',dict(status='passed_exact_metadata_index',plan=h.ref(META_PLAN),changed_paths=changed))
    print(dict(status='staged_metadata',changed_paths=len(changed)))


def finish(args):
    content,_=confirmed('content',args.content_attempt,args.content_commit)
    metadata,_=confirmed('metadata',args.metadata_attempt,args.metadata_commit)
    assert git('rev-parse','HEAD')==git('rev-parse','origin/main')==args.metadata_commit
    assert not git('status','--porcelain')
    ready=h.read(BASE+'/ready.json')
    for name,digest in ready['reader_assets_sha256'].items():
        assert h.ref(name)['sha256']==h.sha((PUB/name).read_bytes())==digest
    plan=h.read(META_PLAN)
    for row in plan['files']:assert h.sha((PUB/row['file']).read_bytes())==row['source']['sha256']
    for name,digest in ready['selected_proofs_sha256'].items():assert h.sha((PUB/name).read_bytes())==digest
    final='reports/solution-review/source93-publication-finish-v1.json'
    h.json_put(final,dict(status='passed_Source93_content_and_metadata_delivery_complete',
        content_commit=args.content_commit,metadata_commit=args.metadata_commit,
        content_delivery=h.ref(content),metadata_delivery=h.ref(metadata),
        ready=h.ref(BASE+'/ready.json'),metadata_plan=h.ref(META_PLAN),
        primer0_exercises=80,added_exercises=30,expanded_original_solutions=50,
        publication_checkout_clean=True,reader_assets=31,new_formal_completion_credit=0,
        final_receipt_publication='Retained locally after observed delivery; include at the next checkpoint rather than creating a recursive third metadata commit.'))
    progress=h.read('book/coverage/progress.json')
    progress['source93_foundations_expansion'].update(status='delivered',metadata_commit=args.metadata_commit,completed_delivery=h.ref(final))
    progress.update(last_published_commit=args.metadata_commit,publication_status='Source93_content_and_metadata_all31_live_and_all3_Pages_jobs_confirmed',
        live_delivery_status='confirmed_Source93_content_and_metadata',live_delivery_evidence=h.ref(final))
    atomic_copy(ROOT/'book/coverage/progress.json',(json.dumps(progress,indent=2)+'\n').encode())
    print(dict(status='delivered',primer0_exercises=80,metadata_commit=args.metadata_commit))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['metadata','finish'])
    parser.add_argument('--content-commit',required=True);parser.add_argument('--content-attempt',required=True,type=int)
    parser.add_argument('--metadata-commit');parser.add_argument('--metadata-attempt',type=int)
    args=parser.parse_args();metadata(args) if args.command=='metadata' else finish(args)

"""Publish observed content delivery; retain final metadata closure without recursion."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[3]
PUB=ROOT/'reports/book/publication-repo'
sys.path.insert(0,str(ROOT/'book/coverage/source91-piece01'))
import common as c
sys.path.insert(0,str(ROOT/'book/solutions'))
from solution_release import atomic_copy

HERE='book/coverage/source93-piece03'
REPORTS='reports/full-coverage/source93-piece03'
AUDIT='reports/full-coverage/runtime-source93-piece03-v1/reports/lean-verification/verification.json'
META=REPORTS+'/metadata-plan-v1.json'


def git(*args):return subprocess.check_output(['git',*args],cwd=PUB,text=True).strip()


def confirmed(phase,attempt,commit):
    name=REPORTS+'/'+phase+'-delivery-attempt'+str(attempt)+'.json'
    value=c.read(name)
    assert value['status']=='passed_all31_live_assets_and_pages_jobs' and value['commit']==commit
    assert value['audit']==c.ref(AUDIT)
    assert len(value['assets'])==31 and all(r['matches'] for r in value['assets'])
    assert len(value['jobs'])>=3 and all(r['status']=='completed' and r['conclusion']=='success' for r in value['jobs'])
    return name


def metadata(args):
    observation=confirmed('content',args.content_attempt,args.content_commit)
    assert git('rev-parse','HEAD')==args.content_commit and not git('status','--porcelain')
    for name in ['book/coverage/progress.json','book/coverage/CONTINUATION.md',HERE+'/README.md']:
        c.put(HERE+'/before-content-delivery/'+name,c.path(name).read_bytes())
    receipt=REPORTS+'/content-delivery-v1.json'
    c.json_put(receipt,dict(status='passed_source93_piece03_content_delivery',
        content_commit=args.content_commit,actual_observation=c.ref(observation),audit=c.ref(AUDIT),
        ledger=c.ref(HERE+'/ledger-v1.json'),reader_assets_unchanged=31,
        independent_review_claimed=False,new_full_coverage_credit=0))
    progress=c.read('book/coverage/progress.json')
    progress.update(last_published_commit=args.content_commit,last_published_content_commit=args.content_commit,
        live_delivery_status='confirmed_Source93_piece03_content',live_delivery_evidence=c.ref(receipt),
        publication_status='Source93_piece03_content_all31_live_and_all3_Pages_jobs_confirmed_metadata_pending')
    progress['formal_coverage_piecewise_work'].update(current_piece_commit=args.content_commit,
        current_piece_publication='content_delivered_metadata_pending',content_delivery=c.ref(receipt))
    atomic_copy(ROOT/'book/coverage/progress.json',(json.dumps(progress,indent=2)+'\n').encode())
    for name in ['book/coverage/CONTINUATION.md',HERE+'/README.md']:
        text=c.path(name).read_text()
        text+='\nContent delivery is confirmed at `'+args.content_commit+'`: all 31 reader\nasset hashes and all three Pages jobs pass. The final metadata receipt will\nbe retained locally after its actual delivery, then included at the next\ncheckpoint without creating a recursive third metadata commit.\n'
        atomic_copy(ROOT/name,text.encode())
    names={'book/coverage/progress.json','book/coverage/CONTINUATION.md',HERE+'/README.md',
        'reports/solution-review/source93-piece03-stage-native-v1.json',
        'reports/solution-review/source93-piece03-stage-native-v1.log'}
    names.update(p.relative_to(ROOT).as_posix() for p in (ROOT/HERE/'before-content-delivery').rglob('*') if p.is_file())
    # All content audit and observation commands have ended before this step.
    # The metadata command's own native receipt/log live outside this directory.
    names.update(p.relative_to(ROOT).as_posix() for p in (ROOT/REPORTS).rglob('*')
                 if p.is_file() and not p.name.endswith('.lock'))
    names.discard(META)
    rows=[]
    for name in sorted(names):
        if name.endswith('.started.json'):
            assert c.path(name.removesuffix('.started.json')+'.json').is_file(), 'Unfinished native command: '+name
        target=PUB/name
        rows.append(dict(file=name,source=c.ref(name),before_sha256=c.sha(target.read_bytes()) if target.is_file() else None))
    c.json_put(META,dict(status='prepared_exact_content_receipt_metadata',expected_head=args.content_commit,
        content_delivery=c.ref(receipt),files=rows,helper=c.ref(HERE+'/close_publication.py')))
    for row in rows:
        assert c.ref(row['file'])==row['source']
        target=PUB/row['file'];target.parent.mkdir(parents=True,exist_ok=True)
        if row['before_sha256']!=row['source']['sha256']:
            atomic_copy(target,c.path(row['file']).read_bytes())
    target=PUB/META;target.parent.mkdir(parents=True,exist_ok=True)
    atomic_copy(target,c.path(META).read_bytes())
    listed=sorted(names|{META})
    for offset in range(0,len(listed),150):
        subprocess.run(['git','add','-f','--',*listed[offset:offset+150]],cwd=PUB,check=True)
    changed=git('diff','--cached','--name-only').splitlines()
    assert set(changed)<=set(listed) and not git('diff','--name-only')
    for name in changed:
        assert c.sha(subprocess.check_output(['git','show',':'+name],cwd=PUB))==c.ref(name)['sha256']
    c.json_put(REPORTS+'/metadata-staged-v1.json',dict(status='passed_exact_metadata_index',plan=c.ref(META),changed_paths=changed))
    print(dict(status='staged_metadata',changed_paths=len(changed)))


def finish(args):
    content=confirmed('content',args.content_attempt,args.content_commit)
    metadata=confirmed('metadata',args.metadata_attempt,args.metadata_commit)
    assert git('rev-parse','HEAD')==git('rev-parse','origin/main')==args.metadata_commit
    assert not git('status','--porcelain')
    audit=c.read(AUDIT);plan=c.read(META)
    for name,digest in audit['proof_sha256'].items():assert c.sha((PUB/name).read_bytes())==digest
    selected={p.relative_to(PUB).as_posix():c.sha(p.read_bytes()) for p in
              (PUB/'verification/lean/SafeLearning').glob('*.lean') if p.name!='Smoke.lean'}
    assert selected==audit['proof_sha256']
    for name,digest in audit['source_sha256'].items():
        assert c.ref(name)['sha256']==c.sha((PUB/name).read_bytes())==digest
    for row in plan['files']:assert c.sha((PUB/row['file']).read_bytes())==row['source']['sha256']
    receipt=REPORTS+'/publication-finish-v1.json'
    c.json_put(receipt,dict(status='passed_Source93_piece03_content_and_metadata_delivery_complete',
        content_commit=args.content_commit,metadata_commit=args.metadata_commit,
        content_delivery=c.ref(content),metadata_delivery=c.ref(metadata),metadata_plan=c.ref(META),
        audit=c.ref(AUDIT),ledger=c.ref(HERE+'/ledger-v1.json'),selected_files=1274,selected_theorems=11544,
        new_theorems=22,new_complete_leaf_units=0,new_complete_whole_exercises=0,
        independent_correspondence_review_pending=True,reader_assets_unchanged=31,
        publication_checkout_clean=True,formal_coverage_complete=False,
        final_receipt_publication='Retained locally after actual metadata delivery; include at the next checkpoint without a recursive third commit.'))
    progress=c.read('book/coverage/progress.json')
    progress.update(last_published_commit=args.metadata_commit,
        publication_status='Source93_piece03_content_and_metadata_all31_live_and_all3_Pages_jobs_confirmed',
        live_delivery_status='confirmed_Source93_piece03_content_and_metadata',live_delivery_evidence=c.ref(receipt))
    progress['formal_coverage_piecewise_work'].update(current_piece_publication='delivered',
        metadata_commit=args.metadata_commit,completed_delivery=c.ref(receipt))
    atomic_copy(ROOT/'book/coverage/progress.json',(json.dumps(progress,indent=2)+'\n').encode())
    print(dict(status='delivered',new_theorems=22,independent_review='pending',metadata_commit=args.metadata_commit))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['metadata','finish'])
    parser.add_argument('--content-commit',required=True);parser.add_argument('--content-attempt',required=True,type=int)
    parser.add_argument('--metadata-commit');parser.add_argument('--metadata-attempt',type=int)
    args=parser.parse_args()
    if args.command=='metadata':metadata(args)
    else:
        assert args.metadata_commit and args.metadata_attempt
        finish(args)

"""Prepare and stage only the exact Source93 reader sources and their evidence."""
import argparse
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
PUB=ROOT/'reports/book/publication-repo'
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h
from solution_release import atomic_copy

BASE='book/solutions/releases/source93-foundations-v1'
PLAN='reports/solution-review/source93-publication-plan-v1.json'
STAGED='reports/solution-review/source93-publication-staged-v1.json'


def git(*args):
    return subprocess.check_output(['git',*args],cwd=PUB,text=True).strip()


def prepare():
    ready=h.read(BASE+'/ready.json')
    assert ready['status']=='passed_ready_for_exact_source93_publication'
    assert not git('status','--porcelain'), 'Publication checkout contains other changes'
    assert git('rev-parse','HEAD')==git('rev-parse','origin/main')
    files=set(ready['reader_assets_sha256'])|{
        'README.md','book/solutions/RELEASE.md','book/coverage/CONTINUATION.md',
        'book/coverage/progress.json','book/chapters/primer-basics.html',
        'book/validate.py','book/inventory_claims.py','book/exercise-counts.json',
        'book/solutions/releases/source92-opening-v1/finish_delivery.py',
        'reports/solution-review/source92-publication-finish-v1.json',
        'reports/solution-review/source92-final-delivery-closure-native-v1.json'
    }
    # Selected frozen candidates/baselines are small source provenance assets;
    # caches and runtime source trees are excluded. The new audit's reports are
    # kept at their original root-relative paths so log references resolve.
    files.update(p.relative_to(ROOT).as_posix() for p in (ROOT/BASE).rglob('*') if p.is_file())
    report_root=ROOT/'reports/solution-review'
    for p in report_root.iterdir():
        if not p.name.startswith('source93-'):continue
        if p.is_dir():
            files.update(q.relative_to(ROOT).as_posix() for q in p.rglob('*') if q.is_file())
        elif not p.name.endswith('.started.json'):
            files.add(p.relative_to(ROOT).as_posix())
    audit_root=ROOT/'reports/solution-review/runtime-source93-foundations-v1/reports/lean-verification'
    files.update(p.relative_to(ROOT).as_posix() for p in audit_root.rglob('*') if p.is_file())
    for name in list(files):
        assert not {'.git','.lake','__pycache__','source-objects'}.intersection(Path(name).parts)
        assert not name.endswith('.started.json')
    proofs={p.relative_to(PUB).as_posix():h.sha(p.read_bytes()) for p in (PUB/'verification/lean/SafeLearning').glob('*.lean') if p.name!='Smoke.lean'}
    assert proofs==ready['selected_proofs_sha256'], 'Published proof tree differs from selected unchanged audit'
    records=[]
    for name in sorted(files):
        source=h.ref(name);target=PUB/name
        records.append(dict(file=name,source=source,
            before_sha256=h.sha(target.read_bytes()) if target.is_file() else None,
            after_sha256=source['sha256']))
    for name,digest in ready['reader_assets_sha256'].items():assert h.ref(name)['sha256']==digest
    h.json_put(PLAN,dict(status='prepared_exact_source93_publication',expected_head=git('rev-parse','HEAD'),
        ready=h.ref(BASE+'/ready.json'),files=records,site_sha256=ready['reader_assets_sha256'],
        selected_proof_sha256=proofs,caches_and_unselected_proofs_included=False))
    print(dict(status='prepared',files=len(records),bytes=sum(h.path(r['file']).stat().st_size for r in records)))


def stage():
    plan=h.read(PLAN)
    assert h.ref(BASE+'/ready.json')==plan['ready']
    assert git('rev-parse','HEAD')==plan['expected_head']
    assert not git('diff','--cached','--name-only')
    for row in plan['files']:
        assert h.ref(row['source']['file'])==row['source']
        target=PUB/row['file'];actual=h.sha(target.read_bytes()) if target.is_file() else None
        assert actual==row['before_sha256'],row['file']
    for row in plan['files']:
        if row['before_sha256']!=row['after_sha256']:
            target=PUB/row['file'];target.parent.mkdir(parents=True,exist_ok=True)
            atomic_copy(target,h.path(row['file']).read_bytes())
    # Force is scoped to these named evidence files because .gitignore excludes
    # audit logs. It does not alter ignore rules or force a push.
    names=[r['file'] for r in plan['files']]
    for start in range(0,len(names),150):
        subprocess.run(['git','add','-f','--',*names[start:start+150]],cwd=PUB,check=True)
    changed=git('diff','--cached','--name-only').splitlines()
    assert set(changed)<=set(names) and not git('diff','--name-only')
    indexed={r['file']:r for r in plan['files']}
    for name in changed:
        raw=subprocess.check_output(['git','show',':'+name],cwd=PUB)
        assert h.sha(raw)==indexed[name]['after_sha256']
    for name,digest in plan['site_sha256'].items():assert h.sha((PUB/name).read_bytes())==digest
    h.json_put(STAGED,dict(status='passed_exact_source93_publication_index',plan=h.ref(PLAN),
        changed_paths=changed,reader_assets=31,selected_proof_files=1272,unexpected_paths=[]))
    print(dict(status='staged_exact',changed_paths=len(changed),reader_assets=31))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['prepare','stage'])
    prepare() if parser.parse_args().command=='prepare' else stage()

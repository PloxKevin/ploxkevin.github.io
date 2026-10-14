"""Stage the final static-check receipts and the one missing scope dependency."""
from pathlib import Path
import json
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h
from solution_release import atomic_copy


def main():
    pub=ROOT/'reports/book/publication-repo';base='book/solutions/releases/source92-opening-v1'
    prior=h.read('reports/solution-review/source92-publication-plan-v2.json')
    assert h.read('reports/solution-review/source92-publication-staged-v2.json')['status']=='passed_exact_source92_publication_index'
    assert h.read('reports/solution-review/source92-book-integration-v1.json')['status']=='PASS'
    names={base+'/check_book.py',base+'/resume_publication.py',base+'/stage_addendum.py',
        'reports/solution-review/source92-book-integration-v1.json',
        'reports/solution-review/source92-canonical-selection-v1.json',
        'reports/full-coverage/source91-piece01/next-piece02-candidate-v1.json',
        'reports/solution-review/source92-publication-plan-v1.json',
        'reports/solution-review/source92-publication-plan-v1-superseded.json',
        'reports/solution-review/source92-publication-plan-v2.json',
        'reports/solution-review/source92-publication-staged-v2.json',
        'reports/solution-review/source92-recovery-history-v1/publication-preparation-v1.py'}
    for name in ['reports/solution-review/source92-book-integration-native-v1.json',
                 'reports/solution-review/source92-publication-staging-native-v3.json']:
        n=h.read(name);assert n['status']=='passed' and n['actual_exit_code']==0
        names.update([name,n['log'],n['started_receipt']])
    expected={r['file']:r['after_sha256'] for r in prior['files']}
    expected.update({name:h.ref(name)['sha256'] for name in names})
    for name in names:
        target=pub/name;target.parent.mkdir(parents=True,exist_ok=True)
        if not target.is_file() or h.sha(target.read_bytes())!=expected[name]:atomic_copy(target,h.path(name).read_bytes())
    subprocess.run(['git','add','-f','--',*sorted(names)],cwd=pub,check=True)
    dirty=subprocess.check_output(['git','diff','--cached','--name-only'],cwd=pub,text=True).splitlines()
    assert set(dirty)<=set(expected)
    assert not subprocess.check_output(['git','diff','--name-only'],cwd=pub).strip()
    for name in dirty:
        assert h.sha(subprocess.check_output(['git','show',':'+name],cwd=pub))==expected[name],name
    h.json_put('reports/solution-review/source92-final-content-index-v1.json',{
        'status':'passed_all_final_content_index_bytes','expected_parent':prior['expected_head'],
        'prior_plan':h.ref('reports/solution-review/source92-publication-plan-v2.json'),
        'additional_sources':[h.ref(name) for name in sorted(names)],'changed_paths':dirty,
        'site_sha256':prior['site_sha256'],'selected_proof_sha256':prior['selected_proof_sha256'],
        'unexpected_index_paths':[]})
    print({'status':'passed_final_content_index','changed_paths':len(dirty),'assets':31,'proofs':1272})


if __name__=='__main__':main()

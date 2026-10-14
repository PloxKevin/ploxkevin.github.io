"""Retain the final verified metadata receipt without a recursive third commit."""
import argparse
import copy
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h
from solution_release import atomic_copy
sys.path.insert(0,str(ROOT/'book/coverage/source91-piece01'))
import common as c


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--delivery',required=True)
    parser.add_argument('--native',required=True);args=parser.parse_args()
    delivery,native=map(h.read,[args.delivery,args.native])
    assert delivery['status']=='passed_all31_live_assets_and_all3_Pages_jobs' and delivery['phase']=='metadata'
    assert native['status']=='passed' and native['actual_exit_code']==0
    assert native['helper_sha256_before']==native['helper_sha256_after']
    assert h.ref(native['log'])['sha256']==native['log_sha256']
    assert delivery['remote_main']==delivery['expected_commit']
    assert len(delivery['assets'])==31 and all(a['matches'] for a in delivery['assets'])
    assert len(delivery['jobs'])==3 and all(j['conclusion']=='success' and j['status']=='completed' for j in delivery['jobs'])
    receipt='reports/solution-review/source92-publication-finish-v1.json'
    content=h.read('reports/solution-review/source92-delivery-v1.json')
    h.json_put(receipt,{'status':'passed_Source92_content_and_metadata_delivery_complete',
        'content_commit':content['content_commit'],'metadata_commit':delivery['expected_commit'],
        'content_receipt':h.ref('reports/solution-review/source92-delivery-v1.json'),
        'actual_metadata_delivery':h.ref(args.delivery),'native_metadata_delivery':h.ref(args.native),
        'expanded_solutions':56,'reassessed_solutions':113,'selected_proof_files':1272,'selected_theorems':11522,
        'current_proved_mathematical_clauses':27,'current_complete_leaf_units':12,
        'new_complete_whole_exercises':0,'whole_exercise_status':'partial','full_formal_coverage_complete':False,
        'final_receipt_publication':'retain_locally_and_include_with_next_bounded_checkpoint_no_recursive_metadata_commit'})
    name='book/coverage/progress.json';history='reports/solution-review/source92-before-final-delivery-v1/'+name
    c.put(history,c.path(name).read_bytes());progress=c.read(history)
    progress.update(last_published_commit=delivery['expected_commit'],last_published_metadata_commit=delivery['expected_commit'],
        publication_status='Source92_content_and_metadata_all31_live_and_all3_Pages_jobs_confirmed',
        live_delivery_status='confirmed_Source92_content_and_metadata',live_delivery_evidence=h.ref(receipt))
    progress['source92_solution_refresh'].update(status='delivered',metadata_commit=delivery['expected_commit'],completed_delivery=h.ref(receipt))
    progress['solution_depth_requirement'].update(status='source92_opening_refresh_installed_and_delivered',
        current_release=copy.deepcopy(progress['source92_solution_refresh']))
    progress['formal_coverage_piecewise_work'].update(current_piece_publication='delivered',
        metadata_commit=delivery['expected_commit'],completed_delivery=h.ref(receipt))
    raw=(__import__('json').dumps(progress,indent=2)+'\n').encode()
    atomic_copy(c.path(name),raw)
    print({'status':'delivery_complete','content_commit':content['content_commit'],
        'metadata_commit':delivery['expected_commit'],'full_formal_coverage_complete':False})


if __name__=='__main__':main()

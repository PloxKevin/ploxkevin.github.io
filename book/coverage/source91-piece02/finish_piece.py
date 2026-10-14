"""Record only correspondence supported by both the reviews and actual audit."""
from pathlib import Path
import copy
import sys

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'book/coverage/source91-piece01'))
import common as c

BASE='reports/full-coverage/source91-piece02'
PREP=BASE+'/landscape-ar-part-ii-independent-preparation-v1.json'
REVIEW=BASE+'/landscape-ar-part-ii-new-bridge-independent-amendment-v1.json'
AUDIT='reports/full-coverage/runtime-source91-piece02-v1/reports/lean-verification/verification.json'
NATIVE=BASE+'/selected-audit-native-v1.json'
LEDGER='book/coverage/source91-piece02/ledger-v1.json'


def main():
    prep,review,audit,native=map(c.read,[PREP,REVIEW,AUDIT,NATIVE])
    assert native['status']=='passed' and native['actual_exit_code']==0
    assert native['helper_sha256_before']==native['helper_sha256_after']
    assert c.ref(native['log'])['sha256']==native['log_sha256']
    assert audit['status']=='passed' and audit['proof_file_count']==1272 and audit['theorem_count']==11522
    assert len(audit['axiom_dependencies'])==11522
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in audit['axiom_dependencies'].values())
    assert not prep['binding_errors'] and not review['binding_errors'] and not review['errors_in_mathematical_bodies']
    assert review['original_preparation']==c.ref(PREP)
    for proof in prep['proof_sources']+[review['new_proof_source']]:
        c.exact(proof)
        assert audit['proof_sha256'][proof['file']]==proof['sha256']
    c.exact(prep['reader_source']);c.exact(prep['inventory'])
    raw=c.path(prep['reader_source']['file']).read_bytes()
    fragment=prep['fragment']
    assert c.sha(raw[fragment['start_byte']:fragment['end_byte']])==fragment['sha256']
    names=set(audit['axiom_dependencies'])
    amendments={r['id']:r for r in review['claims']}
    clauses=[]
    for source in prep['claims']:
        row=copy.deepcopy(source);update=amendments[row['id']]
        assert row['exact_unit_html_sha256']==update['exact_unit_html_sha256']
        assert row['exact_unit_text_sha256']==update['exact_unit_text_sha256']
        row['lean_declarations']=sorted(set(update['existing_lean_declarations']+update.get('new_bridge_declarations',[])))
        assert set(row['lean_declarations'])<=names
        row['remaining_gaps']=update['remaining_gaps']
        if row['id'].endswith(('direct-tail-evaluation-advice','analytical-versus-numerical-exactness')):
            row['status']='reviewed_instruction_no_mathematical_completion_credit'
        elif row['remaining_gaps']:
            row['status']='partial' if row['lean_declarations'] else 'pending'
        else:
            row['status']='proved'
        clauses.append(row)
    proved=[r for r in clauses if r['status']=='proved']
    assert len(proved)==15
    units=[]
    for original,amend in zip(prep['source_units'],review['source_units']):
        assert original['key']==amend['key']
        a,b=original['start_byte'],original['end_byte']
        assert c.sha(raw[a:b])==original['exact_html_sha256']==amend['exact_html_sha256']
        assert c.sha(original['exact_text'].encode())==original['exact_text_sha256']
        row=copy.deepcopy(original)
        row['lean_declarations']=sorted(set(amend['existing_mathematical_declaration_support']+amend['new_mathematical_declaration_support']))
        assert set(row['lean_declarations'])<=names
        row['remaining_gaps']=amend['remaining_gaps']
        row['status']='partial' if row['remaining_gaps'] else 'proved'
        row['whole_leaf_complete']=not row['remaining_gaps']
        units.append(row)
    assert len(units)==6 and sum(r['whole_leaf_complete'] for r in units)==5
    ledger={'schema':'source91.formal.piece02.v1','source_version':'Source91','piece':2,
        'status':'partial_current_source_correspondence','exercise_key':'landscape.html::exercise-19',
        'exercise_status':'partial','part_ii_status':'partial_numerical_warning_leaf_pending',
        'reader_source':prep['reader_source'],'inventory':prep['inventory'],'fragment':fragment,
        'claims':clauses,'source_units':units,'audit':c.ref(AUDIT),'native_execution':c.ref(NATIVE),
        'independent_preparation':c.ref(PREP),'independent_bridge_review':c.ref(REVIEW),
        'counts':{'proved_mathematical_clauses':15,'complete_leaf_units':5,'partial_leaf_units':1,
                  'new_complete_whole_exercises':0,'new_theorems':14,'selected_files':1272,'selected_theorems':11522},
        'remaining_gaps':['The mixed erfc paragraph still needs a nonvacuous numerical model for CDF rounding and tail underflow; true-probability positivity does not prove machine arithmetic.',
                          'Part(iii), the full answer/exercise and all containing parent scopes remain pending.',
                          'Remaining Source91/current-source exercises require explicit correspondence or rebase.'],
        'formal_coverage_complete':False,'publication_status':'pending_actual_delivery'}
    c.json_put(LEDGER,ledger)
    c.json_put(BASE+'/completion-v1.json',{'status':'passed15_mathematical_clauses_five_leaves_whole_exercise_partial',
        'ledger':c.ref(LEDGER),'counts':ledger['counts'],'audit':c.ref(AUDIT),'native':c.ref(NATIVE),
        'formal_coverage_complete':False,'part_ii_fully_complete':False,'publication_status':'pending'})
    print({'status':'passed','proved_clauses':15,'complete_leaves':5,'whole_exercise':'partial'})


if __name__=='__main__': main()

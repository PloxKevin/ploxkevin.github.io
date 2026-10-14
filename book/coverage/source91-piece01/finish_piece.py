"""Promote only twelve independently reviewed and kernel-checked Source91 clauses."""
import copy
import json
import sys
from pathlib import Path
import common as c
import export_audit
import prepare_runtime

PACKET='book/coverage/source91-piece01/claims-v2.json'
REVIEW='reports/full-coverage/source91-piece01/landscape-ar-part-i-independent-source-review-v1.json'
LEDGER='book/coverage/source91-piece01/ledger-v1.json'
REPORT='reports/full-coverage/source91-piece01/completion-v1.json'
HISTORY='reports/full-coverage/source91-piece01/history/before-completion-v1'


def main():
    packet=c.read(PACKET);review=c.read(REVIEW);export=c.read(export_audit.REPORT)
    assert review['status']=='approved' and review['errors']==[]
    assert review['claim_packet']==c.ref(PACKET) and review['inventory']==packet['inventory']
    assert review['whole_exercise_status_after_success']=='partial'
    assert export['status']=='passed_actual_source91_piece01_selected_build_fresh4_kernel_and_all_axiom_audit_export'
    for binding in [export['native_execution'],export['original_native_report'],export['runtime_plan'],export['runtime_preparation']]:c.exact(binding)
    native=c.read(export['native_execution']['file'])
    assert native['status']=='passed' and native['actual_exit_code']==0 and native['helper_sha256_before']==native['helper_sha256_after']
    assert c.ref(native['log'])['sha256']==native['log_sha256']
    audit=c.read(export['original_native_report']['file'])
    assert audit['status']=='passed' and audit['proof_file_count']==1271 and audit['theorem_count']==11508
    assert all(row['exit_code']==0 for row in audit['checks'])
    assert len(audit['axiom_dependencies'])==11508
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in audit['axiom_dependencies'].values())
    names={r['name'] for r in audit['declarations']}
    assert len(names)==len(audit['declarations'])==11508 and names==set(audit['axiom_dependencies'])
    c.exact(packet['reader_source']);c.exact(packet['inventory'])
    assert audit['source_sha256'][packet['reader_source']['file']]==packet['reader_source']['sha256']
    for binding in packet['proof_sources']:
        c.exact(binding);assert audit['proof_sha256'][binding['file']]==binding['sha256']
    claims_by_id={r['id']:r for r in review['claims']}
    assert len(review['claims'])==len(claims_by_id)==12 and set(claims_by_id)=={r['id'] for r in packet['claims']}
    for candidate in packet['claims']:
        decision=claims_by_id[candidate['id']]
        assert decision['verdict']=='approved' and not decision['remaining_gaps']
        assert decision['statement_in_prose']==candidate['statement_in_prose']
        assert decision['lean_declarations']==candidate['lean_declarations']
        assert set(decision['lean_declarations'])<=names
        assert decision['exact_html_sha256']==candidate['source_fragment']['html_sha256']
    raw=c.exact(packet['reader_source']).read_bytes()
    fragment=packet['part_i'];assert c.sha(raw[fragment['start_byte']:fragment['end_byte']])==fragment['sha256']
    units={r['key']:r for r in review['source_units']}
    assert len(review['source_units'])==len(units)==7 and set(units)=={r['source_unit']['key'] for r in packet['source_units']}
    for row in packet['source_units']:
        decision=units[row['source_unit']['key']]
        assert decision['verdict']=='approved' and decision['full_leaf_mathematical_scope_reviewed'] and not decision['remaining_gaps']
        assert decision['start_byte']==row['start_byte'] and decision['end_byte']==row['end_byte']
        assert decision['exact_html_sha256']==row['html_sha256']==c.sha(raw[row['start_byte']:row['end_byte']])
        assert decision['exact_text']==row['source_unit']['source_text']
        assert decision['exact_text_sha256']==row['source_unit']['text_sha256']==c.sha(decision['exact_text'].encode())
        assert set(decision['lean_declarations'])<=names
    ledger={'schema_version':1,'status':'partial_current_Source91_formal_correspondence',
        'piece':1,'source_version':'Source91','inventory':packet['inventory'],'reader_source':packet['reader_source'],
        'exercise_key':packet['exercise']['key'],'exercise_status':'partial','completed_subpart':'(i)',
        'claims':[dict(copy.deepcopy(r),status='proved',independent_review=c.ref(REVIEW)) for r in review['claims']],
        'complete_leaf_material_units':copy.deepcopy(review['source_units']),
        'exact_part_i_fragment':fragment,'audit_export':c.ref(export_audit.REPORT),
        'independent_source_review':c.ref(REVIEW),'claim_packet':c.ref(PACKET),
        'counts':{'reviewed_proved_clauses':12,'complete_leaf_material_units':7,'newly_complete_whole_exercises':0},
        'remaining_gaps':['Exercise1.5 parts(ii) and(iii), including Gaussian tail/erfc integrals, zero-noise case, numerical enclosures and joint-failure interpretation, require later current-source pieces.',
            'Whole answer/exercise/ancestor units are not complete.',
            'All other Source91 exercise/material correspondence remains to be explicitly rebased or reviewed.'],
        'historical_Source90_counts_unchanged':True,'formal_coverage_complete':False}
    c.json_put(LEDGER,ledger)
    result={'status':'passed_source91_piece01_twelve_clauses_seven_leaves_whole_exercise_partial',
        'ledger':c.ref(LEDGER),'independent_source_review':c.ref(REVIEW),'audit_export':c.ref(export_audit.REPORT),
        'proof_files':1271,'public_theorems':11508,'newly_selected_theorems':36,'fresh_kernel_modules':4,
        'proved_clauses':12,'complete_whole_leaf_units':7,'newly_completed_exercises':0,
        'whole_exercise_status':'partial','next_piece':'Exercise1.5 part(ii): actual Gaussian tails and indicator-sum expectation.',
        'helper':c.ref('book/coverage/source91-piece01/finish_piece.py'),'publication_status':'pending_actual_commit_push_Pages_and_live_checks',
        'formal_coverage_complete':False}
    c.json_put(REPORT,result)
    docs=['book/coverage/progress.json','book/coverage/CONTINUATION.md']
    for name in docs:
        saved=HISTORY+'/'+name
        if not c.path(saved).exists():c.put(saved,c.path(name).read_bytes())
    progress=c.read(HISTORY+'/book/coverage/progress.json')
    progress['current_selected_proof_audit']=export['relocated_report']
    progress['current_selected_proof_audit_scope']='1271 selected files / 11508 theorems; only the exact Source91 piece01 part(i) correspondence is newly closed.'
    progress['formal_coverage_piecewise_work']={'source_version':'Source91','status':'in_progress',
        'completed_local_pieces':[c.ref(REPORT)],'current_piece':1,'current_piece_publication':'pending',
        'selected_proof_files':1271,'selected_public_theorems':11508,'new_reviewed_proved_clauses':12,
        'new_complete_leaf_units':7,'new_complete_whole_exercises':0,
        'next_piece':result['next_piece'],'Source90_coverage_counts_remain_historical':True}
    progress['publication_status']='Source91_formal_piece01_locally_complete_publication_pending'
    continuation='''# Continue formal coverage one piece at a time

Source91 piece01 closes **Exercise 1.5 part(i)**: centering/unrolling, actual Gaussian
noise and state moments, the geometric variance formula, stationary Gaussian
characterization, distribution convergence on one infinite noise space, and the
distinction from almost-sure path convergence. Twelve mathematical clauses and
seven complete direct leaf units have independent source correspondence and a
real pinned Lean build, four fresh kernel replays and all-theorem axiom audit.
The selected bundle contains 1,271 files and 11,508 theorems (36 newly selected).
See `source91-piece01/ledger-v1.json` and
`../../reports/full-coverage/source91-piece01/completion-v1.json`.

The whole exercise remains partial. Next: **Exercise 1.5 part(ii)**, Gaussian
tail probabilities, expectation of the finite indicator sum, deterministic
zero-noise handling and the integral definition of erfc. Part(iii) numerical
enclosures and joint-failure interpretation follow as later pieces.

The Source91 inventory has 556 exercises and 14,270 overlapping material units.
Only this exact piece has new current-source formal completion credit. Original
Source90 counts (539 complete / 6 partial / 11 pending; 4,878 reviewed material
units) remain historical, with their exact owner ledgers and original proofs.
Rebase further entries explicitly; successful compilation alone is not source
correspondence. Keep every earlier proof and failure record.

All 556 student solutions remain independently depth-reviewed and published:
251 expanded, 305 retained. The questions and hints stay preserved. Source91's
solution release content/metadata commits are e98d4675 / 54a8fac0.

This formal piece is locally complete; its own commit/push/Pages/live delivery
is recorded separately. Publication checkout: `../../reports/book/publication-repo`.
Run the exact selected audit in `../../reports/full-coverage/runtime-source91-piece01-v1`.
Canonical working proofs still include eight unselected future modules. Native
commands use `checks/checkpoint35-root/record_native35.py`; interrupted or failed
attempts require fresh names. Never copy archives, source objects or .lake caches
into publication. Final bloat cleanup remains due after full coverage and final
publication. Client/application crash causes remain undiagnosed.
'''
    bodies={'book/coverage/progress.json':(json.dumps(progress,indent=2)+'\n').encode(),
            'book/coverage/CONTINUATION.md':continuation.encode()}
    sys.path.insert(0,str(c.ROOT/'book/solutions'));from solution_release import atomic_copy
    for name,data in bodies.items():assert c.path(name).read_bytes() in (c.path(HISTORY+'/'+name).read_bytes(),data)
    for name,data in bodies.items():
        assert c.path(name).read_bytes() in (c.path(HISTORY+'/'+name).read_bytes(),data)
        if c.path(name).read_bytes()!=data:atomic_copy(c.path(name),data)
    assert all(c.path(n).read_bytes()==b for n,b in bodies.items())
    c.json_put('reports/full-coverage/source91-piece01/documentation-v1.json',{'status':'passed_exact_piece01_local_documentation',
        'documents':[c.ref(n) for n in bodies],'originals':[c.ref(HISTORY+'/'+n) for n in docs],'formal_coverage_complete':False})
    print({'status':result['status'],'ledger':c.ref(LEDGER),'report':c.ref(REPORT)})


if __name__=='__main__':main()

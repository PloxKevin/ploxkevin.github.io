"""Bind the actual audit and source mapping, with review provenance explicit."""
import argparse
import copy
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'book/coverage/source91-piece01'))
import common as c

HERE='book/coverage/source93-piece03'
REPORTS='reports/full-coverage/source93-piece03'
RUNTIME='reports/full-coverage/runtime-source93-piece03-v1'
AUDIT=RUNTIME+'/reports/lean-verification/verification.json'
NATIVE=REPORTS+'/selected-audit-native-v1.json'
NEW_IDS={
    'landscape-1.5-part-ii::cdf-rounding-and-false-zero',
    'landscape-1.5-part-ii::underflow-caveat',
    'landscape-1.5-part-ii::positive-count-rejects-zero-budget'}
INSTRUCTIONS={
    'landscape-1.5-part-ii::direct-tail-evaluation-advice',
    'landscape-1.5-part-ii::analytical-versus-numerical-exactness'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--review',help='Exact independent review receipt, if explicitly authorized and completed.')
    parser.add_argument('--version',type=int,default=1,help='Fresh immutable output version for a later review amendment.')
    args=parser.parse_args()
    assert args.version>0
    packet=c.read(HERE+'/claims-v1.json');prep=c.read(HERE+'/runtime-preparation-v1.json')
    audit=c.read(AUDIT);native=c.read(NATIVE)
    assert native['status']=='passed' and native['actual_exit_code']==0
    assert native['helper_sha256_before']==native['helper_sha256_after']
    assert c.ref(native['log'])['sha256']==native['log_sha256']
    assert audit['status']=='passed' and audit['proof_file_count']==1274 and audit['theorem_count']==11544
    assert audit['proof_sha256']==prep['selected_proof_sha256']
    assert audit['source_sha256']==prep['site_sha256'] and len(audit['source_sha256'])==31
    assert len(audit['axiom_dependencies'])==11544
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in audit['axiom_dependencies'].values())
    assert len(packet['new_theorem_names'])==22
    assert set(packet['new_theorem_names'])<=set(audit['axiom_dependencies'])
    for binding in packet['proof_sources']:
        c.exact(binding);assert audit['proof_sha256'][binding['file']]==binding['sha256']
        assert c.ref(RUNTIME+'/'+binding['file'])['sha256']==binding['sha256']
    for name,digest in audit['source_sha256'].items():assert c.ref(name)['sha256']==digest
    c.exact(packet['reader_source']);c.exact(packet['inventory']);c.exact(packet['previous_exact_part_ii_ledger'])
    unit=packet['source_unit'];raw=c.path(packet['reader_source']['file']).read_bytes()
    assert c.sha(raw[unit['start_byte']:unit['end_byte']])==unit['exact_html_sha256']
    assert c.sha(unit['exact_text'].encode())==unit['exact_text_sha256']
    independent=None
    if args.review:
        review=c.read(args.review)
        assert review['status']=='passed_independent_exact_source_to_statement_review'
        assert review['claims_packet']==c.ref(HERE+'/claims-v1.json')
        assert review['proof_sources']==packet['proof_sources'] and review['reader_source']==packet['reader_source']
        assert not review['binding_errors'] and not review['mathematical_errors']
        assert review['independent_of_author'] is True
        reviewed={r['id']:r for r in review['claims']}
        assert set(reviewed)=={r['id'] for r in packet['claims']}
        for row in reviewed.values():
            assert row['source_implication_sufficient'] and not row['remaining_gaps']
        independent=c.ref(args.review)
    rows=[]
    for original in packet['claims']:
        row=copy.deepcopy(original)
        assert set(row['lean_declarations'])<=set(audit['axiom_dependencies'])
        row.update(kernel_verified=True,self_reviewed=True,independently_reviewed=bool(independent))
        if row['id'] in INSTRUCTIONS:
            row['status']='reviewed_instruction_no_mathematical_completion_credit' if independent else 'instruction_self_reviewed_with_verified_model_support'
        elif row['id'] in NEW_IDS:
            row['status']='proved' if independent else 'kernel_verified_source_correspondence_pending_independent_review'
            row['completion_credit']=int(bool(independent))
        else:
            row['status']='proved_previous_independent_lineage_retained'
        rows.append(row)
    unit=copy.deepcopy(unit)
    unit.update(lean_declarations=sorted({n for row in rows for n in row['lean_declarations']}),
        status='proved' if independent else 'kernel_verified_model_self_reviewed_independent_review_pending',
        whole_leaf_complete=bool(independent),whole_leaf_completion_proposed=bool(independent),
        remaining_gaps=[] if independent else ['Independent source-to-statement review of the stated numerical model is pending.'],
        model_limits=packet['model']['exclusions'])
    counts=dict(new_theorems=22,selected_files=1274,selected_theorems=11544,
        new_kernel_verified_mathematical_clauses=3,new_independently_reviewed_proved_clauses=3 if independent else 0,
        new_complete_leaf_units=1 if independent else 0,new_complete_whole_exercises=0,
        current_rebased_reviewed_proved_clauses=30 if independent else 27,
        current_rebased_complete_leaf_units=13 if independent else 12)
    ledger=dict(schema='source93.formal.piece03.v1',source_version='Source93',piece=3,
        status='passed_model_and_independent_correspondence' if independent else 'passed_kernel_audit_self_reviewed_independent_correspondence_pending',
        exercise_key='landscape.html::exercise-19',exercise_status='partial',
        part_ii_status='complete_with_explicit_nearest_rounding_model' if independent else 'pending_independent_numerical_model_correspondence_review',
        reader_source=packet['reader_source'],inventory=packet['inventory'],source_unit=unit,claims=rows,
        packet=c.ref(HERE+'/claims-v1.json'),audit=c.ref(AUDIT),native_execution=c.ref(NATIVE),
        independent_review=independent,self_review_provenance='Primary author re-read all new proof bodies, exact source clauses, finite encoding, strict rounding cells, Gaussian existence arguments and original-process count bridge. This is not an independent review.',
        model=packet['model'],counts=counts,formal_coverage_complete=False,
        remaining_work=['Independent source-to-statement review of this numerical model.'] if not independent else [],
        next_mathematical_piece='Exercise 1.5(iii): nine-digit numerical enclosures, stationary comparison and same-process joint-failure interpretation.',
        foundation_queue='All eighty current foundation answers remain pending exact Source93 correspondence; this piece grants them no credit.',
        publication_status='pending_exact_publication',helper=c.ref(HERE+'/finish_piece.py'))
    ledger_name=HERE+'/ledger-v'+str(args.version)+'.json'
    c.json_put(ledger_name,ledger)
    c.json_put(REPORTS+'/completion-v'+str(args.version)+'.json',dict(status=ledger['status'],ledger=c.ref(ledger_name),
        counts=counts,audit=c.ref(AUDIT),native=c.ref(NATIVE),independent_review=independent,
        reader_assets_unchanged=31,formal_coverage_complete=False,whole_exercise_complete=False))
    print(dict(status=ledger['status'],**counts))


if __name__=='__main__':main()

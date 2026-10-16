"""Freeze exact Source93 rounding correspondence and an explicit selected runtime.

This helper grants no independent review or mathematical completion credit.
Old proofs are selected only from the last passing Source93 audit. Eight
unselected canonical future modules cannot enter through a directory glob.
"""
import argparse
import copy
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'book/coverage/source91-piece01'))
import common as c
sys.path.insert(0, str(ROOT/'book/solutions'))
import solution_review as h
sys.path.insert(0, str(ROOT/'book/coverage'))
from lean_names import declarations

HERE = 'book/coverage/source93-piece03'
REPORTS = 'reports/full-coverage/source93-piece03'
BASE = 'reports/solution-review/runtime-source93-foundations-v1'
AUDIT = BASE+'/reports/lean-verification/verification.json'
AUDIT_SHA = '23529f330002d8d0b9bb345870b98d7066e9018c051b88e027d3ad7d6c69b451'
REBASE = 'book/solutions/releases/source93-foundations-v1/formal-rebase-piece2.json'
REBASE_SHA = '3ac85e95190ca7f80c4cc198aadb0de3f1b7bc6f6899e2c66d13bb819822adf4'
INVENTORY = 'book/solutions/releases/source93-foundations-v1/source93-inventory/inventory.json'
RUNTIME = 'reports/full-coverage/runtime-source93-piece03-v1'
NEW = ['verification/lean/SafeLearning/'+name+'.lean' for name in [
    'CompleteModulesGaussianTailRounding', 'CompleteModulesLandscapeSource93RoundingBridge']]
P = 'SafeLearning.CompleteModulesGaussianTailRounding.'
B = 'SafeLearning.CompleteModulesLandscapeSource93RoundingBridge.'

AMENDMENTS = {
    'cdf-rounding-and-false-zero': dict(
        declarations=[P+'actual_small_positive_gaussian_tails_can_be_lost_by_cdf_subtraction',
                      P+'actual_finite_gaussian_thresholds_eventually_produce_false_zero_cdf_subtractions'],
        hypotheses=['Actual standard Gaussian CDF and strict upper tail.',
                    'Nearest rounding to the explicitly decoded finite binary64 value set in [0,1].',
                    'For the conditional theorem Q(z)<2^-54; the eventual theorem derives this at all sufficiently large real thresholds.'],
        assessment='The finite value set and nearest minimizer are constructed, not postulated. Every representable y<1 is at most 1-2^-53; the open upper rounding cell therefore maps to one. Gaussian-tail decay follows from the actual probability CDF limit. Strict positivity holds at every finite real threshold. Rounded subtraction maps 1-1 to representable zero. No roundedCDF=1 premise supplies the conclusion.'),
    'direct-tail-evaluation-advice': dict(
        declarations=[P+'actual_direct_tail_can_retain_a_positive_value_lost_by_cdf_subtraction'],
        hypotheses=['Direct evaluation means rounding the exact real Q(z), equivalently the analytic erfc expression, once.',
                    'No guarantee is asserted for the reader JavaScript approximation or an arbitrary erfc implementation.'],
        assessment='Continuity and the intermediate value theorem produce a finite nonnegative threshold with Q(z)=2^-60. An explicit exponent/fraction encoding represents that value, so direct rounding fixes it. CDF subtraction returns zero at the same threshold. This supplies a mathematical example supporting the advice, not a universal software error bound.'),
    'underflow-caveat': dict(
        declarations=[P+'actual_finite_gaussian_thresholds_eventually_underflow_even_with_direct_tails'],
        hypotheses=['The same nearest value model, with gradual subnormal values and minimum positive value 2^-1074.',
                    'All thresholds in the conclusion are finite real values; ties are excluded by strict inequalities.'],
        assessment='The exponent/fraction bounds prove that every positive representable value is at least 2^-1074, and that this floor is attained. Below half that floor the nearest result is zero. The actual Gaussian tail tends to zero but remains positive at every finite threshold, so all sufficiently large thresholds give a positive true tail and a rounded zero, also for the equal real erfc expression.'),
    'positive-count-rejects-zero-budget': dict(
        declarations=[B+'actual_source_expected_count_can_be_positive_while_its_cdf_evaluation_is_zero'],
        hypotheses=['The existing arbitrary-parameter positivity theorem covers sigma!=0 and T>0 on the original infinite noise space.',
                    'The new nonvacuous counterexample uses k=1/2, sigma=1, T=1 and a constructed real goal; 0<k<2 and sigma>0 hold.',
                    'The computed count is the printed sum of rounded CDF tail terms; T=1 requires no additional model of summation error.'],
        assessment='The one-step mean, variance and standardized threshold are proved for the literal recurrence parameters. The actual infinite-path expected violation count equals Q(z), not an assigned surrogate. At the constructed threshold its true expectation is 2^-60>0, while the rounded CDF evaluation of that same count is zero and direct evaluation retains 2^-60. No claim is made that the fixed part(iii) example has a zero display.'),
    'analytical-versus-numerical-exactness': dict(
        declarations=[P+'actual_direct_tail_can_retain_a_positive_value_lost_by_cdf_subtraction',
                      B+'actual_source_expected_count_can_be_positive_while_its_cdf_evaluation_is_zero'],
        hypotheses=['Exact refers to the analytical identity; machine approximation may differ.',
                    'The statement does not require every numerical evaluation to have nonzero error.'],
        assessment='The existing real count identity remains exact. The new same-process example exhibits a positive true expectation and a zero rounded evaluation. Terminology and implementation advice receive no extra mathematical clause count.')
}


def packet():
    assert c.ref(AUDIT)['sha256'] == AUDIT_SHA
    assert c.ref(REBASE)['sha256'] == REBASE_SHA
    previous = c.read(REBASE)
    source = previous['reader_source']; c.exact(source); c.exact(previous['inventory'])
    assert previous['inventory']['file'] == INVENTORY
    unit = copy.deepcopy(next(u for u in previous['source_units'] if u['key']=='landscape.html::node-1461'))
    raw = c.path(source['file']).read_bytes()
    exact = raw[unit['start_byte']:unit['end_byte']]
    assert c.sha(exact)==unit['exact_html_sha256']
    assert c.sha(unit['exact_text'].encode())==unit['exact_text_sha256']
    parsed = h.Document(exact)
    assert h.clean(parsed.root.text())==unit['exact_text']
    inventory = c.read(INVENTORY)
    actual = next(u for u in inventory['material_source_units'] if u['key']==unit['key'])
    assert h.clean(actual['source_text'])==unit['exact_text'] and actual['line']==unit['line']
    rows=[]
    for prior in previous['claims']:
        if prior['material_unit_key'] != unit['key']: continue
        row=copy.deepcopy(prior); name=row['id'].split('::')[-1]
        row['prior_status']=row['status']; row['completion_credit']=0
        if name in AMENDMENTS:
            new=AMENDMENTS[name]
            row['lean_declarations']=sorted(set(row['lean_declarations']+new['declarations']))
            row['actual_hypotheses']=new['hypotheses']
            row['correspondence_assessment']=new['assessment']
            row['remaining_gaps']=[]
            row['classification']=('numerical_model_mathematics' if name in [
                'cdf-rounding-and-false-zero','underflow-caveat','positive-count-rejects-zero-budget']
                else 'instruction_with_mathematical_model_support')
        row['status']='candidate_pending_kernel_audit_and_independent_source_review'
        rows.append(row)
    assert len(rows)==8
    proof_refs=[c.ref(n) for n in NEW]
    new_names=[r['name'] for n in NEW for r in declarations(c.path(n).read_text())
               if r['kind'] in {'theorem','lemma'}]
    value=dict(schema='source93.formal.piece03.v1',source_version='Source93',piece=3,
        status='compiled_candidate_not_completion_credit',reader_source=source,inventory=c.ref(INVENTORY),
        previous_exact_part_ii_ledger=c.ref(REBASE),source_unit=unit,claims=rows,
        proof_sources=proof_refs,new_theorem_names=new_names,new_theorems=len(new_names),
        model=dict(format='binary64 nonnegative real values in [0,1]; signed zeros identified',
            encoding='e:Fin 1024, f:Fin(2^52); e=0 decodes f*2^-1074; e>0 decodes (2^52+f)*2^(e-1075); retain values at most one',
            rounding='A nearest value chosen from the finite set. All warning theorems use strict cells, independent of ties.',
            evaluation='Round the exact real CDF then the subtraction, or round the exact real tail once.',
            exclusions=['No bit-level hardware/compiler primitive refinement theorem.',
                        'No certified error bound for JavaScript erfc approximation, exp, or arbitrary library routines.',
                        'No finite representability restriction or input-rounding model for z itself.',
                        'Real sums of rounded terms; the count counterexample has T=1, avoiding summation arithmetic.',
                        'No part(iii) nine-digit numerical enclosure or joint-failure probability claim.'],
            primary_specification='https://docs.oracle.com/en/java/javase/24/docs/api/java.base/java/lang/Double.html'),
        review_provenance='Authored and self-reviewed by the primary agent; independent review not yet claimed.',
        proposed_new_mathematical_clauses=3,proposed_new_complete_leaf_units=1,
        new_complete_whole_exercises=0,formal_coverage_complete=False,helper=c.ref(HERE+'/prepare_piece.py'))
    c.json_put(HERE+'/claims-v1.json',value)
    print(dict(packet=c.ref(HERE+'/claims-v1.json'),new_theorems=len(new_names),completion_credit=0))


def runtime():
    candidate=c.read(HERE+'/claims-v1.json')
    assert c.ref(AUDIT)['sha256']==AUDIT_SHA
    prior=c.read(AUDIT)
    assert prior['status']=='passed' and prior['proof_file_count']==1272 and prior['theorem_count']==11522
    selected=dict(prior['proof_sha256'])
    for binding in candidate['proof_sources']:
        c.exact(binding); assert binding['file'] not in selected
        selected[binding['file']]=binding['sha256']
    expected={**prior['proof_sha256'],**prior['source_sha256'],**prior['project_sha256']}
    expected['book/coverage/lean_names.py']=c.ref(BASE+'/book/coverage/lean_names.py')['sha256']
    inputs={AUDIT:AUDIT_SHA,HERE+'/claims-v1.json':c.ref(HERE+'/claims-v1.json')['sha256'],
            HERE+'/prepare_piece.py':c.ref(HERE+'/prepare_piece.py')['sha256']}
    origins=[]
    for name,digest in sorted(expected.items()):
        if name=='verification/lean/SafeLearning.lean': continue
        origin=BASE+'/'+name
        assert c.ref(origin)['sha256']==digest and c.ref(name)['sha256']==digest, name
        inputs[origin]=digest
        target=c.path(RUNTIME+'/'+name);target.parent.mkdir(parents=True,exist_ok=True)
        if target.exists(): assert c.sha(target.read_bytes())==digest
        else: os.link(c.path(origin),target)
        origins.append(dict(file=name,sha256=digest,origin=c.ref(origin)))
    for binding in candidate['proof_sources']:
        c.put(RUNTIME+'/'+binding['file'],c.path(binding['file']).read_bytes())
        inputs[binding['file']]=binding['sha256']
    aggregate=('\n'.join('import SafeLearning.'+Path(n).stem for n in sorted(selected))+'\n').encode()
    c.put(RUNTIME+'/verification/lean/SafeLearning.lean',aggregate)
    for part in ['build','packages']:
        target=ROOT/RUNTIME/'verification/lean/.lake'/part
        origin=ROOT/'verification/lean/.lake'/part
        assert origin.is_dir();target.parent.mkdir(parents=True,exist_ok=True)
        if target.is_symlink():assert target.resolve()==origin.resolve()
        else:
            assert not target.exists();target.symlink_to(origin.resolve(),target_is_directory=True)
    assert {p.name for p in (ROOT/RUNTIME/'verification/lean/SafeLearning').iterdir()}=={Path(n).name for n in selected}
    assert all(c.ref(n)['sha256']==digest for n,digest in inputs.items())
    c.json_put(HERE+'/runtime-preparation-v1.json',dict(status='prepared_explicit_selected1274_no_completion_credit',
        runtime=RUNTIME,previous_audit=c.ref(AUDIT),candidate_packet=c.ref(HERE+'/claims-v1.json'),
        proof_files=len(selected),expected_theorems=11522+candidate['new_theorems'],
        selected_proof_sha256=selected,site_sha256=prior['source_sha256'],origins=origins,
        protected_input_sha256=inputs,cache_mode='symlinks_to_pinned_existing_cache_no_copy',
        formal_completion_credit=0,helper=c.ref(HERE+'/prepare_piece.py')))
    print(dict(runtime=RUNTIME,selected_files=len(selected),expected_theorems=11522+candidate['new_theorems']))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['packet','runtime'])
    packet() if parser.parse_args().command=='packet' else runtime()

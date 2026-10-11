from pathlib import Path
from datetime import datetime, timezone
import json, hashlib, re
ROOT=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_text())
def P(n):
    p=Path(n);return p if p.is_absolute()else ROOT/p
def checked(r):
    p=P(r['file']);assert p.is_file()and not p.is_symlink()and H(p)==r['sha256'];return p
def ref(p):return {'file':str(p),'sha256':H(p)}
request=Path('/tmp/modules-temporal25-source-component-review-request-v1.json')
assert H(request)=='989a383b312d9b2c096512d28928a846e357b11d8c1e4086d3b277e2221d34c4'
d=J(request)
assert d['distinct_public_theorem_count']==9 and d['six_embedded_dh_bodies_exact'] is True and d['private_temporal_helper_count']==1 and d['named_or_canonical_execution_claimed'] is False
sources=[];names=[]
for s in d['actual_sources']:
    p=checked(s['source']);text=p.read_text();assert text==s['entire_actual_source_and_proof_bodies']
    assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',text)
    r=J(checked(s['actual_record']));assert r==s['entire_original_actual_record_body_and_time'] and r['actual_exit_code']==0
    assert r['actual_command']==['lake','env','lean',str(p)]and r['actual_workdir']==str(ROOT/'verification/lean')
    assert r['source_sha256_before']==r['source_sha256_after']==H(p)
    lp=checked(s['raw_log']);assert str(lp)==r['raw_log'] and H(lp)==r['raw_log_sha256'] and lp.read_bytes()==b''
    rp=checked(s['original_actual_runner']);assert str(rp)==r['actual_runner']and H(rp)==r['actual_runner_sha256']
    assert len(re.findall(r'^theorem\s+',text,re.M))==len(s['public_theorem_names'])
    sources.append(text);names.extend(s['public_theorem_names'])
assert sources[1].startswith(sources[0])and len(set(names))==9
assert len(re.findall(r'^private theorem\s+',sources[1],re.M))==1
history=d['all_actual_failed_and_passed_trial_history'];assert len(history)==8
codes=[]
for item in history:
    r=J(checked(item['actual_record']));assert r==item['entire_original_actual_record_body_and_time']
    source=checked(item['source_snapshot']);log=checked(item['raw_log']);runner=checked(item['runner'])
    assert r['source_sha256_before']==r['source_sha256_after']==H(source)
    assert r['actual_command']==['lake','env','lean',str(source)]and r['actual_workdir']==str(ROOT/'verification/lean')
    assert H(log)==r['raw_log_sha256'] and H(runner)==r['actual_runner_sha256']
    assert (log.read_bytes()==b'')==(r['actual_exit_code']==0)
    codes.append(r['actual_exit_code'])
assert codes.count(0)==2 and codes.count(1)==6
inv51=J(checked(d['original_source51_inventory']))
exkey='nn-in-the-loop.html::exercise-20';key='nn-in-the-loop.html::node-1262'
assert next(r for r in inv51['exercises']if r['key']==exkey)==d['entire_original_source51_exercise_record']
old_rows={r['key']:r for r in inv51['material_source_units']}
for row in d['entire_original_source51_question_and_answers']:assert old_rows[row['key']]==row
old_html=(ROOT/'reports/full-coverage/checkpoint-23/SafeLearning/nn-in-the-loop.html').read_text()
assert ''.join(old_html.splitlines(keepends=True)[270:307])==d['complete_original_local_section3_lines271_307']
proposal=J(checked(d['approved_unapplied_source52_proposal']))
assert proposal['replacements']==d['proposed_source52_two_exact_paragraphs']
current_html=(ROOT/'SafeLearning/nn-in-the-loop.html').read_text()
expected=old_html
for replacement in d['proposed_source52_two_exact_paragraphs']:
    assert expected.count(replacement['before'])==1
    expected=expected.replace(replacement['before'],replacement['after'])
assert current_html==expected
assert ''.join(current_html.splitlines(keepends=True)[270:307])==d['complete_original_local_section3_lines271_307']
inv52_path=ROOT/'book/coverage/inventory-after-correction52.json'
assert H(inv52_path)==H(ROOT/'book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
inv52=J(inv52_path);current_ex=next(r for r in inv52['exercises']if r['key']==exkey);current_unit=next(r for r in inv52['material_source_units']if r['key']==key)
apply_path=ROOT/'reports/full-coverage/source52-apply-execution-v1.json';post_path=ROOT/'book/coverage/checks/root-source-batch52/postwrite-source-integrity-v1.json'
actual=J(apply_path);post=J(post_path)
assert actual['actual_exit_code']==post['actual_exit_code']==0 and H(P(actual['log']))==actual['log_sha256']and post['inventory_after_sha256']==H(inv52_path)
primary=ROOT/'sources/text/2103.17106.txt';birkhoff=ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Convex/Birkhoff.lean';rearrange=ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Algebra/Order/Rearrangement.lean'
assert 'Doubly hyperdominant matrix'in primary.read_text()and 'Lemma 2' in primary.read_text()
assert 'exists_eq_sum_perm_of_mem_doublyStochastic'in birkhoff.read_text() and 'Monovary.sum_mul_comp_perm_le_sum_mul'in rearrange.read_text()
selection=J(ROOT/'reports/full-coverage/checkpoint-23-selection.json');assert len(selection['proof_files'])==1131
for n,row in selection['proof_files'].items():assert H(ROOT/n)==H(ROOT/'reports/full-coverage/checkpoint-23'/n)==row['sha256']
held={n:H(ROOT/n)for n in ['book/coverage/'+o+'.json'for o in ['core','foundations','applied','modules','applied-promotions']]}
groups=[
 {'component_id':'arbitrary_nonsymmetric_doubly_hyperdominant_repeated_monotone_qc','lean_declarations':d['actual_sources'][0]['public_theorem_names'],'hypotheses':['Arbitrary finite type with decidable equality; a real matrix with every off-diagonal entry<=0 and every row and column sum>=0, without symmetry.','One genuine Monotone real map phi with phi(0)=0, repeated across all sampled entries; arbitrary real vector.'],'per_component_reason':'All six complete bodies were read. Monotone samples genuinely Monovary; Birkhoff convex permutation decomposition and rearrangement bound the doubly stochastic product. The explicit positive scale and Option-indexed augmentation really have nonnegative entries and exact unit row/column sums. Padding by zero uses phi(0)=0, and the actual identity converts the rearrangement bound into v dot (M mulVec phi(v))>=0. Desired QC is derived, not assumed. This directly closes the stated doubly hyperdominant lemma even for nonsymmetric matrices.','missing_clauses':[]},
 {'component_id':'actual_finite_fir_prefix_toeplitz_signs_and_row_column_sums','lean_declarations':[d['actual_sources'][1]['public_theorem_names'][6]],'hypotheses':['Finite delay set S subset integers; c(d)<=0 for every nonzero delay, with sum(d in S)c(d)>=0.','Each finite horizon N, including N=0; the actual matrix entry sums c(d) where i-j=d on Fin(N+1).'],'per_component_reason':'The complete exported theorem and private injective-contribution helper were read. Each delay contributes at most once to a row/column; the zero delay is never lost at a boundary. Missing nonzero-delay contributions are nonpositive, so each actual truncated row/column sum is at least the complete coefficient sum. Distinct indices force nonzero delay, giving the actual off-diagonal sign. No doubly hyperdominance or finite-prefix positivity premise is assumed. The finite coefficient-set theorem does not yet identify the source window/filter quadratic form.','missing_clauses':[]},
 {'component_id':'genuine_monotone_channel_and_independent_diagonal_channel_prefix_qc','lean_declarations':d['actual_sources'][1]['public_theorem_names'][7:],'hypotheses':['Every channel has one time-invariant Monotone real function passing through zero; maps may differ between channels.','Finite common delay set, independent coefficient sequences each having nonpositive nonzero delays and nonnegative complete sum.','Arbitrary real sequence(s), arbitrary finite horizon; temporal coupling is only within each channel.'],'per_component_reason':'Both full bodies were read. The actual Toeplitz construction feeds the proved generic doubly hyperdominant QC, yielding 2 sum(i,j) v_i M_ij phi(v_j)>=0 for every finite prefix. Finite summation of these already derived per-channel inequalities proves the diagonal-channel assertion with distinct maps and coefficients. No l2 or uniform bound is needed for this finite algebraic result. Its exact orientation is the exported prefixToeplitz matrix sum, not an inferred FIR-window realization identity. General slope-bound loop transformations, cross-channel temporal coupling and the enlarged odd class remain outside these declarations.','missing_clauses':[]}]
report={'status':'independent_temporal25_nine_body_precise_component_review_passed_whole_source_pending','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/config21_next','original_request':ref(request),'entire_original_request_body_and_time':d,'all_nine_distinct_public_bodies_and_private_helper_fully_read':True,'six_embedded_bodies_identical_not_double_counted':True,'precise_component_count':3,'material_units':[{'key':key,'entire_inventory_record':current_unit,'components':groups,'whole_source_unit_approved':False,'remaining_gaps':d['explicit_unproved_literal_routes']}],'exercise':{'key':exkey,'entire_inventory_record':current_ex,'reviewed_components':[g['component_id']for g in groups],'whole_exercise_approved':False,'remaining_gaps':d['explicit_unproved_literal_routes']},'primary_passages_fully_read':{'arxiv_v2_local_text':ref(primary),'scope':'Appendix A Definition6/Lemma2 and Appendix B finite Toeplitz construction, plus complete local Section3 lines271–307. The paper full window equality is not inferred from the exported matrix-only theorem.','actual_birkhoff_api':ref(birkhoff),'actual_rearrangement_api':ref(rearrange)},'source51_to_actual52_identity':{'original_inventory':d['original_source51_inventory'],'current_inventory':ref(inv52_path),'actual_source52_apply':ref(apply_path),'actual_source52_postwrite':ref(post_path),'only_two_exact_proposed_paragraphs_changed':True,'entire_local_section3_unchanged':True,'current_source_sha256':H(ROOT/'SafeLearning/nn-in-the-loop.html'),'original_unapplied_request_wording_retained_as_historical':True},'all_eight_original_unique_standalone_commands_times_sources_logs_runners_checked':True,'actual_passed_empty_log_record_count':2,'actual_failed_record_count':6,'all1131_selected23_source_hashes_and_frozen_copies_exact':True,'observed_current_live_owner_sha256':held,'new_compiler_or_named_or_canonical_execution_claimed':False,'scope':'Fresh TMP-only semantic/component peer of genuine original standalone proofs. Three precise components approved with their actual hypotheses and missing_clauses[]. Full FIR realization equality, general local/common slope loop transformations, cross-channel temporal/odd extensions, whole answer(c) and whole Exercise14.6 remain pending. No live source, inventory, owner, selected proof, candidate24 or publication mutation.'}
out=Path('/tmp/modules-temporal25-independent-foundations-full-component-review-v1.json')
with out.open('x')as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':report['status'],'report':ref(out),'components':3,'distinct_public_theorems':9}))

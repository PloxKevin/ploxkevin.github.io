from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
ROOT=Path('/home/oxrexkevin/SafetyBased');REQUEST=Path('/tmp/modules-nn-corrected52-answer-b-full-source-review-request25-v1.json')
OUT=Path('/tmp/modules-nn-corrected52-answer-b-independent-foundations-full-source-review25-v1.json')
def P(n):
 p=Path(n);return p if p.is_absolute() else ROOT/p
def H(n):return hashlib.sha256(P(n).read_bytes()).hexdigest()
def R(n):return json.loads(P(n).read_text())
def C(r):assert H(r['file'])==r['sha256'];return R(r['file'])
def ref(n):return {'file':str(n),'sha256':H(n)}
assert H(REQUEST)=='4b21b19f85266a42404779c9f3319137cecfdbf8213b566685f8dee2e8b96088'
request=R(REQUEST);inventory=C(request['inventory']);assert H('book/coverage/inventory.json')==request['inventory']['sha256']
assert H(request['source']['file'])==request['source']['sha256']
literal=request['full_literal'];assert literal==next(x for x in inventory['material_source_units']if x['key']==literal['key'])
parent=request['full_parent_context'];assert parent==next(x for x in inventory['exercises']if x['key']==parent['key'])
for row in request['complete_neighboring_literal_rows']:
 assert row==next(x for x in inventory['material_source_units']if x['key']==row['key'])
 assert hashlib.sha256(row['source_text'].encode()).hexdigest()==row['text_sha256']
offer=C(request['current24_offer_only_as_exact_proof_provenance'])
held={p:H(p)for p in ['book/coverage/inventory.json','SafeLearning/nn-in-the-loop.html','book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']}
sources={};records=[]
for source,meta in request['all_three_full_canonical_proof_sources_and_actual_original_records'].items():
 assert H(source)==meta['sha256']
 text=P(source).read_text();short=re.findall(r'^theorem\s+(\w+)',text,re.M)
 names=['SafeLearning.'+Path(source).stem+'.'+x for x in short]
 assert names==meta['declarations']
 assert len(meta['actual_paired_records'])==2
 for i,pair in enumerate(meta['actual_paired_records']):
  d=C(pair['actual_record']);assert d==pair['entire_original_actual_record_body_and_time']
  assert pair['actual_exit_code']==d['actual_exit_code']==0 and d['status']=='passed'
  assert d['source']==source and d['source_sha256_before']==d['source_sha256_after']==meta['sha256']
  expected=['lake','env','lean',str(Path(source).relative_to('verification/lean'))]if i==0 else ['lake','build','SafeLearning.'+Path(source).stem]
  assert d['actual_command']==expected and d['actual_workdir']==str(ROOT/'verification/lean')
  assert H(pair['raw_log']['file'])==pair['raw_log']['sha256']==d['raw_log_sha256']
  assert H(pair['source_snapshot']['file'])==pair['source_snapshot']['sha256']==d['source_snapshot_sha256']==meta['sha256']
  records.append(pair)
 for p,h in meta['evidence_sha256'].items():assert H(p)==h
 sources[source]={'sha256':meta['sha256'],'entire_source_and_all_public_bodies_read':text,'public_declarations':names}
assert sum(len(x['public_declarations'])for x in sources.values())==16 and len(records)==6
prior=[]
for p in request['original_semantic_reviews']:
 d=C({'file':p['file'],'sha256':p['sha256']});assert d['reviewed_at_utc']==p['original_review_time']
 prior.append({'ref':{'file':p['file'],'sha256':p['sha256']},'entire_original_body_and_time':d})
dep='verification/lean/SafeLearning/CompleteModulesTanhNumerics.lean'
deptext=P(dep).read_text();assert 'actual_tanh_one_rigorous_rational_enclosure' in deptext
primary_paths=['verification/lean/.lake/packages/mathlib/Mathlib/Order/Monotone/Monovary.lean','verification/lean/.lake/packages/mathlib/Mathlib/Algebra/Order/Monovary.lean']
primary=[]
for p in primary_paths:
 text=P(p).read_text()
 if '/Order/Monotone/' in p:
  excerpt=text[text.index('@[simp]\ntheorem monovary_id_iff'):text.index('@[simp]\ntheorem antivary_id_iff')]+text[text.index('protected theorem Monotone.monovary'):text.index('protected theorem Monotone.antivary')]
 else:
  excerpt=text[text.index('lemma monovary_iff_forall_mul_nonneg'):text.index('lemma antivary_iff_forall_mul_nonpos')]+text[text.index('alias ⟨Monovary.sub_mul_sub_nonneg'):text.index('alias ⟨Antivary.sub_mul_sub_nonpos')]
 primary.append({'file':p,'sha256':H(p),'entire_direct_generic_monotonicity_api_passages_read':excerpt})
ns='SafeLearning.CompleteModulesNNTanhOffset24.'
components=[
 {'component_id':'exact_printed_matrix_and_shifted_channels','lean_declarations':[ns+'actual_both_literal_shifted_functions',ns+'actual_source_matrix_qc_is_the_difference_product'],'hypotheses':['Exact literal two centers 0 and 2, exact real 2×2 matrix [[1,-1],[-1,1]].'],'per_component_reason':'The actual source definitions and all-real v,w matrix identity give the stated difference product. At [-1,-1.5] the first factor equals1/2 and the shifted second value is tanh(1/2)-tanh2.','missing_clauses':[]},
 {'component_id':'all_four_corrected_rounded_values_and_actual_strict_negative_witness','lean_declarations':[ns+'actual_half_and_two_tanh_have_rigorous_rational_enclosures',ns+'actual_literal_unequal_tanh_offsets_violate_the_printed_coupled_qc',ns+'actual_literal_numbers_are_rounded_with_strict_non_equalities'],'hypotheses':['Exact real tanh values and literal input [-1,-1.5]; displayed decimals are nearest stated precision approximations.'],'per_component_reason':'Genuine exp-based rational bounds yield |tanh(-1)+.7616|<.00005, the shifted second value within.00005 of-.5019, their difference within.00005 of-.2597, and exact half-product within.0005 of-.130, with all four exact non-equalities. The literal matrix QC at this actual input is independently proven strictly negative.','missing_clauses':[]},
 {'component_id':'invalid_universal_QC_premise_with_limited_logical_conclusion','lean_declarations':[ns+'actual_literal_unequal_tanh_offsets_violate_the_printed_coupled_qc'],'hypotheses':['The conditional certificate actually requires this QC at every shifted input.'],'per_component_reason':'The proved concrete negative witness falsifies that universally quantified premise. The corrected sentence explicitly stops at failure of the premise and asserts no instability/stability-conclusion counterexample; no plant trajectory or final certificate conclusion is promoted.','missing_clauses':[]},
 {'component_id':'different_channels_can_reverse_order_but_one_common_monotone_function_cannot','lean_declarations':[ns+'actual_literal_unequal_tanh_offsets_violate_the_printed_coupled_qc',ns+'actual_equal_offset_group_has_the_true_monotonicity_qc'],'direct_primary_mathlib_declarations':['monovary_id_iff','Monotone.monovary','Monovary.sub_mul_sub_nonneg'],'hypotheses':['One common real monotone function for the comparison, or the actual differently shifted tanh channels for the counterexample.'],'per_component_reason':'The witness has x-y=.5>0 with the actual two-channel output difference strictly negative. For every common real monotone function, directly read Mathlib monovary_id_iff and Monovary.sub_mul_sub_nonneg give (x-y)(f(x)-f(y))≥0 by taking the identity and the same function; the selected actual equal-center tanh theorem additionally proves this over all centers/inputs. No claim is made that arbitrary two separate monotone functions preserve cross-channel order.','missing_clauses':[]}]
manifest=C(request['baseline23_manifest']);assert len(manifest['proof_files'])==1131
for p in manifest['proof_files']:assert H(p)==manifest['working_inputs_sha256'][p]
baseline_held={p:manifest['working_inputs_sha256'][p]for p in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json']}
result=R('reports/full-coverage/owner24-reviewed-candidate-integration-v1.json')
rows={x['destination']:x for x in result['exact_replacements']}
archives={}
for p,h in baseline_held.items():
 row=rows[p];assert row['before_sha256']==h and H(row['original23_byte_copy'])==h
 archives[p]={'original_sha256':h,'actual_original23_byte_copy':ref(row['original23_byte_copy'])}
assert all(H(p)==h for p,h in held.items())
out={'status':'independent_fresh_whole_corrected52_answer_b_literal_source_review_future25_tmp_only_passed','reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'errors':[],'checker':ref(Path(__file__)),'original_request':ref(REQUEST),'entire_original_request_body_and_time':request,'material_units':[{'key':literal['key'],'entire_inventory_record':literal,'whole_mathematical_unit_approved':True,'components':components,'lean_declarations':list(dict.fromkeys(n for c in components for n in c['lean_declarations'])),'hypotheses':list(dict.fromkeys(h for c in components for h in c['hypotheses'])),'per_component_reason':'Every corrected answer(b) clause is supported under its actual literal hypotheses. Four decimal assertions are approximation claims with rigorous rounding bounds and true non-equalities; the concrete coupled-QC counterexample establishes the invalid universal premise with the explicitly limited conclusion. Generic common-function ordering advice is directly matched to the actual Mathlib monotonicity API as well as the genuine equal-shift tanh theorem.','missing_clauses':[]}],'exercise':{'entire_inventory_record':parent,'whole_exercise_approved':False,'new_whole_unit_only':literal['key'],'remaining_gaps':['Full question/answer(c) multiplier and temporal/odd/local-slope routes remain separate; this answer(b)-only review does not promote them or the parent exercise.']},'entire_three_canonical_sources_and_all16_bodies_read':sources,'all_six_entire_original_actual_records_and_times_retained':records,'original_component_peers_exact_body_times_retained':prior,'direct_selected_numeric_dependency_read':{'file':dep,'sha256':H(dep),'entire_body':deptext},'direct_primary_generic_monotonicity_api_read':primary,'actual_original23_raw_owner_archives':archives,'all1131_baseline_selected_sources_exact':True,'current24_held_bytes_sha256':held,'whole_mathematical_units_approved':1,'coverage_complete':False,'scope':'New future25 whole decision for corrected current52 node1260 only. Original component decisions/reviewer times and genuine compiler history remain exact. Current24 offers/ledgers remain fixed; no new proof, named build, canonical write, whole answer(c), parent exercise, temporal, odd-class, plant-stability refutation or source methodology approval is inferred.'}
with OUT.open('x')as f:f.write(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':out['status'],'whole_units':1,'output':ref(OUT)}))

from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased');Q=Path('/tmp/modules-shifted-temporal-IQC21-full-Exercise14_6-review31-v1/modules-shifted-temporal-IQC21-entire-current-Exercise14_6-four-literals-full-review-request31-v2.json');OUT=Path('/tmp/modules-IQC21-full-independent-foundations32-semantic-v1.json')
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def sha(p):return hashlib.sha256(path(p).read_bytes()).hexdigest()
def ref(p):
 p=path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=path(r['file']);assert sha(p)==r['sha256']
 if 'bytes' in r:assert p.stat().st_size==r['bytes']
 return p
assert sha(Q)=='e4bb11615ff430c50d57a5f49a6ef77d23ef3c570f3650d2c6cd8380269a767c';q=json.loads(Q.read_bytes())
for n,h in q['all_physical_original_inputs_sha256'].items():assert sha(n)==h,n
source=checked(q['source']);text=source.read_text();sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations,without_comments
names=declarations(text);assert names==q['all_public_declarations'] and len(names)==26
assert [n['name'] for n in names if n['kind'] in ['theorem','lemma']]==q['public_theorem_names'] and len(q['public_theorem_names'])==21
masked=without_comments(text);assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',masked)
assessments=[
 'The arbitrary finite nonsymmetric doubly hyperdominant QC is derived from actual augmented doubly-stochastic construction and genuine Birkhoff/rearrangement, with only zero-padded Monovary samples as a premise. Positive scale allows multiplication back; no desired QC premise.',
 'An actual common scalar slope interval makes both nu*x-phi(x) and phi(x)-mu*x monotone, using each real chord slope; invertibility of either transformed coordinate is not presumed.',
 'The two monotone coordinates Monovary together under any finite sampling. phi(0)=0 makes the extra origin sample legitimate, giving the transformed QC for any finite nonsymmetric doubly hyperdominant matrix.',
 'Actual finite prefix Toeplitz signs/row and column sums yield the transformed hard prefix inequality for every finite horizon, with explicit coefficient sign and finite sum assumptions.',
 'Finite sums of independent shifted-tanh scalar prefix inequalities allow arbitrary centers per channel and separate coefficients, without shared-function coupling.',
 'For the actual tanh shifted by center, testing alleged oddness at s=center and the double-angle identities forces sinh(center)^3=0, hence center=0. The reverse direction uses tanh oddness. This diagnoses the missing oddness premise only.',
 'The lag-window definition equals present input, starts every delayed slot at zero, and evolves by the actual causal shift-register recurrence including boundary cases.',
 'A genuine finite bijection j->t-j turns the retained zero-padded delay sum into exactly the past-index sum, with no negative natural subtraction or omitted tail.',
 'The actual FIR coefficient matrix has the printed complete first row and first column, with zero interior, including ell=0.',
 'The full symmetric middle matrix [0,P-transpose;P,0] quadratic is exactly twice the lagged-output dot P lagged-input. Transpose identity uses scalar commutativity, without P symmetry.',
 'The supply equals the two causal lag sums; subtracting c0*w(t) removes the duplicated zero-delay contribution exactly once.',
 'Every banded Toeplitz coefficient is decomposed into the upper and lower past triangles with diagonal subtraction, with all integer/natural boundary cases handled.',
 'The finite-band prefix sum reduces to the actual retained coefficient if and only if its lag lies in the band, otherwise zero.',
 'The two zero-padded lag sums at every t<=N equal the two exact past-column expressions, with negative and positive integer lag casts matched.',
 'Summing the genuine causal window supplies and commuting finite sums gives the exact full Toeplitz quadratic over every horizon; diagonal c0 counted once. This closes the actual filter-to-prefix association.',
 'The printed loop-transform coordinates are (-b,-a), rather than (a,b). Applying the genuine Monovary QC to M-transpose swaps row and column conditions before the bilinear transpose identity and two sign changes. No symmetric-coefficient assumption.',
 'With the printed signs and actual zero-state delay-window supplies, finite sum identity plus genuine nonsymmetric QC proves every finite hard FIR horizon under the actual scalar coefficient/sign/sum/slopes/origin assumptions.',
 'Independent shifted-tanh channels each use their own zero-one slope interval and separate coefficient conditions. Summing the scalar printed window inequalities preserves every finite horizon.',
 'The actual complete middle-matrix hard IQC follows directly from the proven supply identity for every channel and time, not from an assumed hard-IQC premise.',
 'A shared activation phi=x/2 with individually valid different bound pairs and the printed doubly hyperdominant M has exact transformed value -1/8 at v=(1,1). This establishes failure of the class guarantee with unmatched bounds, not impossibility for every matrix/problem.',
 'The retained true tanh offset counterexample directly refutes the all-input nonnegative-QC premise. No instability conclusion is inferred from an invalid certificate premise.'
]
starts=list(re.finditer(r'^theorem ([A-Za-z0-9_]+)',text,re.M));assert len(starts)==21
body_assessments=[]
for i,m in enumerate(starts):
 end=text.find('\nend SafeLearning.CompleteModulesShiftedTemporalIQC31',m.start())
 if i+1<len(starts):end=min(end,starts[i+1].start())
 body=text[m.start():end].strip();body_assessments.append({'declaration':q['public_theorem_names'][i],'complete_body_sha256':hashlib.sha256(body.encode()).hexdigest(),'exact_all_input_predicates_and_conclusion':body.split(' := by',1)[0],'entire_body_read':True,'approved':True,'independent_mathematical_assessment':assessments[i]})
histories=[]
for h in q['genuine_original_compiler_histories']:
 n=json.loads(checked(h['native']).read_bytes());s=checked(h['source']);snap=checked(h['snapshot']);raw=checked(h['raw_log'])
 assert type(n['actual_exit_code']) is int and n['actual_exit_code']==h['actual_exit_code'] and n['protection_errors']==[]
 assert n['source_unchanged'] is True and n['source_sha256_before']==n['source_sha256_after']==sha(s)==sha(snap) and s.read_bytes()==snap.read_bytes()
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(ROOT/'verification/lean') and n['elapsed_seconds']>0
 assert n['raw_log_sha256']==sha(raw)
 assert all(n[k]==h['original_body_times'][k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds'])
 count=len(re.findall(r'^[^\n]+:\d+:\d+: warning:',raw.read_text(),re.M));assert count==h['emitted_diagnostic_warning_headers'],(h['trial'],count,h['emitted_diagnostic_warning_headers'])
 histories.append({'trial':h['trial'],'native':h['native'],'actual_exit_code':n['actual_exit_code'],'original_elapsed_seconds':n['elapsed_seconds'],'actual_warning_headers':count,'source':h['source'],'raw_log':h['raw_log'],'source_snapshot':h['snapshot'],'historical_context':h['actual_original_context']})
assert histories[-1]['actual_exit_code']==0 and histories[-1]['source']['sha256']==q['source']['sha256'] and histories[-1]['actual_warning_headers']==2
inventory=json.loads(checked(q['current_inventory']).read_bytes());units={u['key']:u for u in inventory['material_source_units']};exercises={e['key']:e for e in inventory['exercises']}
assert inventory['counts']['exercises']==556 and inventory['counts']['material_source_units']==12774
assert q['entire_current_exercise']==exercises[q['entire_current_exercise']['key']]
for k,v in q['entire_four_current_material_literals'].items():assert v==units[k]
assert checked(q['current_source']).read_bytes()==path('SafeLearning/nn-in-the-loop.html').read_bytes()
owner=json.loads(checked(q['immutable_original_installed_owner30']).read_bytes());oldex=next(x for x in owner['exercises'] if x['inventory_key']=='nn-in-the-loop.html::exercise-20');assert oldex==q['entire_original_partial_exercise_and_all_component_rows'] and oldex['status']=='partial'
assert all(x in owner['material_claims'] for x in q['entire_original_material_rows'])
# Full original24/25 semantic component/b scopes are retained exactly; this is
# a fresh full future-source/literal decision, not a rewrite of those histories.
for r in q['full_selected_proof_sources']:checked(r)
for r in q['complete_used_primary_Mathlib_sources']:checked(r)
for r in q['offline_primary_PDF_and_fulltext_only'].values():checked(r)
retrieval=json.loads(checked(q['actual_primary_retrieval']).read_bytes())
clause_assessment={
 'nn-in-the-loop.html::node-1254':'All six original requirement clauses are supported: actual two centers/functions, inherited bounds/origin, admitted 2x2 matrix by exact sign/sum arithmetic, actual counterexample and the complete survival distinctions in(c).',
 'nn-in-the-loop.html::node-1258':'Exact shifted functions, origin values and global zero-one chord bounds follow from the full selected offset/LFT/tanh bodies.',
 'nn-in-the-loop.html::node-1260':'Actual matrix identity, exact negative QC, four true decimal rounding enclosures and direct refutation of the uniform premise hold. The final stability conclusion is not declared false.',
 'nn-in-the-loop.html::node-1262':'Actual all-depth zero bias-free network/equal-center shared shifts; common bounds and explicit mismatch countermodel; diagonal sector and robust all-diagonal-gain full-block transfer; genuine zero-state causal FIR hard IQC on independent time-invariant channels under coefficient/sign/sum/slopes/origin conditions; exact shifted-tanh oddness iff zero. Final diagonal-T statements are bounded current-source/selected-proof association, not a new generic LMI theorem.'}
whole={k:{'entire_current_literal_approved':True,'remaining_mathematical_gaps':[],'entire_literal':q['entire_four_current_material_literals'][k],'full_clause_correspondence':v} for k,v in clause_assessment.items()}
result={'status':'passed_independent_full_shifted_temporal_IQC21_current_entire_Exercise14_6_four_literals_review','errors':[],'reviewer':'/root/foundations_recovery28','request':ref(Q),'entire_source':q['source'],'all21_complete_public_body_assessments':body_assessments,'all5_actual_filter_definitions_and26_public_names_read':True,'all9_complete_selected_sources_read':q['full_selected_proof_sources'],'complete_used_primary_sources':q['complete_used_primary_Mathlib_sources'],'additional_actual_selected_tanh_provider':ref('verification/lean/SafeLearning/CompleteModulesTheory.lean'),'entire_current_exercise':q['entire_current_exercise'],'whole_exercise_decision':{'entire_current_exercise_approved':True,'remaining_mathematical_gaps':[],'all_six_original_requirements_and_full_answer_read':True},'whole_literal_decisions':whole,'original_partial_owner30_exercise_and19_material_rows_preserved':True,'all_original14_genuine_native_histories':histories,'original24_25_proved_component_and_whole_b_bodies_times_unchanged':True,'actual_finite_FIR_realization_and_printed_nonsymmetric_transform_association_approved':True,'no_general_enlarged_odd_multiplier_or_Section3_stability_lemma_promoted':True,'source_local_box_extension_and_full_generic_stability_not_requested_or_approved':True,'invalid_QC_premise_not_identified_with_false_stability_conclusion':True,'actual_primary_retrieval':q['actual_primary_retrieval'],'primary_bounded_assessment':'The actual primary II-A shift and origin remark distinguish repeated from shifted channels. II-C gives robust sector-box full-block transfer. II-D and AppendicesA/B give coefficient sign/sum, zero-padding and finite-horizon Toeplitz route; the printed per-neuron transformation needs the common-function/common-bound restriction when coupling. The exact countermodel in the current source and new body20 makes that correction substantive. Remote full paper bytes remain offline TMP only.','remote_copyrighted_full_PDF_or_text_copied_into_repository':False,'completed_original_author_preparation':q['completed_author_preparation_native'],'current_owner_or_canonical_or_selected_aggregate_or_publication_mutation':False,'coverage_complete':False}
assert not OUT.exists();OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'passed','errors':[],'public_theorems':21,'public_names':26,'entire_exercise':True,'entire_literals':4,'histories':len(histories)}))

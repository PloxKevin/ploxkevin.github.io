from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction
import json,hashlib,re,sys
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=ROOT/'book/coverage/checks/modules-future30/matrix42-paper-PSD-eq4-supplement-v2/modules-matrix42-paper-PSD-equation4-exact-prefix-full-association-component-review-request30-v2.json'
OUT=Path('/tmp/modules-matrix42-independent-foundations30-findings-v1.json')
EXTRA=Path('/tmp/modules-matrix42-independent-foundations30-extra-primary-v1')
assert not OUT.exists() and not EXTRA.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
def path(q):
 p=Path(q['file']);return p if p.is_absolute() else ROOT/p
closed={str(REQUEST):sha(REQUEST),str(Path(__file__)):sha(__file__)}
def add(q):
 p=path(q);assert p.is_file() and sha(p)==q['sha256']
 if 'bytes' in q:assert p.stat().st_size==q['bytes']
 if p.is_relative_to(ROOT):assert not p.is_symlink() and p.resolve().is_relative_to(ROOT)
 closed[str(p)]=q['sha256'];return p
assert sha(REQUEST)=='28d2ed6c0db7ad9dfbdff7251fade1adf1e16ef275d03ef2a2e470dd031a4d87'
d=json.loads(REQUEST.read_bytes())
for n,h in d['required_evidence_artifacts_sha256'].items():add({'file':n,'sha256':h})
for n,q in d['original_closed_byte_aliases'].items():
 add(q);p=Path(n);p=p if p.is_absolute() else ROOT/p
 assert sha(p)==q['sha256']
source=add(d['source']);body=source.read_text()
sys.path.insert(0,str(ROOT/'book/coverage'));import lean_names
add(ref(ROOT/'book/coverage/lean_names.py'))
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(body))
decls=lean_names.declarations(body);names=[r['name'] for r in decls if r['kind'] in ['theorem','lemma']];other=[r for r in decls if r['kind'] not in ['theorem','lemma']]
assert len(names)==d['public_theorem_count']==42 and names==d['public_theorem_names']
assert len(decls)==d['public_declaration_count']==61 and other==d['other_public_declarations'] and len(other)==19
old=add(d['original23_entire_byte_prefix']);strict=add(d['original_strict30_strengthening_source'])
assert source.read_bytes().startswith(old.read_bytes()) and old.stat().st_size==d['original23_prefix_length_bytes']==17779
assert source.read_bytes().startswith(strict.read_bytes()) and strict.read_bytes().startswith(old.read_bytes())
assert d['exact_entire_strict30_byte_prefix_includes_namespace_end'] is True and d['original23_body_and_peer_time_retained'] is True
prior=add(d['original23_independent_full_semantic_peer']);assert sha(prior)=='32cfb57a3b1e43a25a8c705a50981aaa4f89641119d9a4e855bcdad0c681a6a9'
pd=json.loads(prior.read_bytes());assert pd['errors']==[] and pd['whole_current_Exercise19_or_any_material_literal_approved'] is False and pd['source']['sha256']==sha(old)
oldrequest=json.loads(add(d['original23_full_component_request']).read_bytes())
for k in ['entire_current_exercise','entire_original_owned_exercise_row','entire_current_material_literals','entire_used_scenario_section_context','entire_exercise_context']:
 assert d[k]==oldrequest[k]
assert d['new_genuine_native_codes']==[1,0,0] and d['new_genuine_warning_headers']==[16,16,19]
for row,code,warnings in zip(d['new_authentic_native_history'],[1,0,0],[16,16,19]):
 a=json.loads(add(row['native']).read_bytes());raw=add(row['raw_log'])
 for k in ['actual_exit_code','actual_runner_exit_code']:assert type(a[k]) is int and a[k]==code
 assert a['status']==('passed_actual_tmp_lean_only' if code==0 else 'failed_actual_tmp_lean_or_protection') and row['actual_exit_code']==code
 assert a['actual_command']==['lake','env','lean',a['source']] and a['actual_workdir']==str(ROOT/'verification/lean')
 assert a['protection_errors']==[] and a['source_unchanged'] is True
 assert sha(add(row['source']))==sha(add(row['source_snapshot']))==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']
 assert sha(raw)==a['raw_log_sha256'] and len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M))==warnings==row['actual_warning_headers']
 assert row['original_actual_times']=={k:a[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}
 assert [a[k] for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
 for k in ['original_actual_runner','actual_source65_installed29_context']:
  q=d['original_closed_byte_aliases'][a[k]['file']];assert q['sha256']==a[k]['sha256'];add(q)
 for k in ['actual_installed29_selection','actual_frozen29_original_audit']:add(a[k])
 assert all(sha(ROOT/n)==h for n,h in a['installed29_owner_sha256'].items())
assert d['new_authentic_native_history'][-1]['source']['sha256']==sha(source)
for rows,expected in [(d['strict30_strengthening_public_declarations'],names[23:30]),(d['new_PSD12_public_declarations'],names[30:])]:
 assert [r['name'] for r in rows if r['kind'] in ['theorem','lemma']]==expected
inv=json.loads(add(d['current_inventory']).read_bytes());owner=json.loads(add(d['immutable_original_owner29']).read_bytes())
assert path(d['current_inventory']).read_bytes()==(ROOT/'book/coverage/inventory.json').read_bytes()
assert path(d['immutable_original_owner29']).read_bytes()==(ROOT/'book/coverage/modules.json').read_bytes()
assert d['entire_current_exercise']==next(r for r in inv['exercises'] if r['key']=='verification.html::exercise-19')
assert d['entire_original_owned_exercise_row']==next(r for r in owner['exercises'] if r['inventory_key']=='verification.html::exercise-19')
for u in d['entire_current_material_literals']:assert u==next(r for r in inv['material_source_units'] if r['key']==u['key'])
keys={u['key'] for u in d['entire_current_material_literals']}
assert d['entire_original_material_rows']==[r for r in owner['material_claims'] if any(k in keys for k in r['source_unit_keys'])]
for k in ['entire_used_scenario_section_context','entire_exercise_context']:
 c=d[k];page=add(c['original_page']);assert page.read_bytes()==(ROOT/'SafeLearning/verification.html').read_bytes()
 assert c['keepends_exact_full_html']==''.join(page.read_text().splitlines(keepends=True)[c['start_line_inclusive']-1:c['end_line_exclusive']-1])
for row in d['entire_physical_new_used_primary_API_sources']:add(row['entire_physical_API_source'])
base=ROOT/'verification/lean/.lake/packages/mathlib/Mathlib'
extra=[]
for p in [base/'Analysis/Matrix/Order.lean']:
 q=EXTRA/sha(p)/p.name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());extra.append({'original_historical_path':str(p),'entire_physical_source':ref(q)});add(ref(q))
paper=d['primary_paper_bounded_read'];receipt=json.loads(add(paper['actual_HTTP200_receipt']).read_bytes());add(paper['actual_measured_retrieval_native'])
originalpdf=Path(paper['original_PDF_TMP_path_historical_metadata']);render=Path(paper['actual_original_render_TMP_path_historical_metadata'])
assert originalpdf.is_file() and sha(originalpdf)==paper['original_PDF_SHA256']=='bdc2e2f36fd0f7ba3644afaaa45b2211a87d9d87a4c12e39adfe5d85725536c6' and originalpdf.stat().st_size==paper['original_PDF_bytes']==336103
assert render.is_file() and paper['actual_visual_read_page']==5 and paper['full_original_stays_TMP_offline'] is True
visual={'URL':paper['url'],'genuine_HTTP200_receipt':paper['actual_HTTP200_receipt'],'full_original_PDF_SHA256':sha(originalpdf),'full_original_PDF_stays_TMP_offline':True,'actual_render_page5_SHA256':sha(render),'visual_equation4_checked':'Both block signs are PSD >=0; variables Y are positive definite. Top principal is [Y,W transpose;W,Y] with W=AY+BL. Grouped lower cost block is [I,0;0,R^-1], and cost off-diagonal transpose has Qhalf*Y and L. For the symmetric Q square root and symmetric noise square root convention, the source grouped block is entrywise the paper equation in state dimension4/control dimension1. The noise slack block is [Z,Sigma_w^1/2;Sigma_w^1/2,Y]. Source certificate includes r>0 as the scalar positive R domain. It proves certificate infeasibility only, not objective optimizer or a scenario theorem.'}
author=Path('/tmp/modules-matrix42-paper-PSD-eq4-supplement30-preparation-actual-v2.json');a=json.loads(author.read_bytes())
assert a['status']=='passed' and type(a['actual_exit_code']) is int and a['actual_exit_code']==0 and a['protection_errors']==[]
assert a['helper_sha256_before']==a['helper_sha256_after'] and sha(a['raw_log'])==a['raw_log_sha256']
for p in [author,Path(a['raw_log']),Path(a['actual_command'][1]),Path('/tmp/run-modules-matrix42-paper-PSD-eq4-supplement30-preparation-v2.py')]:add(ref(p))
for k in ['source_ordinal_reserved','source_applied','whole_promotion_performed','canonical_pairs_executed','whole_current_exercise_requested','coverage_complete']:assert d[k] is False
assert d['whole_current_exercise_expected_pending'] is True
# The weaker closed-disk trace obstruction uses the same strict OPEN numerical margin.
L=Fraction(64,3);assert 11-(5+Fraction(2,64)*L)==Fraction(16,3)>4
specs=[(23,30,'Seven actual strict-certificate strengthening bridges','All seven appended full proof bodies and three certificate definitions read. Genuine Y positive definite supplies the actual nonsingular inverse and recovered K=L Y^-1. Full13x13 positive definite block has a true positive definite8x8 principal block. The actual Schur complement theorem plus invertibility derives strict positive drop Y-CYC transpose, which applies the original complex-energy proof to C transpose; exact characteristic-polynomial transpose identity gives actual Schur roots of C. One common Y/L certificate across five models would therefore give one common gain, contradicting the derived open trace obstruction. The affine Gaussian positive open witness gives positive outer measure of failure. This PD version is a strict strengthening; the printed paper has PSD block signs and is not identified with this stronger premise.'),(30,42,'Twelve actual paper semidefinite-certificate association bridges','All twelve appended full proof bodies and both new definitions read. Real PSD energy is the sum of its two nonnegative real/imaginary energies. Genuine positive Y energy plus PSD drop implies every true complex eigenvalue has norm <=1; no strict norm conclusion is claimed. The actual charpoly trace sum then has absolute value <=4, so the same nonempty OPEN five-model margin rules out even a common closed-unit-disk gain. The full printed PSD certificate gives a genuine PSD principal block; the actual Y-positive Schur equivalence derives Y-CYC transpose PSD. Transpose-root invariance gives the true recovered K closed-unit-disk conclusion, and the five-model contradiction proves actual equation4 certificate infeasibility. The explicit nondegenerate affine Gaussian five-sample law assigns positive mass to the measurable OPEN witness; the broader existential failure event is used only via outer-measure monotonicity. No GP derivative posterior, specific pair, optimizer attainment, or general scenario theorem is inferred.')]
groups=[{'scope':label,'public_theorem_names':names[lo:hi],'approved_in_exact_scope':True,'missing_clauses':[],'mathematical_reason':reason} for lo,hi,label,reason in specs]
assert len({n for g in groups for n in g['public_theorem_names']})==19 and sorted(n for g in groups for n in g['public_theorem_names'])==sorted(names[23:])
f={'status':'passed_independent_matrix42_exact_prefix_printed_PSD_equation4_full_association_component_review','reviewer':'/root/foundations_recovery28','review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQUEST),'source':ref(source),'public_theorem_count':42,'public_declaration_count':61,'public_theorem_names':names,'other_public_declarations':other,'original23_full_semantic_peer_exact_body_time':ref(prior),'entire_original23_and_strict30_byte_prefixes_retained':True,'all19_entire_new_bodies_and_five_new_definitions_read':True,'all42_complete_source_bodies_full_current_literals_and_original_rows_read':True,'used_full_principal_submatrix_Schur_invertibility_PSD_PD_energy_trace_and_transpose_primary_chains_read':True,'component_decisions':groups,'printed_paper_actual_PSD_sign_visual_correspondence':visual,'primary_physical_sources':d['entire_physical_new_used_primary_API_sources'],'additional_used_primary_physical_sources':extra,'genuine_new_native_history':d['new_authentic_native_history'],'genuine_new_native_codes':[1,0,0],'genuine_new_warning_headers':[16,16,19],'original_six_native_histories_and_original23_verdict_times_retained_by_exact_refs':True,'original_genuine_author1_schema_failure':d['genuine_original_author_preparation1_failure'],'original_genuine_author2_native':ref(author),'all_original_sources_snapshots_logs_failures_and_native_body_times_preserved':True,'whole_current_Exercise19_or_any_material_literal_approved':False,'whole_remaining_associations':d['remaining_whole_associations'],'matrix_pair_or_GP_conditional_posterior_or_general_scenario_theorem_approved':False,'actual_printed_PSD_certificate_association_approved_in_explicit_four_state_one_control_scope':True,'paper_full_factual_attribution_or_general_design_theorem_approved':False,'full_failure_event_measurability_newly_derived':False,'positive_measurable_open_failure_witness_explicit':True,'semantic_decisions_from_full_math_read_not_integrity':True,'compiler_or_parser_launched_by_reviewer':False,'canonical_or_source_or_owner_or_publication_mutation':False,'source_ordinal_reserved':False,'source_applied':False,'coverage_complete':False,'prospective_postfreeze_evidence_not_part_of_frozen29':True,'required_evidence_artifacts_sha256':closed,'original_closed_byte_aliases':d['original_closed_byte_aliases'],'errors':[]}
OUT.write_text(json.dumps(f,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'findings':ref(OUT),'new_components':19,'groups':2,'whole_decision':False,'errors':[]}))

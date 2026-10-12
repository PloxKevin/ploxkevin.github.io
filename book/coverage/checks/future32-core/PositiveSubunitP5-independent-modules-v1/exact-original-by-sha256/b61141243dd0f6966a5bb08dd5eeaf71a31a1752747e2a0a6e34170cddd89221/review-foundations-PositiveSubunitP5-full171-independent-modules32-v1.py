from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
Q=R/'book/coverage/checks/future32-foundations/positive-subunit-pnorm5-full-scope-v1/foundations-positive-subunit-pnorm5-entire-source-current171-components-prospective171-whole-independent-review-request32-v1.json'
QH='299db96c3057620a3284dedcc7d14d719d63095d2dbeaba0528f69eca1cc6b11'
C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json')
CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c'
F=Path('/tmp/foundations-PositiveSubunitP5-independent-modules32-findings-v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix()if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=path(r['file']);assert p.is_file()and sha(p)==r['sha256'],r
 if 'bytes'in r:assert p.stat().st_size==r['bytes']
 return p
assert sha(C)==CH and sha(Q)==QH and not F.exists()
ctx=json.loads(C.read_bytes());g={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
def guard():
 assert sha(C)==CH
 for n,h in g.items():assert sha(path(n))==h,n
guard();q=json.loads(Q.read_bytes());assert q['errors']==[]
refs={str(Q):QH}
def walk(x):
 if isinstance(x,dict):
  if isinstance(x.get('file'),str)and isinstance(x.get('sha256'),str)and len(x['sha256'])==64:
   p=checked(x);refs[str(p)]=sha(p)
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(q)
for n,h in q['required_evidence_artifacts_sha256'].items():assert sha(path(n))==h;refs[n]=h
source=checked(q['final_genuine_passed_source']).read_text();sys.path.insert(0,str(R/'book/coverage'));import lean_names
names=lean_names.declarations(source);assert names==q['all_public_declarations']and len(names)==6
th=[d['name']for d in names if d['kind']in ['theorem','lemma']];assert len(th)==5 and th==q['public_theorem_names']and len([x for x in names if x['kind']=='def'])==1
assert not re.search(r'\b(?:sorry|axiom|unsafe|admit|native_decide)\b',lean_names.without_comments(source))
body=[]
for m in re.finditer(r'^theorem (\w+)',source,re.M):
 tail=source[m.start():];stop=re.search(r'(?m)^(?:theorem|private theorem|def|end |section |namespace )',tail[1:]);b=tail[:stop.start()+1]if stop else tail
 body.append({'declaration':'SafeLearning.CompleteFoundationsPositiveSubunitPNorm32.'+m.group(1),'complete_body_sha256':hashlib.sha256(b.encode()).hexdigest(),'exact_signature':b.split(':=',1)[0].strip()})
assert body==q['all5_complete_body_signatures']
inv=json.loads(checked(q['current_inventory81']).read_bytes());literal=q['entire_current_literal'];assert literal==next(r for r in inv['material_source_units']if r['key']=='primer-linalg.html::node-171')
page=checked(q['full_current_Source81_linalg']).read_bytes();assert page==(R/'SafeLearning/primer-linalg.html').read_bytes()
assert q['full_current_norm_context_lines155_190']==''.join(page.decode().splitlines(keepends=True)[154:190])
owner=json.loads(checked(q['immutable_actual_installed_owner31']).read_bytes());row=q['actual_installed_owner31_pending_row'];assert row in owner['material_claims']and row['status']=='pending'and row['source_text']==literal['source_text']
prospective=q['exact_planned_prospective_domain_qualified_literal'];rep=q['exact_planned_unnumbered_replacement']
assert rep=={'before':'For $p\\lt1$ the formula is not a norm:','after':'In dimensions $n\\ge2$, for $0\\lt p\\lt1$ the formula is not a norm:'}
assert prospective['key']==literal['key']and prospective['source_text']==literal['source_text'].replace(rep['before'],rep['after'])
pp=checked(q['prospective_full_Source81_page']).read_bytes();assert pp==page.replace(rep['before'].encode(),rep['after'].encode())and prospective['source_sha256']==hashlib.sha256(pp).hexdigest()
assert hashlib.sha256(prospective['source_text'].encode()).hexdigest()==prospective['text_sha256']
for p in q['full_actual_used_Mathlib_primary_source_copies'].values():checked(p).read_text()
history=q['all_genuine_native_histories'];assert [r['actual_exit_code']for r in history]==[1,1,0,0]and [r['actual_emitted_location_first_warning_headers']for r in history]==[1,6,9,9]
for row in history:
 n=json.loads(checked(row['native']).read_bytes());src=checked(row['source']);snap=checked(row['source_snapshot']);log=checked(row['raw_log'])
 assert n['actual_exit_code']==n['actual_runner_exit_code']==row['actual_exit_code']and n['protection_errors']==[]and n['source_unchanged']is True and src.read_bytes()==snap.read_bytes()
 assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(src)and n['raw_log_sha256']==sha(log)
 assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')and {k:n[k]for k in row['original_body_times']}==row['original_body_times']
 assert len(re.findall(r'^.*:\d+:\d+: warning:',log.read_text(),re.M))==row['actual_emitted_location_first_warning_headers']
 assert n['actual_source81_installed_owner31_context']['sha256']==CH and n['original_actual_runner']['sha256']=='6ad85eb3259a45620f552dcafdb9dd5c85b7b99a1e0a49b10b4392e78316b659'
assert checked(history[2]['source']).read_text()==source
axsource=checked(history[-1]['source']).read_text();assert axsource.startswith(source)and axsource[len(source):].count('#print axioms')==5
printed={name:[a.strip()for a in atoms.replace('\n',' ').split(',')if a.strip()]for name,atoms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",checked(history[-1]['raw_log']).read_text(),re.S)}
assert list(printed)==th and printed==q['actual_standard_axioms_per_public_theorem']and all(set(a)<={'propext','Classical.choice','Quot.sound'}for a in printed.values())
def headers(s):return re.findall(r'(?ms)^theorem\s+\w+.*?(?=\s*:=)',s)
assert all(headers(checked(r['source']).read_text())==headers(source)for r in history[:3])and q['all_five_exact_statement_headers_retained_after_two_observed_local_repairs']is True
facts=json.loads(checked(q['bounded_two_remote_primary_norm_facts_with_actual_HTTP200_text0_receipts']).read_bytes());assert facts['errors']==[] and len(facts['sources'])==2
remote_observations=[]
for r in facts['sources']:
 assert r['actual_http_status']==200 and r['actual_content_type']=='application/pdf'and r['actual_pdftotext']['actual_returncode']==0
 pdf=checked(r['actual_pdf']);txt=checked(r['actual_complete_text']);raw=checked(r['actual_pdftotext']['raw_log'])
 assert pdf.is_relative_to('/tmp')and txt.is_relative_to('/tmp')and raw.is_relative_to('/tmp')and r['actual_final_url']==r['requested_url']
 assert r['actual_pdftotext']['command']==['pdftotext','-layout',str(pdf),str(txt)]
 remote_observations.append({'actual_url':r['actual_final_url'],'actual_HTTP_status':200,'actual_pdftotext_returncode':0,'PDF_sha256':sha(pdf),'PDF_bytes':pdf.stat().st_size,'complete_text_sha256':sha(txt),'complete_text_bytes':txt.stat().st_size,'original_HTTP_and_text_execution_times_retained_in_bounded_receipt':True,'full_PDF_and_text_stay_TMP_offline_not_copied_into_this_peer':True})
berk=checked(facts['sources'][0]['actual_complete_text']).read_text();hert=checked(facts['sources'][1]['actual_complete_text']).read_text()
assert 'with respect to the 1-norm' in berk and 'kf (x, u) − µn (x, u)k1' in berk
assert 'The euclidean norm with respect to a positive' in hert and 'kdk∞ ≤ η' in hert and 'λkdk∞' in hert
module=checked(q['full_current_Module11_norm_convention_source']).read_text()
assert q['full_current_Module11_Berkenkamp_context']in module and q['full_current_Module11_robustMPC_norm_context']in module
assert 'refer to the 1-norm' in q['full_current_Module11_Berkenkamp_context']and 'Unadorned vector norms here are Euclidean; the disturbance norm' in q['full_current_Module11_robustMPC_norm_context']
assert q['citation_domain_notes']==facts['bounded_factual_assessments']
assert q['citation_domain_notes']['Hertneck2018']['state_unadorned_Euclidean_reading_is_an_explicit_local_convention_and_consistent_inference']is True
side=Q.parent/'foundations-positive-subunit-pnorm5-full-narrow-primary-original-genuine-author-native-closures32-v1.json';sd=json.loads(side.read_bytes());walk(sd);refs[str(side)]=sha(side)
assert len(sd['three_actual_original_genuine_author_preparations'])==3
for row in sd['three_actual_original_genuine_author_preparations']:
 an=json.loads(checked(row['native']).read_bytes());assert an['actual_exit_code']==row['original_actual_exit_code']==0 and an['protection_errors']==[]
 assert an['started_at_utc']==row['original_started_at_utc']and an['finished_at_utc']==row['original_finished_at_utc']and an['elapsed_seconds']==row['original_elapsed_seconds']
 assert sha(checked(row['raw_log']))==an['log_sha256']
guard()
f={'status':'passed_independent_PositiveSubunitPNorm5_current171_components_and_prospective171_whole_full_mathematical_review','errors':[],'full_source_read':True,'all5_public_complete_bodies_and_power_quasinorm_definition_read':True,'all_used_complete_primary_rpow_exponent_order_composition_finite_sum_and_coordinate_single_proof_bodies_read':True,'original_request':ref(Q),'actual_source':q['final_genuine_passed_source'],'public_theorem_names':th,'public_theorem_count':5,'public_name_count':6,'definition_count':1,'all5_complete_body_signatures':body,'entire_current_literal':literal,'entire_prospective_literal':prospective,'whole_unit_decisions':{'primer-linalg.html::node-171':{'entire_current_literal_preceding_norm_definition_and_Module11_context_read':True,'current_whole_semantic_approved':False,'current_missing_requirements':['The universal non-norm assertion must be restricted to positive exponents 0<p<1 and at least two coordinates; for every positive exponent the one-dimensional formula equals the genuine absolute-value norm, while p=0 is outside the usual formula domain.'],'entire_prospective_literal_and_full_domain_context_read':True,'prospective_whole_semantic_approved':True,'prospective_missing_requirements':[],'conditional_on_later_exact_one_phrase_application_and_distinct_independent_narrow_parser':True}},'all5_exact_component_scopes_approved':True,'component_missing_requirements':[],'actual_generic_triangle_failure_derived':{'domain':'Every nontrivial finite real coordinate type and every real 0<p<1. Two distinct coordinate units have quasinorm1 each and their sum has quasinorm2^(1/p)>2. Nontrivial Fin n is exactly the n>=2 domain.','desired_failure_or_quasinorm_value_not_assumed':True},'actual_printed_half_exponent_4_versus_1_plus_1_derived':True,'actual_Fin1_every_positive_p_equals_absolute_value_countermodel_derived':True,'norm_and_quasinorm_formula_association_matches_the_preceding_literal_definition':True,'actual_factual_attribution_scope':{'Berkenkamp2017':'Directly verified Section2 Assumptions1-2 use the 1-norm for dynamics/policies and calibrated dynamics errors; Module11 uses the same declared norm.','Hertneck2018':'Directly verified positive-matrix Euclidean quadratic notation and explicit infinity input-disturbance set/bound in equation4 and Assumption2. Unadorned state Euclidean norms are the explicit current Module11 presentation convention and a consistent reading, not a newly proven primary algorithm theorem.','norm_constant_advice':'The final instruction to check the norm associated with each constant is editorial advice supported by these distinct declared conventions; no constants are silently converted between norms.'},'bounded_remote_primary_fact_receipt':q['bounded_two_remote_primary_norm_facts_with_actual_HTTP200_text0_receipts'],'full_remote_primary_used_sections_actually_read_from_pinned_original_TMP_text':True,'remote_receipt_observations_without_full_PDF_or_text_copy':remote_observations,'full_Module11_norm_convention_source':q['full_current_Module11_norm_convention_source'],'original_true_failed1_failed2_passed3_all5_axiom_histories':history,'actual_standard_axioms_per_public_theorem':printed,'three_genuine_original_author_preparations_sidecar':ref(side),'current_owner_pending_row_preserved_unchanged':q['actual_installed_owner31_pending_row'],'no_algorithm_Module11_neighbor_parent_Source_ordinal_owner_canonical_selected_or_publication_promotion':True,'reader_compiler_or_parser_or_current_Source_or_owner_mutation':False,'actual_current_context':ref(C),'protection_errors':[],'coverage_complete':False,'input_and_original_artifacts_sha256':refs}
with F.open('x')as out:json.dump(f,out,indent=2,ensure_ascii=False);out.write('\n')
print(json.dumps({'status':f['status'],'whole_key':'primer-linalg.html::node-171','theorems':5,'current_whole':False,'prospective_whole':True,'errors':[]}))

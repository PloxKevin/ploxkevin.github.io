from pathlib import Path
import contextlib, hashlib, importlib.util, json, re, sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
C=Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json'); CH='0396f659bfeb3d380a53f7ca3ca3be9c77d04f56cfbee1a9be7c711ba188210c'
RUN=Path('/tmp/root_tmp_lean_current81_installed_owner31_runner_v1.py'); RUNH='6ad85eb3259a45620f552dcafdb9dd5c85b7b99a1e0a49b10b4392e78316b659'
Q=Path('/tmp/foundations-common-matrixnorm-positive-dimensions-unnumbered32-v1/foundations-common-inducednorms-positive-dimensions-one-phrase-unnumbered-full29-proposal32-v1.json'); QH='13203e3e9fb32999536666a488fc64cffaec2ba7355646917ac35005dfcb3b57'
B=Path('/tmp/modules-child-norm21-positive-dimensions-independent32-v2'); F=Path('/tmp/modules-child-norm21-positive-dimensions-independent32-findings-v2.json')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(s): return Path(s) if Path(s).is_absolute() else R/s
def ref(p):
 p=Path(p); return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
refs={}
def checked(r):
 p=path(r['file']); assert p.is_file() and sha(p)==r['sha256'],r
 if 'bytes' in r: assert p.stat().st_size==r['bytes'],r
 refs[str(p)]=sha(p); return p
def walk(x):
 if isinstance(x,dict):
  if isinstance(x.get('file'),str) and isinstance(x.get('sha256'),str) and len(x['sha256'])==64: checked(x)
  for v in x.values(): walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
assert sha(C)==CH and sha(RUN)==RUNH
ctx=json.loads(C.read_bytes()); assert ctx['status']=='actual_source81_installed_owner31_selected31_audited_TMP_context_only'
guards={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
def guard():
 assert sha(C)==CH and sha(RUN)==RUNH
 for n,h in guards.items(): assert sha(path(n))==h,n
 return []
guard(); assert sha(Q)==QH and not B.exists() and not F.exists()
d=json.loads(Q.read_bytes());walk(d)
assert d['source_number_reserved'] is False and d['source_applied'] is False and d['prospective_source_number'] is None
old=checked(d['source']).read_bytes(); new=checked(d['proposed_source']).read_bytes()
assert path(d['live_source_original_path']).read_bytes()==old
assert len(d['exact_replacements'])==1
rep=d['exact_replacements'][0]
assert rep['after']==r'For $m,n\ge1$, '+rep['before']
assert old.decode().count(rep['before'])==1 and rep['after'] not in old.decode()
assert old.decode().replace(rep['before'],rep['after'],1).encode()==new
assert new.decode().count(rep['after'])==1 and new.decode().replace(rep['after'],rep['before'],1).encode()==old
assert old.count(b'\n')==new.count(b'\n')
assert ''.join(old.decode().splitlines(keepends=True)[138:350])==d['full_current_p_norm_domain_and_induced_formula_context_lines139_350']
assert ''.join(new.decode().splitlines(keepends=True)[138:350])==d['full_proposed_p_norm_domain_and_induced_formula_context_lines139_350']
sys.path.insert(0,str(R/'book'));sys.path.insert(0,str(R/'book/coverage'));from validate import Document;from lean_names import declarations
assert [(n.tag,n.attrs,n.line) for n in Document(old.decode()).nodes]==[(n.tag,n.attrs,n.line) for n in Document(new.decode()).nodes]
qpath=checked(d['supporting_entire21_source_and_histories_request']);q=json.loads(qpath.read_bytes());walk(q)
for n,h in q['required_evidence_artifacts_sha256'].items(): assert sha(path(n))==h,n;refs[str(path(n))]=h
source=checked(q['final_genuine_passed_source']).read_text()
assert declarations(source)==q['all_public_declarations']
assert q['public_theorem_count']==21 and q['public_name_count']==25 and q['definition_count']==4 and q['private_proof_count']==6
assert [v['name'] for v in declarations(source) if v['kind']=='theorem']==q['public_theorem_names']
# The scope-changing prefix is matched against the actual finite maximum signatures and bodies.
sigs={v['declaration'].rsplit('.',1)[-1]:v['exact_signature'] for v in q['all21_complete_body_signatures']}
dimension_theorems={
 'actual_one_to_p_induced_norm_is_the_largest_actual_column_norm':['[Nonempty n]'],
 'actual_all_conjugate_p_to_infinity_induced_norm_is_the_largest_row_q_norm':['[Nonempty m]'],
 'actual_one_induced_norm_is_the_largest_absolute_column_sum':['[Nonempty n]'],
 'actual_infinity_induced_norm_is_the_largest_absolute_row_sum':['[Nonempty m]'],
 'actual_spectral_induced_norm_is_the_square_root_of_the_largest_Gram_eigenvalue':['[Nonempty n]'],
 'actual_one_to_infinity_induced_norm_is_the_largest_absolute_entry':['[Nonempty m]','[Nonempty n]'],
 'actual_two_to_infinity_induced_norm_is_the_largest_Euclidean_row_length':['[Nonempty m]'],
 'actual_spectral_induced_norm_is_the_first_actual_singular_value':['[Nonempty n]'],
 'actual_spectral_induced_norm_is_the_greatest_actual_singular_value':['[Nonempty n]']}
for name,hypotheses in dimension_theorems.items():
 assert sigs[name] in source
 for h in hypotheses: assert h in sigs[name]
assert 'def columnMaximum [Nonempty n]' in source and 'def rowMaximum [Nonempty m]' in source
assert 'def entryMaximum [Nonempty m] [Nonempty n]' in source
assert 'Finset.exists_mem_eq_sup\' Finset.univ_nonempty' in source
assert '[ENNReal.HolderConjugate p q] [Fact (1 ≤ p)] [Fact (1 ≤ q)]' in source
assert 'actual_all_conjugate_unit_attainer p q (A i)' in source
# Read supporting matrix/operator and finite-p endpoint domain bodies by exact bytes.
selected={k:checked(v) for k,v in d['full_three_selected_sources'].items()}
induced=selected['CompleteFoundationsInducedNormProductCertificates30.lean'].read_text()
holder=selected['CompleteFoundationsHolderDualNormWholeUnits30.lean'].read_text()
rayleigh=selected['CompleteFoundationsRayleighQuotientWhole30.lean'].read_text()
assert 'theorem actual_matrix_induced_norm_maxima_and_least_constant [Nonempty n]' in induced
assert 'variable [FiniteDimensional ℝ E] [Nontrivial E]' in induced
assert 'variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]' in rayleigh
assert "Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues" in rayleigh
assert 'cases isEmpty_or_nonempty I with' in holder and 'sourcePNorm p x ≤ 1' in holder
fold=R/'verification/lean/.lake/packages/mathlib/Mathlib/Data/Finset/Lattice/Fold.lean';ft=fold.read_text();refs[str(fold)]=sha(fold)
assert "def sup' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=" in ft
assert "theorem exists_mem_eq_sup' (f : ι → α) : ∃ i, i ∈ s ∧ s.sup' H f = f i := by" in ft
sv=checked(q['full_actual_used_Mathlib_primary_source_copies']['Analysis/InnerProductSpace/SingularValues.lean']).read_text()
assert 'theorem singularValues_of_lt' in sv and 'hi : i < n' in sv and 'theorem singularValues_of_finrank_le' in sv
hist=q['all_genuine_native_histories'];assert [h['actual_exit_code'] for h in hist[:7]]==[1,0,1,1,0,1,0]
assert [h['history_role'] for h in hist]==['source_trial_'+str(i) for i in range(1,8)]+['all19_axiom_inspection','all21_axiom_inspection']
for h in hist:
 native=json.loads(checked(h['native']).read_bytes());log=checked(h['raw_log']).read_text();snapshot=checked(h['source_snapshot'])
 assert snapshot.read_bytes()==checked(h['source']).read_bytes()
 assert native['actual_exit_code']==h['actual_exit_code'] and native['actual_runner_exit_code']==h['actual_exit_code']
 assert native['actual_command']==['lake','env','lean',native['source']] and native['actual_workdir']==str(R/'verification/lean')
 assert native['source_sha256_before']==native['source_sha256_after']==native['source_snapshot_sha256']==sha(snapshot)
 assert native['raw_log_sha256']==sha(checked(h['raw_log'])) and native['source_unchanged'] is True and native['protection_errors']==[]
 assert all(native[k]==v for k,v in h['original_body_times'].items())
 assert len(re.findall(r'^.*\.lean:\d+:\d+: warning:',log,re.M))==h['actual_emitted_location_first_warning_headers']
 assert native['original_actual_runner']['sha256']==RUNH and native['actual_source81_installed_owner31_context']['sha256']==CH
 if 'axiom' in h['history_role']:
  axioms={n:re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',a) for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)}
  assert len(axioms)==(19 if h['history_role'].startswith('all19') else 21)
  assert all(a==['propext','Classical.choice','Quot.sound'] for a in axioms.values())
  if h['history_role'].startswith('all21'):assert axioms==q['actual_standard_axioms_per_public_theorem']
AN=Path('/tmp/foundations-common-matrixnorm-positive-dimensions-full29-author-preparation32-actual-v1.json');an=json.loads(AN.read_bytes())
AH=Path('/tmp/prepare-foundations-common-matrixnorm-dimensions-full29-unnumbered32-v1.py');AW=Path('/tmp/run-prepare-foundations-common-matrixnorm-dimensions-full29-unnumbered32-v1.py')
assert an['status']=='passed' and an['actual_exit_code']==0 and an['protection_errors']==[]
assert an['actual_command']==['python3',str(AH)] and an['actual_workdir']==str(R)
assert an['helper_sha256_before']==an['helper_sha256_after']
for p in [AH,AW,C]:assert an['helper_sha256_before'][str(p)]==sha(p)
assert sha(path(an['log']))==an['log_sha256']
for p in [AN,AH,AW,path(an['log']),C,RUN,Q]:refs[str(p)]=sha(p)
# Own fresh parser: only 29 current HTML files copied; both mutable parser globals kept inside TMP.
B.mkdir();I=B/'isolated-independent-full29-parser';(I/'SafeLearning').mkdir(parents=True)
base=json.loads(checked(d['before_inventory']).read_bytes())
for p in sorted((R/'SafeLearning').glob('*.html')):
 assert sha(p)==base['source_sha256'][p.relative_to(R).as_posix()]
 (I/'SafeLearning'/p.name).write_bytes(new if p.name=='primer-linalg.html' else p.read_bytes())
assert len(list((I/'SafeLearning').glob('*.html')))==29
spec=importlib.util.spec_from_file_location('independent_child_norm21_positive_dimensions32',checked(d['parser']));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
m.ROOT=I;m.OUT=I/'book/coverage';assert m.ROOT.resolve().is_relative_to(B) and m.OUT.resolve().is_relative_to(B)
L=B/'actual-independent-full29-parser-stdout.log'
with L.open('x') as f,contextlib.redirect_stdout(f):m.inventory()
P=m.OUT/'inventory.json';parsed=json.loads(P.read_bytes())
assert parsed['counts']==base['counts']==d['parser_counts'] and parsed['counts']['exercises']==556 and parsed['counts']['material_source_units']==12774
assert parsed['source_sha256']=={**base['source_sha256'],'SafeLearning/primer-linalg.html':hashlib.sha256(new).hexdigest()}
changes={};literals={}
for field in ['exercises','material_source_units']:
 a={v['key']:v for v in base[field]};b={v['key']:v for v in parsed[field]};assert a.keys()==b.keys();changes[field]=[]
 for key in a:
  x=dict(a[key]);y=dict(b[key])
  if x['source']=='SafeLearning/primer-linalg.html':x.pop('source_sha256');y.pop('source_sha256')
  if x!=y:
   assert {k:v for k,v in x.items() if k not in ['source_text','text_sha256']}=={k:v for k,v in y.items() if k not in ['source_text','text_sha256']}
   changes[field].append(key);literals[key]={'entire_current':a[key],'entire_proposed':b[key]}
expected={'exercises':[],'material_source_units':['primer-linalg.html::node-305','primer-linalg.html::node-307']}
assert changes==expected==d['fresh_changed_literal_keys'] and literals==d['entire_current_and_proposed_literal_records']
fixture={'current':next(v for v in base['material_source_units'] if v['key']=='primer-linalg.html::node-311'),'prospective':next(v for v in parsed['material_source_units'] if v['key']=='primer-linalg.html::node-311')}
assert fixture==d['entire_unchanged_current_and_prospective311_proof_fixture']
assert fixture['current']['source_text']==fixture['prospective']['source_text'] and fixture['current']['text_sha256']==fixture['prospective']['text_sha256']
author_parsed=json.loads(checked(d['proposed_full29_inventory']).read_bytes())
assert {k:v for k,v in parsed.items() if k!='generated_at_utc'}=={k:v for k,v in author_parsed.items() if k!='generated_at_utc'}
assert isinstance(parsed['generated_at_utc'],str) and isinstance(author_parsed['generated_at_utc'],str)
guard();refs[str(P)]=sha(P);refs[str(L)]=sha(L)
for original in ['/tmp/review-foundations-norm21-positive-dimensions-independent-modules-child32-v1.py','/tmp/run-foundations-norm21-positive-dimensions-independent-modules-child32-v1.py','/tmp/modules-child-norm21-positive-dimensions-independent32-actual-v1.json','/tmp/modules-child-norm21-positive-dimensions-independent32-actual-v1.log']:refs[original]=sha(original)
out={'status':'passed_independent_common_norm21_one_positive_dimension_phrase_entire_literal_fresh_BOTH_ROOT_OUT_TMP_parser_review','errors':[],
 'narrow_one_positive_dimension_phrase_semantically_approved':True,'full_current_and_proposed305307_literals_and139350_context_read':True,
 'full_supporting21_source_statements_and_complete_bodies_read_for_narrow_domain_review':True,
 'supporting_selected_Holder_entire_source_and_Induced_Rayleigh_relevant_domain_proof_bodies_read':True,
 'exact_forward_and_byte_inverse_substitution_approved':True,
 'dimension_conventions_reviewed':{'common_simultaneous_table':'m,n>=1','column_maximum':'nonempty n','row_maximum':'nonempty m','entry_maximum':'nonempty m and nonempty n','Gram_eigenvalue_maximum_and_first_actual_singular_value_correspondence':'nonempty n','induced_nonzero_input_and_unit_sphere_convention':'nonempty n','unrestricted_empty_index_maximum_or_m0_worst_row_approved':False},
 'all_conjugate_p_q_and_infinity_endpoints_preserved_by_existing_source_domain':True,
 'zero_matrix_sign0_ball_attainer_does_not_claim_unit_sphere_norm1':True,
 'independent_parser':{'both_ROOT_and_OUT_TMP':True,'full29_source_pages':29,'exercise_count':556,'material_source_unit_count':12774,'changed_literal_keys':changes,'all_other28_source_pages_and_all_other_literal_fields_preserved':True,'tags_attributes_lines_exact':True,'exact_inventory':ref(P),'raw_stdout':ref(L),'comparison_excludes_only':'generated_at_utc','own_generated_at_utc':parsed['generated_at_utc'],'author_generated_at_utc':author_parsed['generated_at_utc']},
 'entire_current_and_proposed_literal_records':literals,'entire_unchanged_current_and_prospective311_proof_fixture':fixture,
 'original_proposal':ref(Q),'original_completed_author_native':ref(AN),'original_author_helper':ref(AH),'original_author_wrapper':ref(AW),'original_author_raw_log':ref(path(an['log'])),
 'original_completed_author_exit_code':an['actual_exit_code'],'original_completed_author_elapsed_seconds':an['elapsed_seconds'],
 'supporting_entire21_source_and_histories_request':ref(qpath),'original_all_genuine_source_and_axiom_histories_preserved_exactly':hist,
 'actual_standard_axioms_per_public_theorem_retained_exactly':q['actual_standard_axioms_per_public_theorem'],
 'actual_Finset_nonempty_supremum_and_attainment_primary_provider':ref(fold),'actual_Finset_relevant_domain_and_body_locations_read':['Fold.lean:511-579','Fold.lean:742-775'],
 'supporting_positive_domain_theorem_signature_requirements':dimension_theorems,
 'current_or_prospective_whole305307311_approved_by_this_narrow_peer':False,'current311_unqualified_domain_whole_approved':False,
 'whole21_mathematical_correspondence_left_to_separate_independent_full_review':True,
 'source_ordinal_reserved_or_applied':False,'compiler_canonical_owner_selection_publication_mutated':False,
 'actual_current_context':ref(C),'actual_current_runner':ref(RUN),'protection_errors':[],'coverage_complete':False,
 'original_independent_reader1_true_failure_preserved':{'native':ref(Path('/tmp/modules-child-norm21-positive-dimensions-independent32-actual-v1.json')),'diagnosis':'Reader1 stopped before supporting source or fresh parser checks because lean_names lives under book/coverage, not book. Reader2 adds that correct import path; all original bytes and true0.558137277s failure retained.'},
 'input_and_original_artifacts_sha256':refs}
with F.open('x') as f:json.dump(out,f,indent=2,ensure_ascii=False);f.write('\n')
print(json.dumps({'status':out['status'],'changed':changes,'physical_input_count':len(refs),'errors':[]}))

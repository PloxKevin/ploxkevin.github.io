from pathlib import Path
import contextlib,hashlib,importlib.util,json,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=Path('/tmp/modules-integral-tracking-precision-unnumbered31-v1')
assert not B.exists();B.mkdir()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
S=R/'SafeLearning/nn-in-the-loop.html';V=R/'book/coverage/inventory-after-correction79.json';H=R/'book/inventory_claims.py'
OWN=R/'book/coverage/checks/modules-future30/current79-three-fragments-final-v1/modules30-current79-real30-three-fragments-candidate-v1.json'
assert sha(S)=='8363ca99bfd85ec75fcda4f76917a0c4b7ac437b2b430c5f722fa4310ba90b2c'
assert sha(V)=='9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de'
assert sha(OWN)=='6f347b3d512a5ce36222e72e8236eb350f3218ace430c3a9dabd8776a03fbc34'
replacements=[{'before':r'\xi=-0.833','after':r'\xi=-5/6\approx-0.833'},
 {'before':r'spectral radius $0.632$ ($b=1$)','after':r'spectral radius $\sqrt{2/5}\approx0.632$ ($b=1$)'},
 {'before':r'and $0.616$ ($b=1.2$)','after':r'and $\sqrt{19/50}\approx0.616$ ($b=1.2$)'}]
old=S.read_text();new=old
for r in replacements:assert new.count(r['before'])==1 and r['after']not in new;new=new.replace(r['before'],r['after'],1)
inverse=new
for r in reversed(replacements):assert inverse.count(r['after'])==1;inverse=inverse.replace(r['after'],r['before'],1)
assert inverse.encode()==S.read_bytes()and old.count('\n')==new.count('\n')
P=B/'nn-in-the-loop-integral-tracking-precision-proposed-unnumbered.html';P.write_text(new)
current=B/'nn-in-the-loop-current79-immutable-original.html';current.write_bytes(S.read_bytes())
sys.path.insert(0,str(R/'book'));from validate import Document
assert [(n.tag,n.attrs,n.line)for n in Document(old).nodes]==[(n.tag,n.attrs,n.line)for n in Document(new).nodes]
I=B/'isolated-full29-parser';(I/'SafeLearning').mkdir(parents=True)
for p in sorted((R/'SafeLearning').glob('*.html')):(I/'SafeLearning'/p.name).write_bytes(P.read_bytes()if p==S else p.read_bytes())
assert len(list((I/'SafeLearning').glob('*.html')))==29
spec=importlib.util.spec_from_file_location('integral_tracking_precision31_author_both_roots',H);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
m.ROOT=I;m.OUT=I/'book/coverage';assert m.ROOT.resolve().is_relative_to(B)and m.OUT.resolve().is_relative_to(B)
raw=B/'actual-author-full29-parser-stdout.log'
with raw.open('x')as f,contextlib.redirect_stdout(f):m.inventory()
parsed=json.loads((m.OUT/'inventory.json').read_bytes());inv=json.loads(V.read_bytes())
assert parsed['counts']==inv['counts'];assert parsed['source_sha256']=={**inv['source_sha256'],'SafeLearning/nn-in-the-loop.html':sha(P)}
changes={};literals={}
for field in ['exercises','material_source_units']:
 a={r['key']:r for r in inv[field]};b={r['key']:r for r in parsed[field]};assert a.keys()==b.keys();changes[field]=[]
 for k in a:
  x=dict(a[k]);y=dict(b[k])
  if x['source']=='SafeLearning/nn-in-the-loop.html':x.pop('source_sha256');y.pop('source_sha256')
  if x!=y:
   assert {n:v for n,v in x.items()if n not in ['source_text','text_sha256']}=={n:v for n,v in y.items()if n not in ['source_text','text_sha256']}
   changes[field].append(k);literals[k]={'entire_current':a[k],'entire_proposed':b[k]}
assert changes=={'exercises':['nn-in-the-loop.html::exercise-19'],'material_source_units':['nn-in-the-loop.html::node-1247']}
owner=json.loads(OWN.read_bytes());exercise=next(r for r in owner['exercises']if r['inventory_key']=='nn-in-the-loop.html::exercise-19');assert exercise['status']=='pending'
rows=[r for r in owner['material_claims']if 'nn-in-the-loop.html::node-1247'in r.get('source_unit_keys',[])]
proof=Path('/tmp/CompleteModulesIntegralTrackingWhole30-draft-v15.lean');native=Path('/tmp/modules-integral-tracking-whole31-owner30-trial12.json');n=json.loads(native.read_bytes())
assert n['actual_exit_code']==0 and n['protection_errors']==[]and n['source_sha256_before']==n['source_sha256_after']==sha(proof)
d={'status':'prepared_TMP_only_unnumbered_integral_tracking_three_exact_precision_phrases_author_actual_full29_parser_passed','prospective_source_number':None,'source_number_reserved':False,'source_applied':False,'source':ref(current),'live_source_original_path':'SafeLearning/nn-in-the-loop.html','before_inventory':ref(V),'before_corrections':ref(R/'book/coverage/material-corrections.json'),'parser':ref(H),'validator':ref(R/'book/validate.py'),'proposed_source':ref(P),'exact_replacements':replacements,'both_parser_ROOT_and_OUT_isolated':True,'fresh_changed_literal_keys':changes,'entire_current_and_proposed_literal_records':literals,'full_current_context_lines1008_1030':''.join(old.splitlines(keepends=True)[1007:1030]),'full_proposed_context_lines1008_1030':''.join(new.splitlines(keepends=True)[1007:1030]),'exact_current_owned_exercise_body':exercise,'exact_current_owned_changed_material_rows':rows,'original_installed_owner30_candidate':ref(OWN),'proposed_full29_inventory':ref(m.OUT/'inventory.json'),'actual_parser_stdout':ref(raw),'parser_counts':parsed['counts'],'all_other28_pages_and_all_other_literal_records_exact':True,'full_nodes_tags_attrs_lines_preserved':True,'exact_inverse_returns_entire_current79_page_bytes':True,'actual_supporting_full35_source':ref(proof),'actual_supporting_passed_trial12':ref(native),'actual_supporting_snapshot':ref(n['source_snapshot']),'actual_supporting_raw_log':ref(n['raw_log']),'exact_support_names':['actual_linearised_scalar_offset_and_integrator_state_exact_values_and_rounding','actual_nonlinear_augmented_loop_has_the_printed_Frechet_linearization','actual_linearization_matrix_represents_the_true_derivative_action','actual_nominal_linearization_has_exact_conjugate_eigenvalues','actual_perturbed_linearization_has_exact_conjugate_eigenvalues','actual_both_linearized_spectral_radii_are_exact_and_have_the_printed_rounding'],'rationale':['The displayed integrator state is exactly−5/6, not the printed finite decimal−.833. The existing three-decimal approximation is preserved and qualified.','Actual derivative/matrix-action/complex-spectrum proofs give exact attained radii sqrt(2/5) and sqrt(19/50), each strictly within.0005 of its original three-decimal display and below1.','Exactly three phrases change only the answer paragraph1247 and its containing Exercise14.5. Existing equations, parameters, convergence/stability statements and all other source rows are unchanged. Full35/whole-exercise semantics remain a separate review.'],'current_whole_exercise_or_current_node1247_approved':False,'whole_prospective_semantics_pending_separate_full_reader':True,'compiler_canonical_owner_selection_or_publication_mutations':False,'coverage_complete':False}
O=B/'modules-integral-tracking-three-precision-phrases-unnumbered-full29-proposal31-v1.json';O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'proposal':ref(O),'changed':changes,'proposed_source':ref(P)}))

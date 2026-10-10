from pathlib import Path
import datetime,hashlib,importlib.util,json,re,shutil,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
def P(x):return Path(x) if Path(x).is_absolute() else R/x
def H(x):return hashlib.sha256(P(x).read_bytes()).hexdigest()
proposal='/tmp/modules-gp34-positive-dimensions-scope19-proposal.json'
assert H(proposal)=='20c5a35bf04cdef4858735bd5635821e761b6a0900e36941e8d12bc475532e8f'
d=json.loads(P(proposal).read_text());source=d['source'];old=P(source).read_bytes()
assert H(source)==d['source_sha256_before']=='980a30185175bb46598746b8c332c783cfd32aa0a0a8c110cd7266284dff037b'
assert len(d['replacements'])==1
r=d['replacements'][0]
assert old.count(r['before'].encode())==r['count']==1
assert r['after']==r['before'].replace('Let $k',r'Let $d\ge1$ and $T\ge1$ be integers, and let $k',1)
new=old.replace(r['before'].encode(),r['after'].encode(),1)
assert new.replace(r['after'].encode(),r['before'].encode(),1)==old
assert old.count(b'\n')==new.count(b'\n') and hashlib.sha256(new).hexdigest()==d['proposed_source_sha256_after']
assert P(d['source_bytes_before_snapshot']).read_bytes()==old and H(d['source_bytes_before_snapshot'])==d['source_bytes_before_snapshot_sha256']
assert P(d['source_bytes_proposed_after_snapshot']).read_bytes()==new and H(d['source_bytes_proposed_after_snapshot'])==d['source_bytes_proposed_after_snapshot_sha256']
assert H(d['inventory_at_preparation'])==d['inventory_sha256_at_preparation']=='c5edf43ad9e1b2d408b328fd331b2a52c624126dd167100541d5ca931986a963'
I=json.loads(P(d['inventory_at_preparation']).read_text())
assert all(H(p)==h for p,h in I['source_sha256'].items()) and len(I['source_sha256'])==29
review='/tmp/modules-gp34-linear-information-source-components-review19-v3.json'
assert H(review)=='c146113081c2d5521a53afc36c15819cebe1f8b2d5a8a53ae6e3a091dbffdc4d'
v3=json.loads(P(review).read_text())
for p,h in d['actual_proof_source_sha256'].items():assert H(p)==h==v3['proof_source_sha256'][p]
assert len(d['actual_proof_source_sha256'])==8
for e in d['actual_standalone_evidence']:
 assert H(e['compiler_manifest'])==e['compiler_manifest_sha256']
 f=json.loads(P(e['compiler_manifest']).read_text())['files'][0]
 assert f==e['raw_execution_record'] and f['exit_code']==0 and f['source_unchanged']
 assert H(f['file'])==f['sha256'] and H(f['log'])==f['log_sha256']
for p,h in v3['proof_source_sha256'].items():assert H(p)==h
for p,h in v3['actual_imported_dependency_source_sha256'].items():assert H(p)==h

sys.path.insert(0,str(R/'book'));from validate import Document
A,B=Document(old.decode()),Document(new.decode())
assert len(A.nodes)==len(B.nodes) and all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line) for a,b in zip(A.nodes,B.nodes))
old_ex=[n for n in A.root.descendants('details') if n.child('summary') and re.match(r'^(Exercise\b|(Easy|Medium|Hard)\s+\d+\b)',n.child('summary').text().strip(),re.I)]
new_ex=[n for n in B.root.descendants('details') if n.child('summary') and re.match(r'^(Exercise\b|(Easy|Medium|Hard)\s+\d+\b)',n.child('summary').text().strip(),re.I)]
assert len(old_ex)==len(new_ex)==20
assert old_ex[17].text()==v3['exercise']['source_text']
assert new_ex[17].text()==old_ex[17].text().replace(r'Let $k',r'Let $d\ge1$ and $T\ge1$ be integers, and let $k',1)
assert all(A.nodes[n-1].text()==B.nodes[n-1].text() for n in (1217,1218))
sim=Path('/tmp/modules-gp34-positive-domain-independent-proposal19-simulation')
assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
for f in (R/'SafeLearning').glob('*.html'):shutil.copyfile(f,sim/'SafeLearning'/f.name)
assert len(list((sim/'SafeLearning').glob('*.html')))==29
(sim/source).write_bytes(new)
spec=importlib.util.spec_from_file_location('gp34_positive_domain_independent_inventory19',R/'book/inventory_claims.py')
generator=importlib.util.module_from_spec(spec);spec.loader.exec_module(generator)
generator.ROOT=sim;generator.OUT=sim/'book/coverage';generator.inventory()
np=generator.OUT/'inventory.json';N=json.loads(np.read_text());assert I['counts']==N['counts']
delta={};details=[]
for section in ('exercises','material_source_units'):
 a={u['key']:u for u in I[section]};b={u['key']:u for u in N[section]}
 assert list(a)==list(b) and len(a)==len(b);delta[section]=[]
 for key,u in a.items():
  v=b[key];assert u.keys()==v.keys()
  for field in u:
   if field not in ('source_sha256','source_text','text_sha256'):assert u[field]==v[field],(key,field)
  if u['source_text']!=v['source_text']:
   delta[section].append(key);details.append(dict(key=key,line=u['line'],locator=u['locator'],text_sha256_before=u['text_sha256'],text_sha256_proposed_after=v['text_sha256']))
  else:assert u['text_sha256']==v['text_sha256']
  if u['source']!=source:assert u==v
assert delta=={'exercises':['toolkit-gp.html::exercise-18'],'material_source_units':['toolkit-gp.html::node-1213']}
assert details==d['affected_exercises']+d['affected_physical_material_units']
assert delta==d['full_temporary_inventory_parser']['actual_delta']
pc=v3['preservation_check'];S=json.loads(P(pc['selection']).read_text());C=json.loads(P(pc['frozen_manifest']).read_text());protected={}
assert H(pc['selection'])==pc['selection_sha256'] and H(pc['frozen_manifest'])==pc['frozen_manifest_sha256']
for p,row in S['proof_files'].items():protected[p]=row['sha256'];protected.update(row['evidence_sha256'])
frozen={str(Path(C['snapshot'])/p):h for p,h in C['frozen_inputs_sha256'].items()}
assert len(S['proof_files'])==490 and len(protected)==565 and len(frozen)==2431
assert all(H(p)==h for p,h in protected.items()) and all(H(p)==h for p,h in frozen.items())
assert all(H(p)==h for p,h in pc['held_metadata_sha256'].items())
z=dict(schema_version=1,status='approved_narrow_read_only_positive_domain_qualification_proposal',reviewer='/root/modules_resume/gp34_review',
 reviewed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),proposal=proposal,proposal_sha256=H(proposal),
 original_preparation_time_preserved=d['prepared_at_utc'],source=source,source_sha256_before=H(source),proposed_source_sha256_after=hashlib.sha256(new).hexdigest(),
 inventory=d['inventory_at_preparation'],inventory_sha256=d['inventory_sha256_at_preparation'],exact_substitutions=d['replacements'],
 independent_exact_current_component_review=review,independent_exact_current_component_review_sha256=H(review),
 fresh_independent_full_parser=dict(actual_command=['python3','/tmp/modules-review-gp34-positive-domain-proposal19.py'],actual_exit_code=0,
  simulated_inventory=str(np),simulated_inventory_sha256=H(np),page_count=29,counts=N['counts'],actual_delta=delta,
  all_keys_lines_locators_tags_attributes_order_other_fields_unchanged=True,all_original_question_math_and_answer_bytes_unchanged=True,exact_forward_reverse_source_bytes=True),
 actual_proof_source_sha256=d['actual_proof_source_sha256'],actual_standalone_evidence=d['actual_standalone_evidence'],
 mathematical_review=[
  dict(clause='Positive feature dimension',decision='approved_explicit_dimension_domain',
   declarations=['SafeLearning.CompleteModulesGPLinearInformationBounds.actual_linear_design_information_has_the_dimension_trace_bound'],
   reason='The printed ordinary real formula divides by d, and the actual finite-dimensional Jensen bound requires a nonempty feature index, corresponding exactly to positive integer d. Adding d>=1 explicitly supplies that domain without changing any matrix, inequality, constructive design, or numerical answer.'),
  dict(clause='Positive sample count excludes the genuine zero-observation counterexample',decision='approved_explicit_sample_domain',
   declarations=['SafeLearning.CompleteModulesGPLinearInformationStrictness.actual_zero_observation_design_is_the_boundary_exception_to_strict_nonattainment','SafeLearning.CompleteModulesGPLinearInformationStrictness.actual_positive_fewer_samples_than_dimensions_prevent_attaining_the_dimension_bound'],
   reason='The actual zero Gram has information0 and the printed dimension bound at T0 is also0, so unqualified T<d strict nonattainment fails. The true strict-concavity/arbitrary-design theorem proves strict nonattainment for0<T<d. Adding integer T>=1 to the containing question supplies precisely this missing premise to every unchanged worked answer clause.'),
  dict(clause='Existing positive noise and fixed-parameter asymptotic assumptions',decision='exact_local_context_checked',
   source_units=['toolkit-gp.html::node-119','toolkit-gp.html::node-417'],
   reason='Page notation line86 explicitly supplies lambda>0. Section4 line437 fixes kernel, dimension, domain and regularizer when taking T to infinity, and allows constants to depend on them. These exact local assumption passages were read; the proposal leaves them and all formulas unchanged.'),
  dict(clause='Scope of corrected question and unchanged two answer nodes',decision='approved_narrow_question_prefix_only',
   reason='Fresh physical DOM parsing confirms the new integer premises lie in the same containing Exercise3.4 question. Both worked answer physical nodes1217/1218 are byte-identical in text and retain their full formulas/examples. This narrow domain approval does not approve the unresolved arbitrary finite Gaussian mutual-information formula or generic nondivisible unit-norm tight-frame existence.')],
 preservation_check=dict(selection=pc['selection'],selection_sha256=H(pc['selection']),frozen_manifest=pc['frozen_manifest'],frozen_manifest_sha256=H(pc['frozen_manifest']),
  selected_proofs=490,selected_source_evidence_paths=565,frozen_inputs=2431,all_hashes_exact=True,all29_current_inventory_pages_exact=True,held_modules_metadata_exact=True),
 missing_clauses=[],limits=['TMP-only under HOLD33; no live HTML/inventory/coverage/index or publication mutation.',
  'Approval covers only the precise positive-integer d and T premise insertion. Root release/serialization, application and a fresh exact corrected-source review remain separate.',
  'V1–V3 review bodies, original review times, compiler warning logs and failed histories remain immutable. Current uncorrected source remains pending; this proposal does not close its two scope defects until actually applied and re-reviewed.',
  'General finite-dimensional Gaussian mutual information and general nondivisible unit-norm tight-frame existence remain pending; no whole exercise/material unit is approved.'])
out=Path('/tmp/modules-gp34-positive-domain-independent-proposal-review19.json');assert not out.exists()
assert P(source).read_bytes()==old and H(d['inventory_at_preparation'])==d['inventory_sha256_at_preparation']
assert all(H(p)==h for p,h in I['source_sha256'].items())
out.write_text(json.dumps(z,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(dict(path=str(out),sha256=H(out),actual_delta=delta,status=z['status']),indent=2))

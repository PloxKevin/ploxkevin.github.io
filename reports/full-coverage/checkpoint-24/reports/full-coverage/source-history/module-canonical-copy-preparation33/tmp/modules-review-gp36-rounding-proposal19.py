from pathlib import Path
import datetime,hashlib,importlib.util,json,re,shutil,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
def P(x):return Path(x) if Path(x).is_absolute() else R/x
def H(x):return hashlib.sha256(P(x).read_bytes()).hexdigest()
proposal='/tmp/modules-gp36-confidence-rounding19-proposal.json'
assert H(proposal)=='f49ae275172b51d4bce12fc33444a43a79fb04f5021ddc85aceb755ebf1f7ccf'
d=json.loads(P(proposal).read_text());source=d['source'];old=P(source).read_bytes()
assert H(source)==d['source_sha256_before']=='980a30185175bb46598746b8c332c783cfd32aa0a0a8c110cd7266284dff037b'
assert len(d['replacements'])==1
r=d['replacements'][0]
assert old.count(r['before'].encode())==r['count']==1
start=r['before'].index('Numbers: ');end=r['before'].index(' The printed constant',start)
expected_numbers=r'Numbers: $-2\log0.05\approx5.99$ and $\ln101\approx4.62$; corrected: $\frac{0.1}{0.1}\sqrt{\ln101-2\ln0.05}\approx3.26$; original: $0.1\sqrt{\ln2-2\ln0.05}\approx0.26$.'
assert r['after']==r['before'][:start]+expected_numbers+r['before'][end:]
new=old.replace(r['before'].encode(),r['after'].encode(),1)
assert new.replace(r['after'].encode(),r['before'].encode(),1)==old
assert old.count(b'\n')==new.count(b'\n') and hashlib.sha256(new).hexdigest()==d['proposed_source_sha256_after']
assert P(d['source_bytes_before_snapshot']).read_bytes()==old and H(d['source_bytes_before_snapshot'])==d['source_bytes_before_snapshot_sha256']
assert P(d['source_bytes_proposed_after_snapshot']).read_bytes()==new and H(d['source_bytes_proposed_after_snapshot'])==d['source_bytes_proposed_after_snapshot_sha256']
assert H(d['inventory_at_preparation'])==d['inventory_sha256_at_preparation']=='c5edf43ad9e1b2d408b328fd331b2a52c624126dd167100541d5ca931986a963'
I=json.loads(P(d['inventory_at_preparation']).read_text())
assert all(H(p)==h for p,h in I['source_sha256'].items()) and len(I['source_sha256'])==29
review='/tmp/modules-gp36-confidence-scaling-components-review19-v4-order.json'
assert H(review)=='143d59e94d4011cb95a588a8d8637577fbb502d642b6a3ad24e5a28696875f10'
v3=json.loads(P(review).read_text())
for p,h in d['actual_proof_source_sha256'].items():assert H(p)==h==v3['proof_source_sha256'][p]
assert len(d['actual_proof_source_sha256'])==2
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
assert old_ex[19].text()==v3['exercise']['source_text']
assert new_ex[19].text()==old_ex[19].text().replace(A.nodes[1243-1].text(),B.nodes[1243-1].text(),1)
assert all(A.nodes[n-1].text()==B.nodes[n-1].text() for n in (1239,1246,1251,1253))
sim=Path('/tmp/modules-gp36-rounding-independent-proposal19-simulation')
assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
for f in (R/'SafeLearning').glob('*.html'):shutil.copyfile(f,sim/'SafeLearning'/f.name)
assert len(list((sim/'SafeLearning').glob('*.html')))==29
(sim/source).write_bytes(new)
spec=importlib.util.spec_from_file_location('gp36_rounding_independent_inventory19',R/'book/inventory_claims.py')
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
assert delta=={'exercises':['toolkit-gp.html::exercise-20'],'material_source_units':['toolkit-gp.html::node-1243']}
assert details==d['affected_exercises']+d['affected_physical_material_units']
assert delta==d['full_temporary_inventory_parser']['actual_delta']
pc=v3['preservation_check'];S=json.loads(P(pc['selection']).read_text());C=json.loads(P(pc['frozen_manifest']).read_text());protected={}
assert H(pc['selection'])==pc['selection_sha256'] and H(pc['frozen_manifest'])==pc['frozen_manifest_sha256']
for p,row in S['proof_files'].items():protected[p]=row['sha256'];protected.update(row['evidence_sha256'])
frozen={str(Path(C['snapshot'])/p):h for p,h in C['frozen_inputs_sha256'].items()}
assert len(S['proof_files'])==490 and len(protected)==565 and len(frozen)==2431
assert all(H(p)==h for p,h in protected.items()) and all(H(p)==h for p,h in frozen.items())
assert all(H(p)==h for p,h in pc['held_metadata_sha256'].items())
z=dict(schema_version=1,status='approved_narrow_read_only_confidence_rounding_proposal',reviewer='/root/modules_resume/gp34_review',
 reviewed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),proposal=proposal,proposal_sha256=H(proposal),
 original_preparation_time_preserved=d['prepared_at_utc'],source=source,source_sha256_before=H(source),proposed_source_sha256_after=hashlib.sha256(new).hexdigest(),
 inventory=d['inventory_at_preparation'],inventory_sha256=d['inventory_sha256_at_preparation'],exact_substitutions=d['replacements'],
 independent_exact_current_component_review=review,independent_exact_current_component_review_sha256=H(review),
 fresh_independent_full_parser=dict(actual_command=['python3','/tmp/modules-review-gp36-rounding-proposal19.py'],actual_exit_code=0,
  simulated_inventory=str(np),simulated_inventory_sha256=H(np),page_count=29,counts=N['counts'],actual_delta=delta,
  all_keys_lines_locators_tags_attributes_order_other_fields_unchanged=True,all_question_answer_b_coverage_derivation_other_math_and_non_numeric_answer_a_bytes_unchanged=True,exact_forward_reverse_source_bytes=True),
 actual_proof_source_sha256=d['actual_proof_source_sha256'],actual_standalone_evidence=d['actual_standalone_evidence'],
 mathematical_review=[
  dict(clause='Both printed logarithmic decimals are approximate values',decision='approved_actual_rounding_qualification',
   declarations=['SafeLearning.CompleteModulesGPCorrectionNumerics.actual_minus_twice_log_delta_printed_rounding_and_false_exact_equality','SafeLearning.CompleteModulesGPCorrectionNumerics.actual_log_one_hundred_one_printed_rounding_and_false_exact_equality'],
   reason='Genuine actual source-matched proofs establish rounding error<.005 for5.99 and4.62 and prove the former exact equalities false. The proposal explicitly changes them to approximation signs, directly matching the proved precision.'),
  dict(clause='Both one-point noise formulas retain their true logarithms',decision='approved_exact_unrounded_formulas_and_rounded_outputs',
   declarations=['SafeLearning.CompleteModulesGPCorrectionNumerics.actual_noise_formulas_at_the_literal_exercise_parameters','SafeLearning.CompleteModulesGPCorrectionNumerics.actual_original_and_corrected_noise_printed_two_decimal_roundings','SafeLearning.CompleteModulesGPCorrectionNumerics.actual_noise_ratio_printed_one_decimal_rounding'],
   reason='The corrected expression keeps ln101−2ln.05 and its exact.1/.1 prefactor; the original keeps ln2−2ln.05 and exact.1 prefactor. Actual true noise enclosures prove3.26 and.26 with error<.005, and true ratio12.6 with error<.05. The proposal removes all rounded exact radicand substitutions while preserving these independently certified final approximations.'),
  dict(clause='All scope and other physical claims stay fixed',decision='approved_narrow_answer_a_numeric_range_only',
   reason='Exact reconstruction changes only the Numbers range in the physical Answer(a) paragraph. Every mathematical comparison before it and factor discussion after it is byte-identical. Question, Answer(b), coverage derivation and heading are text-identical. Fresh full29page inventory/DOM parsing yields exactly exercise20/node1243 text changes with every key,line,locator,DOM tag,attribute,order and other field fixed.'),
  dict(clause='Scope of approval',decision='approved_proposal_only_no_whole_unit_promotion',
   reason='Current eight-primary61-declaration independent component review is bound exactly. This narrow numeric proposal does not prove or independently approve the broader corrected concentration theorem, does not apply source edits, and does not release HOLD33.')],
 preservation_check=dict(selection=pc['selection'],selection_sha256=H(pc['selection']),frozen_manifest=pc['frozen_manifest'],frozen_manifest_sha256=H(pc['frozen_manifest']),
  selected_proofs=490,selected_source_evidence_paths=565,frozen_inputs=2431,all_hashes_exact=True,all29_current_inventory_pages_exact=True,held_modules_metadata_exact=True),
 missing_clauses=[],limits=['TMP-only under HOLD33; no live HTML/inventory/coverage/index or publication mutation.',
  'Approval covers only the exact Answer(a) Numbers-range correction. Root release/serialization, application and a fresh exact corrected-source review remain separate.',
  'V1–V4 component review bodies, original review times, actual warning logs and failed histories remain immutable. The current uncorrected source remains pending literal precision until actually applied and re-reviewed.',
  'Generic corrected GP concentration validity and its complete assumptions remain outside these component proofs; no whole exercise or material unit is promoted.',
  'The parent proposal status label mentions domain qualification, but its actual exact delta and this approval concern only numeric precision. No domain or mathematical scope text changes.'])
out=Path('/tmp/modules-gp36-rounding-independent-proposal-review19.json');assert not out.exists()
assert P(source).read_bytes()==old and H(d['inventory_at_preparation'])==d['inventory_sha256_at_preparation']
assert all(H(p)==h for p,h in I['source_sha256'].items())
out.write_text(json.dumps(z,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(dict(path=str(out),sha256=H(out),actual_delta=delta,status=z['status']),indent=2))

from pathlib import Path
import datetime,hashlib,importlib.util,json,re,shutil,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
def P(p):return Path(p) if Path(p).is_absolute() else R/p
def H(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
kind=sys.argv[1];assert kind in ('states','tail_comment')
if kind=='states':
 proposal='/tmp/modules-landscape-independence-positive-noise-v2-modal19-proposal.json';ph='f9ffde064949c5f70379d5ebd9a614f2739fd051b71c8fcdd6c47d88ff1163f7'
 review='/tmp/modules-landscape-independent-states-components-review19-v1.json';vh='c486fa2ce79743af102f21b56e3e2fcb13b5b8eaa21f434c10b3ca9f9692bb75'
 substitutions=[('States within one episode are dependent, because each state contains all past noise.','States within one episode can be dependent because later states carry earlier noise.'),(r'Only at $k=1$',r'With $\sigma\gt0$, only at $k=1$')]
 expected={'exercises':[],'material_source_units':['landscape.html::node-962']};stem='independence-positive-noise-modal'
else:
 proposal='/tmp/modules-landscape-tail-underflow-comment19-proposal.json';ph='d052b7d2125020d832076d87fe4207098be8b6f0f982a2cb75b37325313becdb'
 review='/tmp/modules-landscape-ar1-components-review19-v4-real-numerics.json';vh='083ed5376c48888c4e2e52f78f84dc5a9f08677bf5e2db46a3a12e95d58ebbbd'
 substitutions=[('Numerical Recipes erfcc, relative error below 1.2e-7 for every z','Numerical Recipes erfcc approximation; double-precision underflow can still return 0 for large z')]
 expected={'exercises':[],'material_source_units':[]};stem='tail-underflow-comment'
assert H(proposal)==ph and H(review)==vh
d=json.loads(P(proposal).read_text());V=json.loads(P(review).read_text());source=d['source'];old=P(source).read_bytes();assert H(source)==d['source_sha256_before']==V['source_sha256'] and len(d['replacements'])==1
r=d['replacements'][0];derived=r['before']
for a,b in substitutions:assert derived.count(a)==1;derived=derived.replace(a,b,1)
assert derived==r['after'] and old.count(r['before'].encode())==r['count']==1
new=old.replace(r['before'].encode(),r['after'].encode(),1);assert new.replace(r['after'].encode(),r['before'].encode(),1)==old and old.count(b'\n')==new.count(b'\n')
assert hashlib.sha256(new).hexdigest()==d['proposed_source_sha256_after']
assert P(d['source_bytes_before_snapshot']).read_bytes()==old and H(d['source_bytes_before_snapshot'])==d['source_bytes_before_snapshot_sha256']
assert P(d['source_bytes_proposed_after_snapshot']).read_bytes()==new and H(d['source_bytes_proposed_after_snapshot'])==d['source_bytes_proposed_after_snapshot_sha256']
assert H(d['inventory_at_preparation'])==d['inventory_sha256_at_preparation']==V['inventory_sha256'];I=json.loads(P(V['inventory']).read_text());assert len(I['source_sha256'])==29 and all(H(p)==h for p,h in I['source_sha256'].items())
assert all(H(p)==h for p,h in V['proof_source_sha256'].items()) and all(H(p)==h for p,h in V['prior_immutable_artifacts'].items())
for p,h in d['actual_proof_source_sha256'].items():assert V['proof_source_sha256'][p]==h and H(p)==h
ve=V['actual_standalone_evidence'];ve=ve if isinstance(ve,list)else[ve]
for e in d['actual_standalone_evidence']:
 v=next(a for a in ve if a['compiler_manifest']==e['compiler_manifest']);assert H(e['compiler_manifest'])==e['compiler_manifest_sha256']==v['compiler_manifest_sha256']
 q=json.loads(P(e['compiler_manifest']).read_text());a=q['files'][0];assert a==e['raw_execution_record'] and q==v['raw_execution_record'] and a['exit_code']==0 and a['source_unchanged'] and H(a['file'])==a['sha256'] and H(a['log'])==a['log_sha256']
names=V.get('all_reviewed_theorem_declarations',V.get('all_new_full_read_theorem_declarations'));assert all(n in names for n in d['proof_declarations'])
prior_proposals={}
if kind=='states':
 h=d['transparent_prior_proposal_preserved'];assert H(h['path'])==h['sha256'];prior=json.loads(P(h['path']).read_text());assert prior['prepared_at_utc']==h['original_preparation_time'] and prior['source_sha256_before']==d['source_sha256_before'] and prior['actual_proof_source_sha256']==d['actual_proof_source_sha256'] and prior['actual_standalone_evidence']==d['actual_standalone_evidence']
 for p,k in [('source_bytes_before_snapshot','source_bytes_before_snapshot_sha256'),('source_bytes_proposed_after_snapshot','source_bytes_proposed_after_snapshot_sha256')]:assert H(prior[p])==prior[k]
 assert H(prior['full_temporary_inventory_parser']['simulated_inventory'])==prior['full_temporary_inventory_parser']['simulated_inventory_sha256'];prior_proposals[h['path']]=h['sha256']
else:
 for e in d['independently_executed_implementation_evidence']:assert H(e['path'])==e['sha256']
 emp=json.loads(P(d['independently_executed_implementation_evidence'][1]['path']).read_text());assert emp['cancellation_result']['actual_underflow39']['directQ']==0
 for e in emp['actual_executions']:assert e['actual_exit_code']==0 and H(e['stdout'])==e['stdout_sha256'] and H(e['stderr'])==e['stderr_sha256']
 for e in emp['new_harness_sources']:assert H(e['new_script'])==e['new_sha256'] and H(e['original_script'])==e['original_sha256']
 for e in emp['complete_original_vs_new_output_comparisons']:assert H(e['new_file'])==e['new_sha256'] and H(e['original_file'])==e['original_sha256']
sys.path.insert(0,str(R/'book'));from validate import Document
A,B=Document(old.decode()),Document(new.decode());assert len(A.nodes)==len(B.nodes) and all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line)for a,b in zip(A.nodes,B.nodes))
if kind=='states':
 assert A.nodes[961].text()!=B.nodes[961].text()
 slider=next(n for n in A.nodes if n.attrs.get('id')=='ls-ce-T');assert slider.attrs['min']=='5'
 for a,b in zip(A.root.descendants('script'),B.root.descendants('script')):assert a.text()==b.text()
else:
 assert r['before'].lstrip().startswith('//') and r['after'].lstrip().startswith('//') and '\n'not in r['before'] and '\n'not in r['after']
 old_line=next(l for l in old.splitlines()if l.decode()==r['before']);new_line=next(l for l in new.splitlines()if l.decode()==r['after'])
 assert old.replace(old_line,b'',1)==new.replace(new_line,b'',1)
 marker='    // ===== Constraint Semantics Explorer =====\n'
 def extract(raw):
  t=raw.decode();s=t.index('    (function(){',t.index(marker)+len(marker));e=t.index('    })();',s)+len('    })();');return t[s:e]
 assert extract(old).replace(r['before'],'',1)==extract(new).replace(r['after'],'',1)
sim=Path('/tmp/modules-landscape-'+stem+'-independent19-simulation');assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
for p in (R/'SafeLearning').glob('*.html'):shutil.copyfile(p,sim/'SafeLearning'/p.name)
assert len(list((sim/'SafeLearning').glob('*.html')))==29;(sim/source).write_bytes(new)
spec=importlib.util.spec_from_file_location('landscape_scope_'+kind+'_independent_inventory19',R/'book/inventory_claims.py');generator=importlib.util.module_from_spec(spec);spec.loader.exec_module(generator);generator.ROOT=sim;generator.OUT=sim/'book/coverage';generator.inventory();np=generator.OUT/'inventory.json';N=json.loads(np.read_text());assert I['counts']==N['counts']
delta={};details=[]
for section in ('exercises','material_source_units'):
 aa={u['key']:u for u in I[section]};bb={u['key']:u for u in N[section]};assert list(aa)==list(bb) and len(aa)==len(bb);delta[section]=[]
 for key,u in aa.items():
  v=bb[key];assert u.keys()==v.keys()
  for field in u:
   if field not in ('source_sha256','source_text','text_sha256'):assert u[field]==v[field],(key,field)
  if u['source_text']!=v['source_text']:delta[section].append(key);details.append(dict(key=key,line=u['line'],locator=u['locator'],text_sha256_before=u['text_sha256'],text_sha256_proposed_after=v['text_sha256']))
  else:assert u['text_sha256']==v['text_sha256']
  if u['source']!=source:assert u==v
assert delta==expected==d['full_temporary_inventory_parser']['actual_delta'] and details==d['affected_exercises']+d['affected_physical_material_units']
assert H(d['full_temporary_inventory_parser']['simulated_inventory'])==d['full_temporary_inventory_parser']['simulated_inventory_sha256']
pc=V['preservation_check'];S=json.loads(P(pc['selection']).read_text());F=json.loads(P(pc['frozen_manifest']).read_text());protected={}
assert H(pc['selection'])==pc['selection_sha256'] and H(pc['frozen_manifest'])==pc['frozen_manifest_sha256']
for p,v in S['proof_files'].items():protected[p]=v['sha256'];protected.update(v['evidence_sha256'])
frozen={str(Path(F['snapshot'])/p):h for p,h in F['frozen_inputs_sha256'].items()};assert len(S['proof_files'])==490 and len(protected)==565 and len(frozen)==2431
assert all(H(p)==h for p,h in protected.items()) and all(H(p)==h for p,h in frozen.items()) and all(H(p)==h for p,h in pc['held_metadata_sha256'].items())
if kind=='states':
 math=[dict(clause='Modal state dependence includes genuine model exceptions',decision='approved_exact_narrow_modal_correction',reason='Actualnonzero-noise/non-k1/atleasttwo-state covariance proves dependence. The initial0state isconstant, sigma0makes deterministic states and gain1resets to independentfreshnoise, so categorical every-state dependence/allpast-noise is false. The new can-be dependent because laterstatescarryearliernoise follows from genuine source unrolling/covariance and retains all exceptions.'),dict(clause='Positive-noise gain1 necessity and sufficiency',decision='approved_exact_narrow_domain_qualification',reason='Actual sourcegain1positive-time family has genuine iIndepFun. For sigma≠0, k≠1 andT≥2 firsttwo actual states are dependent, so the family cannot bejointindependent. Withsigma>0supplies the absentnoise premise and actual source horizon slider5..100suppliesT≥2. The actualsigma0deterministic exception remains in the nextsource sentence. No absent assumption is waived.'),dict(clause='Retain genuine product chance formula and invariance witness',decision='approved_exact_preserved_components',reason='Every other paragraph formula/example is byteidentical: truegain1joint-event product probability andsigma0finitechecker scope plus actualpassinginitial0/alltime trajectory butsafe−10maps47/25unsafe witness. No exercise or executablecode changes; every source unit except962retains exacttext.'),dict(clause='Scope',decision='approved_proposal_only',reason='Original node962review/times/gaps and originalpartialV1proposal preserved. This approves both narrow wording substitutions only; no application or freshcorrectedwholeunit approval.')]
else:
 math=[dict(clause='Machine-range qualification replaces false global relative-error guarantee',decision='approved_exact_comment_correction',reason='Fresh originalIIFEactualNodeexecution independently reproduceddirectQ39=0. GenuineactualGaussianErfcTailprovesstrictlypositive realtailat everyfinitereal threshold; relativeerrorat39is1, contradicting foreveryzclaim. The newapproximation/underflowqualification is true and doesnot invent a replacementuniversalerror theorem.'),dict(clause='Preserve executable and all material/exercise text',decision='approved_exact_comment_only_scope',reason='The onlychangedline is an ordinaryone-lineJavaScriptcomment. Removing thatline fromold/new source andexplorerIIFEs gives completebyteequality. All29pagefullinventory exercise/material text/fields andDOMstructure match; onlythecurrentpage sourcefingerprint differs. No freshNodeexecution isclaimed, becauseevery executable statement is unchanged.'),dict(clause='Existing algorithm attribution scope',decision='existing_local_attribution_preserved_without_new_external_approval',reason='NumericalRecipeserfcc attribution is unchanged; thisreview addresses onlytheremovalof globalfloatingerror wording andadds machine-rangequalification. It doesnot independentlyapprove anexternalalgorithmerror theorem or certify allrealapproximation accuracy.'),dict(clause='Scope',decision='approved_proposal_only',reason='Originalglobalrelativeerrorgap and allactualbeforeexecutionevidence remain preserved. Thisapprovecommentreplacementonly, with noapplication or wholecorrectedsource/materialpromotion.')]
z=dict(schema_version=1,status='approved_narrow_read_only_'+stem+'_proposal',reviewer='/root/modules_resume/gp34_review',reviewed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),proposal=proposal,proposal_sha256=ph,original_preparation_time_preserved=d['prepared_at_utc'],source=source,source_sha256_before=H(source),proposed_source_sha256_after=hashlib.sha256(new).hexdigest(),inventory=V['inventory'],inventory_sha256=V['inventory_sha256'],exact_substitutions=d['replacements'],independently_derived_narrow_substitutions=[dict(before=a,after=b)for a,b in substitutions],independent_current_component_review=review,independent_current_component_review_sha256=vh,
 fresh_independent_full_parser=dict(actual_command=['python3','/tmp/modules-review-landscape-scope-proposals19.py',kind],actual_exit_code=0,simulated_inventory=str(np),simulated_inventory_sha256=H(np),page_count=29,counts=N['counts'],actual_delta=delta,all_keys_lines_locators_tags_attributes_order_other_fields_unchanged=True,all_exercises_unchanged=True,all_executable_statements_unchanged=True,exact_forward_reverse_source_bytes=True),actual_proof_source_sha256=d['actual_proof_source_sha256'],actual_standalone_evidence=d['actual_standalone_evidence'],mathematical_review=math,
 preservation_check=dict(selection=pc['selection'],selection_sha256=H(pc['selection']),frozen_manifest=pc['frozen_manifest'],frozen_manifest_sha256=H(pc['frozen_manifest']),selected_proofs=490,selected_source_evidence_paths=565,frozen_inputs=2431,all_hashes_exact=True,all29_current_inventory_pages_exact=True,held_modules_metadata_exact=True),prior_reviews_immutable={review:vh,**V['prior_immutable_artifacts'],**prior_proposals},missing_proposal_clauses=[],limits=['TMP-onlyunderHOLD33. No live source/assets/materialinventory/coverage/selection/builder/index/ledger writes orpublication.','Onlytheexactproposednarrowcorrection isapproved. Originalreviewdates/decisions/gaps preserved; application/rootserialization/freshcorrectedwhole review remain separate.','Actualproof/compiler/rawlog andwarning/failedsnapshot bytes immutable. This reviewreuses genuine exactactualruns and adds afreshfulltemporaryparser; nofresh Lean theoremcompile oraggregatekernel/axiom audit isclaimed.','Mathematical iidGaussian model, finitePRNG/binary64 empirical evidence andrealanalyticproofs remain distinct. NoexactPRNGlaw/browser/fullpageconfidence or universalfloatingerror theorem inferred.','All490/565/2431/29page fingerprints andearlier source-restoration history preserved.'])
if kind=='states':z['transparent_prior_proposal_preserved']=d['transparent_prior_proposal_preserved']
else:z['independently_executed_implementation_evidence']=d['independently_executed_implementation_evidence']
out=Path('/tmp/modules-landscape-'+stem+'-independent-proposal-review19.json');assert not out.exists()
assert H(proposal)==ph and H(review)==vh and P(source).read_bytes()==old and all(H(p)==h for p,h in I['source_sha256'].items()) and all(H(p)==h for p,h in z['prior_reviews_immutable'].items())
out.write_text(json.dumps(z,indent=2,ensure_ascii=False)+'\n');print(json.dumps(dict(path=str(out),sha256=H(out),actual_delta=delta,status=z['status']),indent=2))

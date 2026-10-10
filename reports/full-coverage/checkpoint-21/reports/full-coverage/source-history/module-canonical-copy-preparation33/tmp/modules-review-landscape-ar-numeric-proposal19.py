from pathlib import Path
import datetime,hashlib,importlib.util,json,re,shutil,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
def P(p):return Path(p) if Path(p).is_absolute() else R/p
def H(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
proposal='/tmp/modules-landscape-ar-numeric-precision19-proposal-v2-declarations.json';ph='c4fb44e41617f4ece603e2da512e71c77fe139894faba8f4b652c198f29077ba'
review='/tmp/modules-landscape-ar1-components-review19-v4-real-numerics.json';vh='083ed5376c48888c4e2e52f78f84dc5a9f08677bf5e2db46a3a12e95d58ebbbd'
assert H(proposal)==ph and H(review)==vh
d=json.loads(P(proposal).read_text());V=json.loads(P(review).read_text());source=d['source'];old=P(source).read_bytes()
assert H(source)==d['source_sha256_before']==V['source_sha256'] and len(d['replacements'])==1
r=d['replacements'][0];substitutions=[
 (r'$\sigma_\infty=0.1155$',r'$\sigma_\infty=\sqrt{0.01/0.75}\approx0.1155$'),
 (r'$p_\infty=1-\Phi(0.2/0.1155)=1-\Phi(1.732)=0.0416$',r'$p_\infty=1-\Phi(0.2/\sqrt{0.01/0.75})=1-\Phi(\sqrt3)\approx0.0416$ ($\sqrt3\approx1.732$)'),
 (r'$p_3=0.0044$',r'$p_3\approx0.0044$'),(r'$p_5=0.0256$',r'$p_5\approx0.0256$'),(r'$p_{10}=0.0410$',r'$p_{10}\approx0.0410$'),
 (r'$\mathbb E[N]=1.484$',r'$\mathbb E[N]\approx1.484$'),
 (r'$Tp_\infty=1.665$',r'$Tp_\infty\approx1.665$'),
 (r'$\mathbb P(\exists t:x_t\gt1)\le1.484$',r'$\mathbb P(\exists t:x_t\gt1)\le\mathbb E[N]\lt1.485$')]
derived=r['before']
for a,b in substitutions:assert derived.count(a)==1;derived=derived.replace(a,b,1)
assert derived==r['after'] and old.count(r['before'].encode())==r['count']==1
new=old.replace(r['before'].encode(),r['after'].encode(),1)
assert new.replace(r['after'].encode(),r['before'].encode(),1)==old and old.count(b'\n')==new.count(b'\n')
assert hashlib.sha256(new).hexdigest()==d['proposed_source_sha256_after']=='3a9d82413d17a1b7bfb69119ff97f0e06d5f9aa2f04121559ba7b1030b2ac981'
assert P(d['source_bytes_before_snapshot']).read_bytes()==old and H(d['source_bytes_before_snapshot'])==d['source_bytes_before_snapshot_sha256']
assert P(d['source_bytes_proposed_after_snapshot']).read_bytes()==new and H(d['source_bytes_proposed_after_snapshot'])==d['source_bytes_proposed_after_snapshot_sha256']
assert H(d['inventory_at_preparation'])==d['inventory_sha256_at_preparation']==V['inventory_sha256'];I=json.loads(P(V['inventory']).read_text())
assert len(I['source_sha256'])==29 and all(H(p)==h for p,h in I['source_sha256'].items())
assert all(H(p)==h for p,h in V['proof_source_sha256'].items()) and all(H(p)==h for p,h in V['prior_immutable_artifacts'].items())
assert d['actual_proof_source_sha256']=={p:h for p,h in V['proof_source_sha256'].items()if any(x in p for x in ['GaussianTailNumericalBounds.lean','ARTailTable.lean','ARCountNumerics.lean','ARStationaryNumerics.lean'])}
for e in d['actual_standalone_evidence']:
 v=next(a for a in V['actual_standalone_evidence']if a['compiler_manifest']==e['compiler_manifest']);assert H(e['compiler_manifest'])==e['compiler_manifest_sha256']==v['compiler_manifest_sha256']
 q=json.loads(P(e['compiler_manifest']).read_text());a=q['files'][0];assert a==e['raw_execution_record'] and q==v['raw_execution_record'] and a['exit_code']==0 and a['source_unchanged'] and H(a['file'])==a['sha256'] and H(a['log'])==a['log_sha256']
assert all(n in V['all_reviewed_theorem_declarations']for n in d['proof_declarations'])
history=d['transparent_declaration_reference_correction'];assert H(history['prior_proposal'])==history['prior_proposal_sha256']
prior=json.loads(P(history['prior_proposal']).read_text());old_keys=set(prior);new_keys=set(d)-{'transparent_declaration_reference_correction'};assert old_keys==new_keys
assert all(prior[k]==d[k]for k in old_keys if k!='proof_declarations') and prior['proof_declarations']==history['old_declaration_references_preserved'] and d['proof_declarations']==history['new_declaration_references_checked_against_actual_source']
assert prior['prepared_at_utc']==d['prepared_at_utc']==history['prior_prepared_at_utc_preserved']
sys.path.insert(0,str(R/'book'));from validate import Document
A,B=Document(old.decode()),Document(new.decode());assert len(A.nodes)==len(B.nodes) and all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line)for a,b in zip(A.nodes,B.nodes))
old_ex=[n for n in A.root.descendants('details')if n.child('summary')and re.match(r'^(Exercise\b|(Easy|Medium|Hard)\s+\d+\b)',n.child('summary').text().strip(),re.I)]
new_ex=[n for n in B.root.descendants('details')if n.child('summary')and re.match(r'^(Exercise\b|(Easy|Medium|Hard)\s+\d+\b)',n.child('summary').text().strip(),re.I)]
assert len(old_ex)==len(new_ex)==19 and old_ex[18].text()==V['exercise']['source_text']
assert A.nodes[1368-1].text()!=B.nodes[1368-1].text()
for n in (1350,1354,1355,1357,1359,1360,1361,1363,1365,1366,1367,1369):assert A.nodes[n-1].text()==B.nodes[n-1].text()
for a,b in zip(A.root.descendants('script'),B.root.descendants('script')):assert a.text()==b.text()
sim=Path('/tmp/modules-landscape-ar-numeric-independent19-simulation');assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
for p in (R/'SafeLearning').glob('*.html'):shutil.copyfile(p,sim/'SafeLearning'/p.name)
assert len(list((sim/'SafeLearning').glob('*.html')))==29;(sim/source).write_bytes(new)
spec=importlib.util.spec_from_file_location('landscape_ar_numeric_independent_inventory19',R/'book/inventory_claims.py');generator=importlib.util.module_from_spec(spec);spec.loader.exec_module(generator)
generator.ROOT=sim;generator.OUT=sim/'book/coverage';generator.inventory();np=generator.OUT/'inventory.json';N=json.loads(np.read_text());assert I['counts']==N['counts']
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
assert delta=={'exercises':['landscape.html::exercise-19'],'material_source_units':['landscape.html::node-1368']}
assert details==d['affected_exercises']+d['affected_physical_material_units'] and delta==d['full_temporary_inventory_parser']['actual_delta']
assert H(d['full_temporary_inventory_parser']['simulated_inventory'])==d['full_temporary_inventory_parser']['simulated_inventory_sha256']
pc=V['preservation_check'];S=json.loads(P(pc['selection']).read_text());F=json.loads(P(pc['frozen_manifest']).read_text());protected={}
assert H(pc['selection'])==pc['selection_sha256'] and H(pc['frozen_manifest'])==pc['frozen_manifest_sha256']
for p,v in S['proof_files'].items():protected[p]=v['sha256'];protected.update(v['evidence_sha256'])
frozen={str(Path(F['snapshot'])/p):h for p,h in F['frozen_inputs_sha256'].items()};assert len(S['proof_files'])==490 and len(protected)==565 and len(frozen)==2431
assert all(H(p)==h for p,h in protected.items()) and all(H(p)==h for p,h in frozen.items()) and all(H(p)==h for p,h in pc['held_metadata_sha256'].items())
z=dict(schema_version=1,status='approved_narrow_read_only_ar_numeric_precision_proposal',reviewer='/root/modules_resume/gp34_review',reviewed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),proposal=proposal,proposal_sha256=ph,original_preparation_time_preserved=d['prepared_at_utc'],transparent_original_declaration_preparation_history=history,all_prior_metadata_bytes_preserved=True,source=source,source_sha256_before=H(source),proposed_source_sha256_after=hashlib.sha256(new).hexdigest(),inventory=V['inventory'],inventory_sha256=V['inventory_sha256'],exact_substitutions=d['replacements'],independently_derived_eight_narrow_formula_substitutions=[dict(before=a,after=b)for a,b in substitutions],independent_current_component_review=review,independent_current_component_review_sha256=vh,
 fresh_independent_full_parser=dict(actual_command=['python3','/tmp/modules-review-landscape-ar-numeric-proposal19.py'],actual_exit_code=0,simulated_inventory=str(np),simulated_inventory_sha256=H(np),page_count=29,counts=N['counts'],actual_delta=delta,all_keys_lines_locators_tags_attributes_order_other_fields_unchanged=True,all_other_question_general_answer_background_joint_law_and_explorer_source_bytes_unchanged=True,exact_forward_reverse_source_bytes=True),actual_proof_source_sha256=d['actual_proof_source_sha256'],actual_standalone_evidence=d['actual_standalone_evidence'],
 mathematical_review=[dict(clause='Retain true unrounded stationary expressions and qualify every displayed decimal',decision='approved_exact_numerical_precision_correction',reason='Actual variance1/75=.01/.75 andSD=sqrt(1/75) are true exact formulas. The actual stationary radius isexactly sqrt3, so the trueCDFexpression keeps the exactroot. Genuine real bounds prove nearest0.1155/1.732/0.0416 and40p∞nearest1.665; all four rounded exact equalities are formally disproved. The new equalities connect only true unrounded expressions and all decimals use approximation signs.'),dict(clause='True transient marginals and actual count roundings',decision='approved_exact_numerical_precision_correction',reason='The true39rationally checked transient probability intervals, truefirststate radius6 andpositive four-decimal-zero tail, and genuine count integral identity establish all printed transient/count rounded outputs. P3/P5/P10 andEN are proved unequal to exact displayed decimals, now explicitly marked approximations. TrueENbounds1.48415<EN<1.484355 also proveEN<1.485.'),dict(clause='Use the actual expected count in Markov and an upward certified decimal',decision='approved_exact_bound_correction',reason='The actual recursive joint event is genuinely bounded by the true expected count. The certified upper1.484355<1.485 justifies the proposed chainPjoint≤EN<1.485. GenuineEN>1 andPjoint≤1 make the Markovbound vacuous. The proposed text retains the true unrounded quantity rather than substituting a nearest rounded count.'),dict(clause='Preserve valid finite empirical observation and all other source clauses',decision='approved_exact_one_paragraph_scope',reason='Only originalparagraph1368changes. General laws/moments/tails/erfc/futureindependence and the exact sourcequestion remain byte-identical. Independently reproduced200000episodeempirical0.688555 supports the retained qualified about0.69 observation; no exactprobability or certifiedPRNGlaw is inferred. The actual code and separate false global relative-error comment are unchanged.'),dict(clause='Proposal approval scope',decision='approved_proposal_only_no_application_or_whole_corrected_source_promotion',reason='The freshfull29pageparser changes exactlyexercise19/node1368text, preserving all556/12774keys/lines/locators/DOM/otherfields and all490/565/2431protectedbytes. This approves only the narrow readonly substitution. Current originalreviewdates/decisions remain preserved; application/rootserialization/freshcorrectedwhole review remain separate.')],
 preservation_check=dict(selection=pc['selection'],selection_sha256=H(pc['selection']),frozen_manifest=pc['frozen_manifest'],frozen_manifest_sha256=H(pc['frozen_manifest']),selected_proofs=490,selected_source_evidence_paths=565,frozen_inputs=2431,all_hashes_exact=True,all29_current_inventory_pages_exact=True,held_modules_metadata_exact=True),prior_reviews_immutable={review:vh,**V['prior_immutable_artifacts'],history['prior_proposal']:history['prior_proposal_sha256']},missing_proposal_clauses=[],limits=['TMP-only underHOLD33. No live HTML/assets/inventory/coverage/index mutation or publication.','This is independent exact semantic/byte/freshparser approval of one proposed paragraph correction only. Current whole exercise/numericanswer remains pending unapplied literal correction; no fresh corrected whole-source approval is recorded.','Thirteen actual0primary files/85declarations and six reviewed local dependencies remain exact. Real warnings, failed source snapshots and earlier review times/decisions are preserved. No fresh theorem compilation or aggregate kernel/axiom audit is claimed in this proposal review.','The proposed arithmetic uses exact positive source parameters and actual connected Gaussian/count laws. Analytic error bounds and trustedkernel rational decisions certify numeric roundings; hostfloats do not certify them.','Finite empirical explorer estimate remains qualified; no browser/fullpage verification, iidPRNGlaw, exactjointprobability, pathconvergence or genericconcentration approval.','Separate unrestricted binary64 sourcecomment relative-error gap remains unchanged; this proposal does not claim to fix or approve it.'])
out=Path('/tmp/modules-landscape-ar-numeric-independent-proposal-review19.json');assert not out.exists()
assert H(proposal)==ph and H(review)==vh and P(source).read_bytes()==old and all(H(p)==h for p,h in I['source_sha256'].items()) and all(H(p)==h for p,h in z['prior_reviews_immutable'].items())
out.write_text(json.dumps(z,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(dict(path=str(out),sha256=H(out),actual_delta=delta,status=z['status']),indent=2))

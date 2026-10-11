from pathlib import Path
import datetime,hashlib,importlib.util,json,re,shutil,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
def P(p):return Path(p) if Path(p).is_absolute() else R/p
def H(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
proposal='/tmp/modules-landscape-lyapunov-positive-level19-proposal.json'
review='/tmp/modules-landscape-classification-components-review19-v2-lyapunov.json'
assert H(proposal)=='f3e6d6c9f8b97e207b505ddc9b3379c615882e429413092e43cd9103c61b9e6f'
assert H(review)=='b9bb077b9e6bfc998ed70e0820463ca68548580f03d21b1eb1608c1606229bc4'
d=json.loads(P(proposal).read_text());V=json.loads(P(review).read_text())
source=d['source'];old=P(source).read_bytes();assert H(source)==d['source_sha256_before']==V['source_sha256']
assert len(d['replacements'])==1;r=d['replacements'][0]
assert r['before'].count('which a Lyapunov sublevel-set certificate provides')==1
assert r['after']==r['before'].replace('which a Lyapunov sublevel-set certificate provides','which a positive-level Lyapunov sublevel-set certificate provides',1)
assert old.count(r['before'].encode())==r['count']==1
new=old.replace(r['before'].encode(),r['after'].encode(),1)
assert new.replace(r['after'].encode(),r['before'].encode(),1)==old
assert old.count(b'\n')==new.count(b'\n') and hashlib.sha256(new).hexdigest()==d['proposed_source_sha256_after']=='320c65214e18458a2eab5896497698882f43c9228c7716f59aef548aced74d4f'
assert P(d['source_bytes_before_snapshot']).read_bytes()==old and H(d['source_bytes_before_snapshot'])==d['source_bytes_before_snapshot_sha256']
assert P(d['source_bytes_proposed_after_snapshot']).read_bytes()==new and H(d['source_bytes_proposed_after_snapshot'])==d['source_bytes_proposed_after_snapshot_sha256']
assert H(d['inventory_at_preparation'])==d['inventory_sha256_at_preparation']==V['inventory_sha256']
I=json.loads(P(V['inventory']).read_text());assert len(I['source_sha256'])==29 and all(H(p)==h for p,h in I['source_sha256'].items())
assert all(H(p)==h for p,h in V['proof_source_sha256'].items()) and all(H(p)==h for p,h in V['prior_immutable_artifacts'].items())
assert d['actual_proof_source_sha256']=={p:h for p,h in V['proof_source_sha256'].items()if 'LyapunovStability.lean' in p}
ev=V['lyapunov_actual_standalone_evidence'];assert H(ev['compiler_manifest'])==ev['compiler_manifest_sha256']
q=json.loads(P(ev['compiler_manifest']).read_text());assert q==ev['raw_execution_record'];a=q['files'][0]
assert a['exit_code']==0 and a['source_unchanged'] and H(a['file'])==a['sha256'] and H(a['log'])==a['log_sha256']
assert d['actual_standalone_evidence']==[dict(compiler_manifest=ev['compiler_manifest'],compiler_manifest_sha256=ev['compiler_manifest_sha256'],raw_execution_record=a)]
assert all(n in V['all_reviewed_theorem_declarations']for n in d['proof_declarations'])
sys.path.insert(0,str(R/'book'));from validate import Document
A,B=Document(old.decode()),Document(new.decode())
assert len(A.nodes)==len(B.nodes) and all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line)for a,b in zip(A.nodes,B.nodes))
old_ex=[n for n in A.root.descendants('details')if n.child('summary')and re.match(r'^(Exercise\b|(Easy|Medium|Hard)\s+\d+\b)',n.child('summary').text().strip(),re.I)]
new_ex=[n for n in B.root.descendants('details')if n.child('summary')and re.match(r'^(Exercise\b|(Easy|Medium|Hard)\s+\d+\b)',n.child('summary').text().strip(),re.I)]
assert len(old_ex)==len(new_ex)==19 and old_ex[14].text()==V['exercise']['source_text']
assert new_ex[14].text()==old_ex[14].text().replace('which a Lyapunov sublevel-set certificate provides','which a positive-level Lyapunov sublevel-set certificate provides',1)
assert A.nodes[1297-1].text()!=B.nodes[1297-1].text()
assert all(A.nodes[n-1].text()==B.nodes[n-1].text()for n in (167,168,169,1285,1294,1332,1336,1338,1344,1345,1346))
sim=Path('/tmp/modules-landscape-positive-level-independent19-simulation');assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
for p in (R/'SafeLearning').glob('*.html'):shutil.copyfile(p,sim/'SafeLearning'/p.name)
assert len(list((sim/'SafeLearning').glob('*.html')))==29;(sim/source).write_bytes(new)
spec=importlib.util.spec_from_file_location('landscape_positive_level_independent_inventory19',R/'book/inventory_claims.py');generator=importlib.util.module_from_spec(spec);spec.loader.exec_module(generator)
generator.ROOT=sim;generator.OUT=sim/'book/coverage';generator.inventory()
np=generator.OUT/'inventory.json';N=json.loads(np.read_text());assert I['counts']==N['counts']
delta={};details=[]
for section in ('exercises','material_source_units'):
 aa={u['key']:u for u in I[section]};bb={u['key']:u for u in N[section]};assert list(aa)==list(bb)and len(aa)==len(bb);delta[section]=[]
 for key,u in aa.items():
  v=bb[key];assert u.keys()==v.keys()
  for field in u:
   if field not in ('source_sha256','source_text','text_sha256'):assert u[field]==v[field],(key,field)
  if u['source_text']!=v['source_text']:
   delta[section].append(key);details.append(dict(key=key,line=u['line'],locator=u['locator'],text_sha256_before=u['text_sha256'],text_sha256_proposed_after=v['text_sha256']))
  else:assert u['text_sha256']==v['text_sha256']
  if u['source']!=source:assert u==v
assert delta=={'exercises':['landscape.html::exercise-15'],'material_source_units':['landscape.html::node-1297']}
assert details==d['affected_exercises']+d['affected_physical_material_units'] and delta==d['full_temporary_inventory_parser']['actual_delta']
pc=V['preservation_check'];S=json.loads(P(pc['selection']).read_text());C=json.loads(P(pc['frozen_manifest']).read_text());protected={}
assert H(pc['selection'])==pc['selection_sha256']and H(pc['frozen_manifest'])==pc['frozen_manifest_sha256']
for p,v in S['proof_files'].items():protected[p]=v['sha256'];protected.update(v['evidence_sha256'])
frozen={str(Path(C['snapshot'])/p):h for p,h in C['frozen_inputs_sha256'].items()}
assert len(S['proof_files'])==490 and len(protected)==565 and len(frozen)==2431
assert all(H(p)==h for p,h in protected.items()) and all(H(p)==h for p,h in frozen.items())and all(H(p)==h for p,h in pc['held_metadata_sha256'].items())
z=dict(schema_version=1,status='approved_narrow_read_only_positive_level_answer_proposal',reviewer='/root/modules_resume/gp34_review',reviewed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),proposal=proposal,proposal_sha256=H(proposal),original_preparation_time_preserved=d['prepared_at_utc'],source=source,source_sha256_before=H(source),proposed_source_sha256_after=hashlib.sha256(new).hexdigest(),inventory=V['inventory'],inventory_sha256=V['inventory_sha256'],exact_substitutions=d['replacements'],independent_current_component_review=review,independent_current_component_review_sha256=H(review),
 fresh_independent_full_parser=dict(actual_command=['python3','/tmp/modules-review-landscape-positive-level-proposal19.py'],actual_exit_code=0,simulated_inventory=str(np),simulated_inventory_sha256=H(np),page_count=29,counts=N['counts'],actual_delta=delta,all_keys_lines_locators_tags_attributes_order_other_fields_unchanged=True,all_source_question_qualifier_section1_and_other_answers_bytes_unchanged=True,exact_forward_reverse_source_bytes=True),
 actual_proof_source_sha256=d['actual_proof_source_sha256'],actual_standalone_evidence=d['actual_standalone_evidence'],
 mathematical_review=[dict(clause='Positive-level Lyapunov sublevel certificate supplies equilibrium stability',decision='approved_exact_domain_qualification',declarations=d['proof_declarations'][:2],reason='Actual generic originStable is proved from positive level c>0, continuous positive-definite V with V(0)=0, compact sublevel, fixed zero equilibrium and strict decrease. Compactness gives a positive minimum outside each epsilon ball and continuity gives a genuine initial neighborhood. Actual iterate induction then proves the epsilon-delta stability property. With continuous F, the actual generic compact convergence proof yields attraction for every sublevel initial state. These are the genuine assumptions in the local Section1 certificate, with the new phrase supplying c>0.'),dict(clause='Unqualified zero-level certificate can fail equilibrium stability',decision='approved_actual_counterexample_motivation',declarations=[d['proof_declarations'][2]],reason='The genuine new theorem proves that the actual doubling map is unstable, while its actual V=x² zero-level sublevel is the compact singleton and nonzero-member strict decrease is vacuous. This confirms the literal domain qualification rather than using stability as a hypothesis.'),dict(clause='Only the extra stability implication is qualified',decision='approved_exact_narrow_answer_phrase',reason='The proposal inserts positive-level only in original Answer1297. Section1 invariance/attraction statement is byte-identical and remains applicable at zero level where appropriate. The eight classification labels, input/output examples, question and interpretation qualifier are byte-identical. Fresh actual full29page inventory and DOM parsing changes exactly exercise15/node1297 text.'),dict(clause='Scope of approval',decision='approved_proposal_only_no_whole_corrected_or_current_source_promotion',reason='This independent review approves only the read-only substitution, not its application or whole corrected exercise. Current V1/V2 dates and decisions remain exact; the unqualified current whole answer/exercise remain pending until application and fresh exact-source review. No full SafeOpt/CBF or external GP-model guarantee is approved.')],
 preservation_check=dict(selection=pc['selection'],selection_sha256=H(pc['selection']),frozen_manifest=pc['frozen_manifest'],frozen_manifest_sha256=H(pc['frozen_manifest']),selected_proofs=490,selected_source_evidence_paths=565,frozen_inputs=2431,all_hashes_exact=True,all29_current_inventory_pages_exact=True,held_modules_metadata_exact=True),prior_reviews_immutable={review:H(review),**V['prior_immutable_artifacts']},missing_proposal_clauses=[],limits=['TMP-only under HOLD33; no live HTML/inventory/coverage/index mutation or publication.', 'Only this proposed one-phrase positive-level qualification is approved. Root serialization, application and a fresh whole exact-source review remain separate.', 'Two independently reviewed actual0 primary files/13 declarations remain immutable. The actual deprecation warning and inherited compact proof evidence are retained; no new kernel/axiom audit is claimed.', 'This proposal leaves Section1 zero-level invariance/attraction context fixed and does not qualify or approve its external Berkenkamp/GP-probability attribution.','Prior V1/V2 artifacts retain exact original bodies, review times and decisions, including earlier mathematical and current unapplied-domain gaps.'])
out=Path('/tmp/modules-landscape-positive-level-independent-proposal-review19.json');assert not out.exists()
assert P(source).read_bytes()==old and all(H(p)==h for p,h in I['source_sha256'].items())and all(H(p)==h for p,h in z['prior_reviews_immutable'].items())
out.write_text(json.dumps(z,indent=2,ensure_ascii=False)+'\n');print(json.dumps(dict(path=str(out),sha256=H(out),actual_delta=delta,status=z['status']),indent=2))

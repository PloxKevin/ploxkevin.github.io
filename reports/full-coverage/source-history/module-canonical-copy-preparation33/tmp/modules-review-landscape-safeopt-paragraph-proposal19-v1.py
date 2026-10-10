from pathlib import Path
import datetime,hashlib,importlib.util,json,shutil,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
def P(p):return Path(p)if Path(p).is_absolute()else R/p
def H(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
proposal='/tmp/modules-landscape-safeopt-paragraph-precision19-proposal.json';ph='30ac1e5953d59feda16beaa9d4c7f76ac606a66f92a8f513af685fa6cc18d6dd';assert H(proposal)==ph
review='/tmp/modules-landscape-unsafe-seeds-components-review19-v1.json';vh='53b2883f4ab44ac520d1127716b79d7f08a6827926e644ce17aae769628cbe31';assert H(review)==vh
V=json.loads(P(review).read_text());d=json.loads(P(proposal).read_text());I=json.loads(P(V['inventory']).read_text());pc=V['preservation_check']
old=P(d['source']).read_bytes();assert H(d['source'])==d['source_sha256_before']==V['source_sha256']and H(V['inventory'])==d['inventory_sha256_at_preparation']==V['inventory_sha256']
assert len(d['replacements'])==1and len(d['precise_subspan_replacements'])==3
r=d['replacements'][0];derived=r['before']
for sub in d['precise_subspan_replacements']:
 assert derived.count(sub['before'])==1
 derived=derived.replace(sub['before'],sub['after'],1)
assert derived==r['after']and old.count(r['before'].encode())==r['count']==1
new=old.replace(r['before'].encode(),r['after'].encode(),1);assert new.count(r['after'].encode())==1and new.replace(r['after'].encode(),r['before'].encode(),1)==old
assert hashlib.sha256(new).hexdigest()==d['proposed_source_sha256_after']and old.count(b'\n')==new.count(b'\n')
for key,hkey,expected in[('source_bytes_before_snapshot','source_bytes_before_snapshot_sha256',old),('source_bytes_proposed_after_snapshot','source_bytes_proposed_after_snapshot_sha256',new)]:assert P(d[key]).read_bytes()==expected and H(d[key])==d[hkey]
unchanged=[r'Too small an $L$ wrongly certifies unevaluated points;',r'Not checkable: $B$ and the kernel.']
assert all(r['before'].count(t)==r['after'].count(t)==1for t in unchanged)
prior={review:vh,**V['prior_immutable_artifacts'],'/tmp/modules-landscape-control-affine-domain-components-review19-v1.json':'f3231782464495ae798215a246772791772c6cecfdb2d31c0c5dc027b53b46e8'}
assert d['immutable_original_review']['sha256']==prior[d['immutable_original_review']['path']]
S=json.loads(P(pc['selection']).read_text());F=json.loads(P(pc['frozen_manifest']).read_text());protected={}
for p,v in S['proof_files'].items():protected[p]=v['sha256'];protected.update(v['evidence_sha256'])
frozen={str(Path(F['snapshot'])/p):h for p,h in F['frozen_inputs_sha256'].items()}
assert len(S['proof_files'])==490and len(protected)==565and len(frozen)==2431
def protect():
 assert H(proposal)==ph and H(review)==vh and H(V['inventory'])==V['inventory_sha256']and H(pc['selection'])==pc['selection_sha256']and H(pc['frozen_manifest'])==pc['frozen_manifest_sha256']
 for rows in(protected,frozen,I['source_sha256'],pc['held_metadata_sha256'],prior,d['actual_proof_source_sha256'],d['preservation_check']['all_live_safelearning_sources_and_assets_sha256']):assert all(H(p)==h for p,h in rows.items())
 assert P(d['source']).read_bytes()==old
protect()
for e in d['actual_standalone_evidence']:
 assert H(e['compiler_manifest'])==e['compiler_manifest_sha256']
 q=json.loads(P(e['compiler_manifest']).read_text());a=q['files'][0]
 assert q['status']=='passed'and q['all_sources_still_match']and a==e['raw_execution_record']and a['exit_code']==0and a['source_unchanged']and H(a['file'])==a['sha256']and H(a['log'])==a['log_sha256']
seed_names=V['actual_standalone_evidence']['all_theorem_declarations'];assert all(n in seed_names for n in d['proof_declarations'])
primary=d['primary_attribution']
assert H(primary['primary_local_pdf'])==primary['primary_local_pdf_sha256']and H(primary['primary_local_text'])==primary['primary_local_text_sha256']
text=P(primary['primary_local_text']).read_text();lines=text.splitlines()
ranges=[(254,317),(648,674),(699,779),(1014,1073)]
excerpts=[dict(line_start=s,line_end=t,text='\n'.join(lines[s-1:t]))for s,t in ranges]
assert 'Safety violations %'in excerpts[-1]['text']and all(x in excerpts[-1]['text']for x in['3.95','0.859','28.62','13.38'])
assert 'algorithm with βt from (7)'in text and 'misspecified RKHS norm of 2.5 in (7)'in text and 'to the best of our knowledge' in text
web='/tmp/modules-landscape-safeopt-paragraph-independent-primary-web19-v1.txt';wh='9ab51c07150f55701e1ca925b6c5331b46074d28f3ebd9d91dd5c4c3ea84a3ae';assert H(web)==wh
sys.path.insert(0,str(R/'book'));from validate import Document
A,B=Document(old.decode()),Document(new.decode());assert len(A.nodes)==len(B.nodes)==d['full_temporary_inventory_parser']['html_structure_node_count']
assert all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line)for a,b in zip(A.nodes,B.nodes))
for a,b in zip(A.root.descendants('script'),B.root.descendants('script')):assert a.text()==b.text()
assert A.nodes[1335].text()==V['exact_assigned_material_unit']['source_text']and A.nodes[1335].line==710
assert B.nodes[1335].text()!=A.nodes[1335].text()
sim=Path('/tmp/modules-landscape-safeopt-paragraph-independent19-simulation');assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
for p in (R/'SafeLearning').glob('*.html'):shutil.copyfile(p,sim/'SafeLearning'/p.name)
assert len(list((sim/'SafeLearning').glob('*.html')))==29;(sim/d['source']).write_bytes(new)
spec=importlib.util.spec_from_file_location('landscape_safeopt_paragraph_independent_inventory19',R/'book/inventory_claims.py');gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen);gen.ROOT=sim;gen.OUT=sim/'book/coverage';gen.inventory();np=gen.OUT/'inventory.json';N=json.loads(np.read_text());assert I['counts']==N['counts']
delta={};details=[]
for section in('exercises','material_source_units'):
 aa={u['key']:u for u in I[section]};bb={u['key']:u for u in N[section]};assert list(aa)==list(bb);delta[section]=[]
 for key,u in aa.items():
  v=bb[key];assert u.keys()==v.keys()
  for field in u:
   if field not in('source_sha256','source_text','text_sha256'):assert u[field]==v[field],(key,field)
  if u['source_text']!=v['source_text']:delta[section].append(key);details.append(dict(key=key,line=u['line'],locator=u['locator'],text_sha256_before=u['text_sha256'],text_sha256_proposed_after=v['text_sha256']))
  else:assert u['text_sha256']==v['text_sha256']
  if u['source']!=d['source']:assert u==v
assert delta==d['full_temporary_inventory_parser']['actual_delta']==dict(exercises=['landscape.html::exercise-18'],material_source_units=['landscape.html::node-1336'])
assert details==d['affected_exercises']+d['affected_physical_material_units']
assert H(d['full_temporary_inventory_parser']['simulated_inventory'])==d['full_temporary_inventory_parser']['simulated_inventory_sha256']
assessment=[
 dict(scope='First actual replacement: modal underbound/admission failure',status='approved_narrow_modal_correction',reason='Genuine official linear RKHS coefficient1 has actual norm²1>B1/4 while every possible positive-design query is safe. Underbounds can invalidate confidence and enable unsafe admission, without inevitably admitting an unsafe point in every domain/run. The new can phrasing is supported; it supplies no generic concentration derivation.'),
 dict(scope='Second actual replacement: empirical rates and historical schedule',status='approved_exact_primary_attribution_correction',reason='Independent official arXiv v1 section5.2 explicitly calls the original algorithm with data-dependent formula7 Real-beta-SafeOpt; section6.1 explicitly uses misspecified norm2.5 in that formula against true norm10. Official Table1 contains exact average/worst 3.95/28.62 percent for constantbeta2 and .859/13.38 percent forB2.5. The proposal preserves those reported rates and attributes their actual historical schedule. It neither labels v1 formula7 a proven correct modern concentration theorem nor treats empirical frequencies as universal failure probabilities.'),
 dict(scope='Third actual replacement: selected unsafe seed',status='approved_exact_selected_query_qualification',reason='The new literal condition says if the unsafe seed is selected at the first query, that selected value violates safety. Exported order equivalence matches this condition. Genuine mixed seed initialization/endpoints and unique width-max safe first query disprove the old unconditional implication; all associated model/probability limitations are preserved.'),
 dict(scope='Entire source and mathematical boundary',status='proposal_only_no_whole_paragraph_or_exercise_approval',reason='Full original/proposed paragraph and exact surrounding Exercise1.4 question/answer read. Only the three stated subspans differ. Existing whole-exercise and generic confidence/CBF/theory/checkability gaps are unchanged; correction/application/fresh corrected whole-source review remain separate.')]
remaining=[
 dict(id='unchanged-too-small-L-categorical-failure',exact_excerpt=unchanged[0],status='requires_can_or_other_precise_failure_qualification_for_literal_universal_reading',reason='The proposal intentionally leaves this text unchanged. An underestimated Lipschitz constant invalidates its general transfer proof and can certify unsafe neighbors, but need not cause any unsafe admission: a finite entirely positive decision set cannot contain an unsafe point. It should not acquire whole approval from the three corrected neighboring subspans.'),
 dict(id='unchanged-model-checkability-categorical-wording',exact_excerpt=unchanged[1],status='contextual_practical_advice_needs_qualification_if_literal_universal_claim',reason='Primary section6.1 gives a qualified practical difficulty, explicitly to the best of the authors knowledge and for realistic prior knowledge/nontrivial applications; it is not a proof no kernel/norm bound can be established in any model. Official finite-dimensional linear RKHS examples have explicit norms/kernels. No blanket impossibility theorem is supplied.'),
 dict(id='generic-RKHS-concentration-and-all-time-query-safety',status='pending_true_generic_confidence_derivation_and_exact_query_rule_transfer',reason='Correct attribution and finite counterexamples do not derive true adaptive simultaneous confidence from the stated RKHS/conditional-noise assumptions.'),
 dict(id='unchanged-remaining-source-context',status='prior_exact_broad_review_remains_pending',reason='CBF paragraph711 and summary713 are byteidentical. General ODE/feasibility/Nagumo/QP/ISSf/learned-residual scopes and summary nobody-can-verify wording remain separate. ModelError evidence is neighboring context only.')]
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
z=dict(schema_version=1,status='approved_exact_three_subspan_readonly_proposal_whole_paragraph_pending',reviewer='/root/modules_resume/gp34_review',reviewed_at_utc=now,proposal=proposal,proposal_sha256=ph,original_preparation_time_preserved=d['prepared_at_utc'],source=d['source'],source_sha256_before=H(d['source']),proposed_source_sha256_after=hashlib.sha256(new).hexdigest(),inventory=V['inventory'],inventory_sha256=V['inventory_sha256'],exact_paragraph_replacement=d['replacements'],independently_composed_exact_three_subspan_replacements=d['precise_subspan_replacements'],exact_forward_reverse_and_line_counts=True,
 fresh_independent_full_parser=dict(actual_command=['python3','/tmp/modules-review-landscape-safeopt-paragraph-proposal19-v1.py'],actual_exit_code=0,simulated_inventory=str(np),simulated_inventory_sha256=H(np),page_count=29,counts=N['counts'],actual_delta=delta,all_keys_lines_locators_tags_attributes_order_other_fields_unchanged=True,all_executable_code_unchanged=True,dom_node_count=len(A.nodes)),
 independent_current_component_review=review,independent_current_component_review_sha256=vh,actual_proof_source_sha256=d['actual_proof_source_sha256'],actual_standalone_evidence=d['actual_standalone_evidence'],proof_declarations=d['proof_declarations'],primary_attribution=dict(primary,independent_relevant_local_primary_ranges_read=excerpts,actual_fresh_official_web_read=dict(url='https://arxiv.org/html/2403.12948v1',exact_returned_text_snapshot=web,sha256=wh,relevant_html_lines=['129 formula7','291-298 Real-beta and conditionalnoise/RKHS norm','325 misspecified2.5 formula7','440-445 exact Table1 and sampling context']),scope='Exact version-specific historical empirical attribution and qualified practical discussion only; no generic concentration validity approval or empirical rerun.'),mathematical_and_primary_review=assessment,missing_proposed_replacement_clauses=[],unchanged_original_paragraph_remaining_clauses=remaining,
 prior_reviews_immutable=prior,preservation_check=dict(pc,rechecked_at_utc=now,all_hashes_exact=True,all_live31_source_asset_fingerprints_exact=True),limits=['TMP-only under HOLD33; no live material/source/metadata/inventory/coverage/index/selection/ledger writes or publication.','Fresh independent full29page inventory parser truly completed; all556 exercises/12774units structure and onlyex18/node1336 text changes exactly verified.','All prior review/proposal/body/failed source/actual warnings/times remain immutable. All490/565/2431/29page/31source-assets current fingerprints exact; prior restoration history preserved.','This approves only the exact three proposed corrections. The unchanged too-small-L/checkability claims and generic concentration/whole original paragraph/exercise status remain pending.','The original v1 schedule is attributed accurately without silently declaring that historical formula a correct present concentration theorem. Primary text/table are attributed empirical observations; no exact implementation reproduction of the external experiment or theorem of its probabilities is inferred.'])
out=Path('/tmp/modules-landscape-safeopt-paragraph-independent-proposal-review19-v1.json');assert not out.exists();protect();out.write_text(json.dumps(z,indent=2,ensure_ascii=False)+'\n');print(json.dumps(dict(path=str(out),sha256=H(out),actual_delta=delta,unchanged_literal_gaps=2),indent=2))

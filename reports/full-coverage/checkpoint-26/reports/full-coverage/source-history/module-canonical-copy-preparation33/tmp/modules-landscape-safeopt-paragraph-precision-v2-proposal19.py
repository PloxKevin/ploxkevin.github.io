from pathlib import Path
import hashlib,json,re,datetime,sys,importlib.util,shutil
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
BH=lambda b:hashlib.sha256(b).hexdigest()
source='SafeLearning/landscape.html';old=(R/source).read_bytes()
assert BH(old)=='4626b82bdcabbdb7275d8abc16864d6cca9c41e9346db312f366cc4b5f2d627e'
ip=R/'book/coverage/inventory-after-correction33.json';I=json.loads(ip.read_text())
assert H(ip)=='c5edf43ad9e1b2d408b328fd331b2a52c624126dd167100541d5ca931986a963'
before=re.search(r'<p style="margin-top:0;"><strong>SafeOpt</strong>.*?</p>',old.decode()).group()
spans=[
 (r'Too small a $B$, or a heuristic constant in place of $\beta_t$, narrows the intervals and the safe set swallows unsafe points:',r'Too small a $B$, or a heuristic constant in place of $\beta_t$, can produce intervals that are too narrow and admit unsafe points.', 'Qualify failure as possible; underestimated assumptions invalidate the guarantee without forcing unsafe admissions in every model or run.'),
 (r'3.95% unsafe runs on average (28.62% worst) with $\beta\equiv2$, and 0.859% (13.38% worst) with the rigorous $\beta_t$ but a norm bound $\|f\|_k\le2.5$ against a true norm of $10$ (Fiedler et al. 2024).',r'Fiedler et al. (2024, Table 1) report 3.95% unsafe runs on average (28.62% worst) with $\beta\equiv2$, and 0.859% (13.38% worst) for Real-$\beta$-SafeOpt using their data-dependent formula (7) in arXiv v1, with a norm bound $\|f\|_k\le2.5$ against a true norm of $10$.','Preserve all four exact empirical rates and norm values; identify the actual Real-beta data-dependent schedule in the verified primary version instead of implying Sui\'s earlier schedule was used in those experiments.'),
 (r'an unsafe point in $S_0$ violates safety at $t=1$.',r'if an unsafe seed point is selected at $t=1$, that first query violates safety.','Bind a first-query violation to the actually selected point. Mixed unsafe membership alone does not force selection; the new true width-argmax countermodel demonstrates this.')
]
spans.extend([
 (r'Not checkable: $B$ and the kernel.',r'Difficult to justify for an unknown $f$: $B$ and the kernel.','State the engineering difficulty for the unknown target, rather than universal impossibility; known exact RKHS functions can have rigorously computed norm bounds.'),
 (r'Too small an $L$ wrongly certifies unevaluated points;',r'Too small an $L$ can wrongly certify unevaluated points;','An underestimated Lipschitz constant can invalidate transfer but does not necessarily admit an unsafe point; the true positive-design countermodel stays safe under every query.')
])
after=before
for a,b,_ in spans:
 assert after.count(a)==1,(a,after);after=after.replace(a,b,1)
assert old.count(before.encode())==1
new=old.replace(before.encode(),after.encode(),1)
assert new.replace(after.encode(),before.encode(),1)==old and old.count(b'\n')==new.count(b'\n')
asset_paths=sorted(p for p in (R/'SafeLearning').rglob('*') if p.is_file())
assets_before={str(p.relative_to(R)):H(p) for p in asset_paths}
sys.path.insert(0,str(R/'book'));from validate import Document
A,B=Document(old.decode()),Document(new.decode())
assert len(A.nodes)==len(B.nodes)
assert all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line) for a,b in zip(A.nodes,B.nodes))
sim=Path('/tmp/modules-landscape-safeopt-paragraph-precision-v2-proposal19-simulation');sim.mkdir(exist_ok=False)
(sim/'SafeLearning').mkdir()
for p in (R/'SafeLearning').glob('*.html'):shutil.copyfile(p,sim/'SafeLearning'/p.name)
(sim/source).write_bytes(new)
spec=importlib.util.spec_from_file_location('landscape_safeopt_precision_inventory19',R/'book/inventory_claims.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
m.ROOT=sim;m.OUT=sim/'book/coverage';m.inventory()
np=m.OUT/'inventory.json';N=json.loads(np.read_text());assert I['counts']==N['counts']
delta={};details=[]
for field in ['exercises','material_source_units']:
 a={u['key']:u for u in I[field]};b={u['key']:u for u in N[field]};assert a.keys()==b.keys();delta[field]=[]
 for k,u in a.items():
  v=b[k];assert u.keys()==v.keys()
  for f in u:
   if f not in ['source_sha256','source_text','text_sha256']:assert u[f]==v[f],(k,f)
  if u['source_text']!=v['source_text']:
   delta[field].append(k);details.append(dict(key=k,line=u['line'],locator=u['locator'],text_sha256_before=u['text_sha256'],text_sha256_proposed_after=v['text_sha256']))
  else:assert u['text_sha256']==v['text_sha256']
  if u['source']!=source:assert u==v
assert delta=={'exercises':['landscape.html::exercise-18'],'material_source_units':['landscape.html::node-1336']}
proofs={};evidence=[]
specs=[
 ('book/coverage/checks/modules-landscape-unsafe-seeds19-trial2-standalone.json','af8fb2b5d13f21aaebc4ce3fe25c476b1347267e9cb9a1cfc4b33bf760d0e531','22b63e2a542e7270eefe5fe62d98205fcec7a9be2e039ea9efaaa8924ad299a7','Supports the qualified seed-selection statement and the absence of inevitable failure; not the generic theoretical-beta confidence/noise run or empirical rates.'),
 ('book/coverage/checks/modules-landscape-model-error19-trial3-standalone.json','b78949bf5354edfbbaea3c17bcb77b1a627e860f08c781462ad28621d79b0f0a','2dc702d7980309c73b3356a4b3a96844ff0f8bc88d5f527eef99099004eb7b5b','Separate immutable neighboring model-error component; no wording in node1338 is edited or approved by this paragraph710 proposal.')]
specs.append(('book/coverage/checks/modules-landscape-known-bounds19-trial1-standalone.json','70a3155507678534b79050c8b8de56b8d548787ea96c8786f8ff48f984507af2','9972b6db1bc73e9553b7254767981efbdf4c5670a51c09e97d42c38c8ea289b6','Actual known-function norm/least Lipschitz constant and wrong-L safe-domain witness justify only the two new wording qualifications. No unknown-function norm inferred from data.'))
for p,msha,ssha,scope in specs:
 q=R/p;assert H(q)==msha;j=json.loads(q.read_text());f=j['files'][0]
 assert f['exit_code']==0 and f['source_unchanged'] and H(R/f['file'])==f['sha256']==ssha
 assert H(R/f['log'])==f['log_sha256'];proofs[f['file']]=f['sha256']
 evidence.append(dict(compiler_manifest=p,compiler_manifest_sha256=H(q),raw_execution_record=f,precise_use=scope))
cm=R/'reports/full-coverage/checkpoint-18-manifest.json';C=json.loads(cm.read_text());paths={}
for p,row in C['proof_files'].items():
 paths[p]=row['sha256'];assert H(R/p)==row['sha256']
 for p,s in row['evidence_sha256'].items():paths[p]=s;assert H(R/p)==s
for p,s in C['frozen_inputs_sha256'].items():assert H(R/C['snapshot']/p)==s
assert len(C['proof_files'])==490 and len(paths)==565 and len(C['frozen_inputs_sha256'])==2431
primarytext=R/'sources/text/2403.12948.txt'
pt=primarytext.read_text();assert 'algorithm with βt from (7)' in pt
assert all(number in pt for number in ['3.95','28.62','0.859','13.38'])
primary_evidence={'official_version_url':'https://arxiv.org/html/2403.12948v1','official_pdf_url':'https://arxiv.org/pdf/2403.12948v1','primary_local_pdf':'sources/pdf/2403.12948.pdf','primary_local_pdf_sha256':H(R/'sources/pdf/2403.12948.pdf'),'primary_local_text':'sources/text/2403.12948.txt','primary_local_text_sha256':H(primarytext),'precise_locations':['Section5.2 textlines655-670 explicitly Real-beta formula(7)','Table1 textlines1025-1035 exact four empirical rates and true norm10 setting','Section6.4 textlines1058-1068 experimental noise/nominal variance context'],'limits':'Observed empirical Table1 rates are attributed; no Lean theorem of those empirical probabilities, and no claim that they used Sui2B+300gamma log-cubed schedule.'}
prefix='/tmp/modules-landscape-safeopt-paragraph-precision-v2-19'
for suffix,b in [('-source-before.html',old),('-source-proposed-after.html',new)]:
 p=Path(prefix+suffix)
 with p.open('xb') as f:f.write(b)
review=Path('/tmp/modules-landscape-original14-independent-readonly-review19-v1.json')
assert H(review)=='913d516c37fbf627cf930713b03f0a8366425000248589fd88ebaa497ee3cc11'
d=dict(schema_version=1,status='read_only_narrow_paragraph_proposal_not_applied',hold='HOLD33 ACTIVE. TMP only. No live source, inventory, ledger, index, selection or offer write.',correction_index_proposed=None,
prepared_by='/root/modules_resume',prepared_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source=source,source_line=710,physical_material_key='landscape.html::node-1336',source_sha256_before=BH(old),proposed_source_sha256_after=BH(new),source_bytes_before_snapshot=prefix+'-source-before.html',source_bytes_before_snapshot_sha256=BH(old),source_bytes_proposed_after_snapshot=prefix+'-source-proposed-after.html',source_bytes_proposed_after_snapshot_sha256=BH(new),inventory_at_preparation=str(ip.relative_to(R)),inventory_sha256_at_preparation=H(ip),immutable_original_review=dict(path=str(review),sha256=H(review),unchanged=True),exercise_key='landscape.html::exercise-18',replacements=[dict(before=before,after=after,count=1,reason='Five precise SafeOpt Answer paragraph710 wording/attribution qualifications; original three scopes and their independent review remain unchanged.')],precise_subspan_replacements=[dict(before=a,after=b,reason=c) for a,b,c in spans],affected_physical_material_units=[x for x in details if '::node-' in x['key']],affected_exercises=[x for x in details if '::exercise-' in x['key']],expected_changed_text_keys=delta['exercises']+delta['material_source_units'],full_temporary_inventory_parser=dict(actual_command=['python3','/tmp/modules-landscape-safeopt-paragraph-precision-v2-proposal19.py'],generator_completed=True,simulated_inventory=str(np),simulated_inventory_sha256=H(np),counts=N['counts'],actual_delta=delta,all_keys_lines_locators_tags_attributes_order_and_other_fields_unchanged=True,html_structure_node_count=len(A.nodes)),actual_proof_source_sha256=proofs,actual_standalone_evidence=evidence,primary_attribution=primary_evidence,proof_declarations=['SafeLearning.CompleteModulesLandscapeUnsafeSeeds.actual_mixed_seed_contains_an_unsafe_point_but_the_first_query_is_safe','SafeLearning.CompleteModulesLandscapeUnsafeSeeds.actual_source_seed_initialization_has_exact_endpoints_and_admits_both_candidates','SafeLearning.CompleteModulesLandscapeUnsafeSeeds.actual_unique_maximum_width_first_query_can_avoid_the_unsafe_seed_point','SafeLearning.CompleteModulesLandscapeUnsafeSeeds.actual_selected_unsafe_seed_is_unsafe_if_and_only_if_the_first_selected_value_is_unsafe','SafeLearning.CompleteModulesLandscapeUnsafeSeeds.actual_underestimated_RKHS_norm_bound_does_not_force_an_unsafe_query'],preservation_check=dict(frozen_manifest=str(cm.relative_to(R)),frozen_manifest_sha256=H(cm),selected_proofs=490,selected_source_evidence_paths=565,frozen_inputs=2431,all_hashes_exact=True,all_live_safelearning_source_and_asset_count=len(assets_before),all_live_safelearning_sources_and_assets_sha256=assets_before),limits=['Narrow wording/attribution proposal only; no whole exercise or material-unit promotion.','Generic GP/RKHS concentration and all-time SafeOpt probability remain pending; supplied confidence assumptions are not relabeled a concentration proof.','The CBF answer paragraph711, summary713 and prior independent review decisions/times are unchanged.','ModelError is linked as separate unchanged contextual evidence; it does not support any extra correction in this proposal.','Independent full parser/semantic review and authorized source application remain separate from this TMP-only preparation.'])
prior=Path('/tmp/modules-landscape-safeopt-paragraph-precision19-proposal.json')
prior_review=Path('/tmp/modules-landscape-safeopt-paragraph-independent-proposal-review19-v1.json')
assert H(prior)=='30ac1e5953d59feda16beaa9d4c7f76ac606a66f92a8f513af685fa6cc18d6dd'
assert H(prior_review)=='54360089d88cdcc4314704dbe6a8d223e47c6d8a684032dd200d8fe92882f6ac'
pd=json.loads(prior.read_text())
d['schema_version']=2
d['additional_version_created_at_utc']=d['prepared_at_utc']
d['prepared_at_utc']=pd['prepared_at_utc']
d['transparent_prior_proposal_and_review']={'proposal':str(prior),'proposal_sha256':H(prior),'original_preparation_time_preserved':pd['prepared_at_utc'],'independent_review':str(prior_review),'independent_review_sha256':H(prior_review),'original_bytes_and_decisions_unchanged':True,'version_delta':'Two additional qualifications only: contextual unknown-function difficulty and modal too-small-L failure. Exact original three proposed replacement scopes retained.'}
d['proof_declarations'] += [
 'SafeLearning.CompleteModulesLandscapeKnownBounds.actual_known_linear_RKHS_coefficient_has_an_exact_squared_norm_bound',
 'SafeLearning.CompleteModulesLandscapeKnownBounds.actual_known_linear_RKHS_function_has_the_exact_least_global_Lipschitz_constant',
 'SafeLearning.CompleteModulesLandscapeKnownBounds.actual_underestimated_Lipschitz_constant_can_still_certify_only_safe_points',
 'SafeLearning.CompleteModulesLandscapeKnownBounds.actual_safe_positive_design_keeps_every_query_safe_even_under_wrong_bounds']
p=Path(prefix+'-proposal.json')
with p.open('x') as f:json.dump(d,f,indent=2,ensure_ascii=False);f.write('\n')
assert (R/source).read_bytes()==old and H(ip)==d['inventory_sha256_at_preparation']
assert assets_before=={str(p.relative_to(R)):H(p) for p in asset_paths}
print(json.dumps(dict(path=str(p),sha256=H(p),delta=delta,proposed_source_sha256_after=BH(new),protected_selected=490,protected_paths=565,frozen_inputs=2431,all_live_sources_assets_unchanged=len(assets_before)),indent=2))

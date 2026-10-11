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
before=re.search(r'<p><strong>ZCBF</strong>.*?</p>',old.decode()).group()
spans=[
 ("where either $D$ is an open neighbourhood of $C$ or $0$ is a regular value of $h$", "where $D$ is an open ambient neighbourhood of $C$ for the stated locally Lipschitz closed loop; for a boundary-only check, $0$ must additionally be a regular value of $h$", "State the ambient local Lipschitz domain explicitly for both the full-domain barrier and the boundary-only Nagumo route. Regularity of the defining function alone cannot replace ambient dynamics regularity when only relative Lipschitz data on a closed D are supplied.")
]
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
sim=Path('/tmp/modules-landscape-cbf-ambient-domain-proposal19-simulation');sim.mkdir(exist_ok=False)
(sim/'SafeLearning').mkdir()
for p in (R/'SafeLearning').glob('*.html'):shutil.copyfile(p,sim/'SafeLearning'/p.name)
(sim/source).write_bytes(new)
spec=importlib.util.spec_from_file_location('landscape_cbf_ambient_inventory19',R/'book/inventory_claims.py')
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
assert delta=={'exercises':['landscape.html::exercise-18'],'material_source_units':['landscape.html::node-1338']}
proofs={};evidence=[]
specs=[]
for p,scope in [
 ('book/coverage/checks/modules-landscape-regular-boundary-domain-countermodel19-trial4-standalone.json','Actual closed-domain relative Lipschitz/C1 regular barrier/full on-D alpha=id inequality plus a true escaping ODE path shows why ambient regularity must be stated.'),
 ('book/coverage/checks/modules-landscape-regular-boundary-local19-trial2-standalone.json','Uniform true Picard perturbations and Gronwall derive genuine weak regular-boundary local safety on an open ambient domain.'),
 ('book/coverage/checks/modules-landscape-regular-boundary-invariance19-trial3-standalone.json','True boundary-only invariance for every existing path and compact global existence under explicit open ambient local-Lipschitz/C1 hypotheses.')]:
 j=json.loads((R/p).read_text());specs.append((p,H(R/p),j['files'][0]['sha256'],scope))
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
primary_evidence={'scope':'Exact full original Exercise1.4 read. The direct independently checked 2017/2019 primary ambient ODE-domain excerpts are retained in the separate new boundary review, rather than silently extending a relative closed-domain theorem.'}
prefix='/tmp/modules-landscape-cbf-ambient-domain19'
for suffix,b in [('-source-before.html',old),('-source-proposed-after.html',new)]:
 p=Path(prefix+suffix)
 with p.open('xb') as f:f.write(b)
review=Path('/tmp/modules-landscape-original14-independent-readonly-review19-v1.json')
assert H(review)=='913d516c37fbf627cf930713b03f0a8366425000248589fd88ebaa497ee3cc11'
d=dict(schema_version=1,status='read_only_narrow_paragraph_proposal_not_applied',hold='HOLD33 ACTIVE. TMP only. No live source, inventory, ledger, index, selection or offer write.',correction_index_proposed=None,
prepared_by='/root/modules_resume',prepared_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source=source,source_line=711,physical_material_key='landscape.html::node-1338',source_sha256_before=BH(old),proposed_source_sha256_after=BH(new),source_bytes_before_snapshot=prefix+'-source-before.html',source_bytes_before_snapshot_sha256=BH(old),source_bytes_proposed_after_snapshot=prefix+'-source-proposed-after.html',source_bytes_proposed_after_snapshot_sha256=BH(new),inventory_at_preparation=str(ip.relative_to(R)),inventory_sha256_at_preparation=H(ip),immutable_original_review=dict(path=str(review),sha256=H(review),unchanged=True),exercise_key='landscape.html::exercise-18',replacements=[dict(before=before,after=after,count=1,reason='One precise ambient-domain qualification in paragraph711; paragraph710, summary713 and all other source bytes stay unchanged.')],precise_subspan_replacements=[dict(before=a,after=b,reason=c) for a,b,c in spans],affected_physical_material_units=[x for x in details if '::node-' in x['key']],affected_exercises=[x for x in details if '::exercise-' in x['key']],expected_changed_text_keys=delta['exercises']+delta['material_source_units'],full_temporary_inventory_parser=dict(actual_command=['python3','/tmp/modules-landscape-cbf-ambient-domain-proposal19.py'],generator_completed=True,simulated_inventory=str(np),simulated_inventory_sha256=H(np),counts=N['counts'],actual_delta=delta,all_keys_lines_locators_tags_attributes_order_and_other_fields_unchanged=True,html_structure_node_count=len(A.nodes)),actual_proof_source_sha256=proofs,actual_standalone_evidence=evidence,primary_attribution=primary_evidence,proof_declarations=['SafeLearning.CompleteModulesLandscapeRegularBoundaryDomainCountermodel.actual_closed_domain_relative_Lipschitz_regular_barrier_has_an_escaping_true_solution','SafeLearning.CompleteModulesLandscapeRegularBoundaryLocal.actual_regular_boundary_only_inward_condition_gives_local_safety_of_an_existing_path','SafeLearning.CompleteModulesLandscapeRegularBoundaryInvariance.actual_regular_boundary_only_inward_condition_keeps_every_existing_path_safe','SafeLearning.CompleteModulesLandscapeRegularBoundaryInvariance.actual_compact_regular_superlevel_set_with_boundary_only_inwardness_has_global_solutions'],preservation_check=dict(frozen_manifest=str(cm.relative_to(R)),frozen_manifest_sha256=H(cm),selected_proofs=490,selected_source_evidence_paths=565,frozen_inputs=2431,all_hashes_exact=True,all_live_safelearning_source_and_asset_count=len(assets_before),all_live_safelearning_sources_and_assets_sha256=assets_before),limits=['Narrow wording/attribution proposal only; no whole exercise or material-unit promotion.','Generic GP/RKHS concentration and all-time SafeOpt probability remain pending; supplied confidence assumptions are not relabeled a concentration proof.','Only the identified paragraph711 ambient-domain phrase changes. SafeOpt710, summary713 and all other source bytes and prior decisions/times remain unchanged.','The regular-boundary theorem is approved only with open ambient regularity. The closed-domain relative-data countermodel does not refute a theorem which already assumes an ambient locally Lipschitz extension. No generic GP confidence or QP-regularity law is supplied.','Independent full parser/semantic review and authorized source application remain separate from this TMP-only preparation.'])
d['separate_prior_paragraph710_proposal']={'path':'/tmp/modules-landscape-safeopt-paragraph-precision-v2-19-proposal.json','sha256':H('/tmp/modules-landscape-safeopt-paragraph-precision-v2-19-proposal.json'),'independent_review':'/tmp/modules-landscape-safeopt-paragraph-independent-proposal-review19-v2.json','independent_review_sha256':H('/tmp/modules-landscape-safeopt-paragraph-independent-proposal-review19-v2.json'),'limits':'Historical separate unapplied paragraph710 proposal preserved unchanged. This summary-only proposal applies to the original live source33 and requires a refreshed read-only identity plan after any earlier serialized source edit.'}
p=Path(prefix+'-proposal.json')
with p.open('x') as f:json.dump(d,f,indent=2,ensure_ascii=False);f.write('\n')
assert (R/source).read_bytes()==old and H(ip)==d['inventory_sha256_at_preparation']
assert assets_before=={str(p.relative_to(R)):H(p) for p in asset_paths}
print(json.dumps(dict(path=str(p),sha256=H(p),delta=delta,proposed_source_sha256_after=BH(new),protected_selected=490,protected_paths=565,frozen_inputs=2431,all_live_sources_assets_unchanged=len(assets_before)),indent=2))

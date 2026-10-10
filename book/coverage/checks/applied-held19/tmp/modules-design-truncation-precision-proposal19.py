from pathlib import Path
import hashlib,json,re,datetime,sys,importlib.util,shutil
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();BH=lambda b:hashlib.sha256(b).hexdigest()
source='SafeLearning/lipschitz-by-design.html';old=(R/source).read_bytes();ip=R/'book/coverage/inventory-after-correction33.json';I=json.loads(ip.read_text());assert H(ip)=='c5edf43ad9e1b2d408b328fd331b2a52c624126dd167100541d5ca931986a963'
before=re.search(r'<p><strong>Step 2\.</strong> The skew-exponential remainder bound.*?</p>',old.decode()).group()
after=before.replace('0.2^3/6=0.00133333','0.2^3/6\\approx0.00133333').replace('$\\|S_2\\|_2\\le1.00133333$, a valid looser upper bound.','$\\|S_2\\|_2\\le1+0.2^3/6$. The rounded bound $\\|S_2\\|_2\\le1.00133333$ is also valid here by the exact norm in Step 1.')
assert before!=after and old.count(before.encode())==1
new=old.replace(before.encode(),after.encode(),1);assert new.replace(after.encode(),before.encode(),1)==old and old.count(b'\n')==new.count(b'\n')
sys.path.insert(0,str(R/'book'));from validate import Document
A,B=Document(old.decode()),Document(new.decode());assert len(A.nodes)==len(B.nodes) and all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line) for a,b in zip(A.nodes,B.nodes))
sim=Path('/tmp/modules-design-truncation-precision-proposal19-simulation');assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
for p in (R/'SafeLearning').glob('*.html'):shutil.copyfile(p,sim/'SafeLearning'/p.name)
(sim/source).write_bytes(new)
spec=importlib.util.spec_from_file_location('truncation19_inventory',R/'book/inventory_claims.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.ROOT=sim;m.OUT=sim/'book/coverage';m.inventory(); np=m.OUT/'inventory.json';N=json.loads(np.read_text());assert I['counts']==N['counts'];delta={};details=[]
for field in ['exercises','material_source_units']:
 a={u['key']:u for u in I[field]};b={u['key']:u for u in N[field]};assert a.keys()==b.keys();delta[field]=[]
 for k,u in a.items():
  v=b[k];assert u.keys()==v.keys()
  for f in u:
   if f not in ['source_sha256','source_text','text_sha256']:assert u[f]==v[f],(k,f)
  if u['source_text']!=v['source_text']:
   delta[field].append(k)
   details.append(dict(key=k,line=u['line'],locator=u['locator'],text_sha256_before=u['text_sha256'],text_sha256_proposed_after=v['text_sha256']))
  else:assert u['text_sha256']==v['text_sha256']
  if u['source']!=source:assert u==v
assert delta=={'exercises':['lipschitz-by-design.html#practice-hard-3'],'material_source_units':['lipschitz-by-design.html::node-1293']}
proofs={};ev=[]
for p in ['book/coverage/checks/modules-design-truncation19-trial3-standalone.json','book/coverage/checks/modules-design-truncation-consequences19-trial3-standalone.json']:
 q=R/p;j=json.loads(q.read_text());f=j['files'][0];assert f['exit_code']==0 and f['source_unchanged'];assert H(R/f['file'])==f['sha256'];assert H(R/f['log'])==f['log_sha256'];proofs[f['file']]=f['sha256'];ev.append(dict(compiler_manifest=p,compiler_manifest_sha256=H(q),raw_execution_record=f))
cm=R/'reports/full-coverage/checkpoint-18-manifest.json';C=json.loads(cm.read_text());paths={}
for p,row in C['proof_files'].items():
 paths[p]=row['sha256'];assert H(R/p)==row['sha256']
 for p,s in row['evidence_sha256'].items():paths[p]=s;assert H(R/p)==s
for p,s in C['frozen_inputs_sha256'].items():assert H(R/C['snapshot']/p)==s
assert len(C['proof_files'])==490 and len(paths)==565 and len(C['frozen_inputs_sha256'])==2431
prefix='/tmp/modules-design-truncation-precision19'
for suffix,b in [('-source-before.html',old),('-source-proposed-after.html',new)]:p=Path(prefix+suffix);assert not p.exists();p.write_bytes(b)
prepared=datetime.datetime.now(datetime.timezone.utc).isoformat();d=dict(schema_version=1,status='read_only_narrow_precision_proposal_not_applied',correction_index_proposed=None,prepared_by='/root/modules_resume',prepared_at_utc=prepared,source=source,source_sha256_before=BH(old),proposed_source_sha256_after=BH(new),source_bytes_before_snapshot=prefix+'-source-before.html',source_bytes_before_snapshot_sha256=BH(old),source_bytes_proposed_after_snapshot=prefix+'-source-proposed-after.html',source_bytes_proposed_after_snapshot_sha256=BH(new),inventory_at_preparation=str(ip.relative_to(R)),inventory_sha256_at_preparation=H(ip),exercise_key=delta['exercises'][0],replacements=[dict(before=before,after=after,count=1,reason='Exact rational0.2^3/6=1/750 is strictly above finite decimal.00133333, though nearest8-place rounding is genuine. The orthogonal-exponential triangle route gives exact layer bound1+1/750; the slightly smaller rounded bound1.00133333 is valid for this actual S2 by its separately proved exact norm, rather than by rounding an upper bound downward.')],affected_physical_material_units=[x for x in details if '::node-' in x['key']],affected_exercises=[x for x in details if '#practice-' in x['key']],expected_changed_text_keys=delta['exercises']+delta['material_source_units'],full_temporary_inventory_parser=dict(actual_command=['python3','/tmp/modules-design-truncation-precision-proposal19.py'],generator_completed=True,simulated_inventory=str(np),simulated_inventory_sha256=H(np),counts=N['counts'],actual_delta=delta,all_keys_lines_locators_tags_attributes_order_and_other_fields_unchanged=True),actual_proof_source_sha256=proofs,actual_standalone_evidence=ev,proof_declarations=['SafeLearning.CompleteModulesDesignTruncation.actual_source_matrix_exponential_remainder_is_below_the_literal_rational_bound','SafeLearning.CompleteModulesDesignTruncation.actual_source_exponential_is_orthogonal_and_has_norm_one','SafeLearning.CompleteModulesDesignTruncation.actual_source_remainder_bound_gives_the_looser_layer_bound','SafeLearning.CompleteModulesDesignTruncationConsequences.actual_rational_remainder_has_the_printed_rounding_and_is_not_equal'],hypotheses=['The exact source2x2real skew K, actual L2 operator norm and true NormedSpace.exp.','Finite approximation tolerance is strictly half the last8-place decimal unit.','Question/hint/Step1/Step3/depth bounds/activations remain byte-for-byte unchanged.'],preservation_check=dict(frozen_manifest=str(cm.relative_to(R)),frozen_manifest_sha256=H(cm),selected_proofs=490,selected_source_evidence_paths=565,frozen_inputs=2431,all_hashes_exact=True),limits=['TMP-only under HOLD33; no live source/inventory/coverage/index mutation.','No independent semantic approval/serial/root authorization inferred; source application and fresh whole review remain separate.','Both actual passing sources/compiler/logs and every failed trial/snapshot remain immutable.'])
p=Path(prefix+'-proposal.json');assert not p.exists();p.write_text(json.dumps(d,indent=2)+'\n');assert (R/source).read_bytes()==old and H(ip)==d['inventory_sha256_at_preparation'];print(json.dumps(dict(path=str(p),sha256=H(p),delta=delta),indent=2))

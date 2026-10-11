from pathlib import Path
import hashlib,json,re,datetime,sys,importlib.util,shutil
R=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
BH=lambda b:hashlib.sha256(b).hexdigest()
source='SafeLearning/landscape.html';old=(R/source).read_bytes()
ip=R/'book/coverage/inventory-after-correction33.json';I=json.loads(ip.read_text())
assert H(ip)=='c5edf43ad9e1b2d408b328fd331b2a52c624126dd167100541d5ca931986a963'
before=next(line for line in old.decode().splitlines() if 'Only at $k=1$' in line)
after=before.replace('Only at $k=1$',r'With $\sigma\gt0$, only at $k=1$',1).replace('States within one episode are dependent, because each state contains all past noise.','States within one episode can be dependent because later states carry earlier noise.',1)
assert before!=after and old.count(before.encode())==1
new=old.replace(before.encode(),after.encode(),1)
assert new.replace(after.encode(),before.encode(),1)==old and old.count(b'\n')==new.count(b'\n')
sys.path.insert(0,str(R/'book'));from validate import Document
A,B=Document(old.decode()),Document(new.decode())
assert len(A.nodes)==len(B.nodes) and all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line) for a,b in zip(A.nodes,B.nodes))
sim=Path('/tmp/modules-landscape-independence-positive-noise-v2-modal-proposal19-simulation');assert not sim.exists()
(sim/'SafeLearning').mkdir(parents=True)
for p in (R/'SafeLearning').glob('*.html'):shutil.copyfile(p,sim/'SafeLearning'/p.name)
(sim/source).write_bytes(new)
spec=importlib.util.spec_from_file_location('landscape_independence_noise19_inventory',R/'book/inventory_claims.py')
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
   delta[field].append(k)
   details.append(dict(key=k,line=u['line'],locator=u['locator'],text_sha256_before=u['text_sha256'],text_sha256_proposed_after=v['text_sha256']))
  else:assert u['text_sha256']==v['text_sha256']
  if u['source']!=source:assert u==v
assert delta=={'exercises':[],'material_source_units':['landscape.html::node-962']}
proofs={};ev=[]
for p in ['book/coverage/checks/modules-landscape-independent-states19-trial4-standalone.json']:
 q=R/p;j=json.loads(q.read_text());f=j['files'][0]
 assert f['exit_code']==0 and f['source_unchanged']
 assert H(R/f['file'])==f['sha256'] and H(R/f['log'])==f['log_sha256']
 proofs[f['file']]=f['sha256'];ev.append(dict(compiler_manifest=p,compiler_manifest_sha256=H(q),raw_execution_record=f))
cm=R/'reports/full-coverage/checkpoint-18-manifest.json';C=json.loads(cm.read_text());paths={}
for p,row in C['proof_files'].items():
 paths[p]=row['sha256'];assert H(R/p)==row['sha256']
 for p,s in row['evidence_sha256'].items():paths[p]=s;assert H(R/p)==s
for p,s in C['frozen_inputs_sha256'].items():assert H(R/C['snapshot']/p)==s
assert len(C['proof_files'])==490 and len(paths)==565 and len(C['frozen_inputs_sha256'])==2431
prefix='/tmp/modules-landscape-independence-positive-noise-v2-modal19'
for suffix,b in [('-source-before.html',old),('-source-proposed-after.html',new)]:
 p=Path(prefix+suffix);assert not p.exists();p.write_bytes(b)
d=dict(schema_version=2,status='read_only_narrow_domain_qualification_proposal_not_applied',correction_index_proposed=None,
 prepared_by='/root/modules_resume',prepared_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 source=source,source_sha256_before=BH(old),proposed_source_sha256_after=BH(new),
 source_bytes_before_snapshot=prefix+'-source-before.html',source_bytes_before_snapshot_sha256=BH(old),
 source_bytes_proposed_after_snapshot=prefix+'-source-proposed-after.html',source_bytes_proposed_after_snapshot_sha256=BH(new),
 inventory_at_preparation=str(ip.relative_to(R)),inventory_sha256_at_preparation=H(ip),
 exercise_key=None,replacements=[dict(before=before,after=after,count=1,
 reason='For nonzero Gaussian noise and at least two positive-time states, actual covariance proves dependence whenever k differs from1; k1 genuinely yields independent states and the exact finite-horizon product probability. At sigma0 every state is deterministic, so even k not1 gives independent states. The original only-at phrase therefore needs positive noise, consistent with the explorer nonnegative sigma domain. Qualify both the categorical dependence sentence and only-at phrase; retain the subsequent sigma0/invariance paragraph and every numerical/example clause.')],
 affected_physical_material_units=[x for x in details if '::node-' in x['key']],
 affected_exercises=[x for x in details if '::exercise-' in x['key']],
 expected_changed_text_keys=delta['exercises']+delta['material_source_units'],
 full_temporary_inventory_parser=dict(actual_command=['python3','/tmp/modules-landscape-independence-positive-noise-v2-modal-proposal19.py'],
 generator_completed=True,simulated_inventory=str(np),simulated_inventory_sha256=H(np),counts=N['counts'],actual_delta=delta,
 all_keys_lines_locators_tags_attributes_order_and_other_fields_unchanged=True),
 actual_proof_source_sha256=proofs,actual_standalone_evidence=ev,
 proof_declarations=['SafeLearning.CompleteModulesLandscapeIndependentStates.actual_gain_one_replaces_every_positive_time_state_by_the_fresh_noise',
 'SafeLearning.CompleteModulesLandscapeIndependentStates.actual_gain_one_positive_time_states_are_jointly_independent',
 'SafeLearning.CompleteModulesLandscapeIndependentStates.actual_gain_one_joint_violation_probability_has_the_source_product_formula',
 'SafeLearning.CompleteModulesLandscapeIndependentStates.actual_nonzero_noise_and_gain_not_one_make_the_first_two_states_dependent',
 'SafeLearning.CompleteModulesLandscapeIndependentStates.actual_zero_noise_makes_the_first_two_states_independent_at_every_gain'],
 hypotheses=['The source explorer uses nonnegative sigma and a horizon slider of at least5, so sigma>0 and at least two positive-time states give exact necessary/sufficient gain1 independence.',
 'This is a statement about the stated independent Gaussian noise model, not a claim that a finite deterministic PRNG trace is literally an independent Gaussian law.',
 'The sigma0 deterministic exception is proved directly using actual source recurrence, not merely absence of a covariance premise.'],
 preservation_check=dict(frozen_manifest=str(cm.relative_to(R)),frozen_manifest_sha256=H(cm),selected_proofs=490,
 selected_source_evidence_paths=565,frozen_inputs=2431,all_hashes_exact=True),
 limits=['TMP-only under HOLD33; no live source/inventory/coverage/index mutation.',
 'Independent semantic approval, root serialization, source application and a fresh whole review remain separate gates.',
 'The original source review decisions/times and actual compiler logs, including genuine warnings and failed trial histories, remain immutable.',
 'This qualifies only the dependence and necessary gain1 independence statements; every exercise and all other paragraph text remain unchanged.'])
prior=Path('/tmp/modules-landscape-independence-positive-noise19-proposal.json')
assert prior.exists()
d['transparent_prior_proposal_preserved']={'path':str(prior),'sha256':H(prior),'original_preparation_time':json.loads(prior.read_text())['prepared_at_utc'],'reason':'Original V1 qualified only the only-at sentence. Independent full literal reading also found the preceding categorical dependence claim overstates initial,zero-noise and gain1 exceptions. This fresh V2 separately simulates the same paragraph with both narrow qualifications; original V1 snapshots/parser/time and all proof bytes preserved.','new_source_substitution':True,'status':'Both versions unapplied/unindexed under HOLD33.'}
p=Path(prefix+'-proposal.json');assert not p.exists();p.write_text(json.dumps(d,indent=2)+'\n')
assert (R/source).read_bytes()==old and H(ip)==d['inventory_sha256_at_preparation']
print(json.dumps(dict(path=str(p),sha256=H(p),delta=delta),indent=2))

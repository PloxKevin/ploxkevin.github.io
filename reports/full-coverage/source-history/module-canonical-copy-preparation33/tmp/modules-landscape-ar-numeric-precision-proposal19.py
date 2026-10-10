from pathlib import Path
import hashlib,json,re,datetime,sys,importlib.util,shutil
R=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
BH=lambda b:hashlib.sha256(b).hexdigest()
source='SafeLearning/landscape.html';old=(R/source).read_bytes()
ip=R/'book/coverage/inventory-after-correction33.json';I=json.loads(ip.read_text())
assert H(ip)=='c5edf43ad9e1b2d408b328fd331b2a52c624126dd167100541d5ca931986a963'
before=next(line for line in old.decode().splitlines() if r'\sigma_\infty=0.1155' in line)
after=r'            <p>(iii) $\sigma_\infty^2=0.01/0.75$, $\sigma_\infty=\sqrt{0.01/0.75}\approx0.1155$, so the stationary per-step violation probability is $p_\infty=1-\Phi(0.2/\sqrt{0.01/0.75})=1-\Phi(\sqrt3)\approx0.0416$ ($\sqrt3\approx1.732$). The transient is short: $p_1\approx0$ ($m_1=0.4$, $\sqrt{v_1}=0.1$, six standard deviations away), $p_3\approx0.0044$, $p_5\approx0.0256$, $p_{10}\approx0.0410$. Summing the exact terms gives $\mathbb E[N]\approx1.484$, slightly below the stationary approximation $Tp_\infty\approx1.665$. The Markov bound $\mathbb P(\exists t:x_t\gt1)\le\mathbb E[N]\lt1.485$ is vacuous; the explorer (set $\sigma=0.1$) estimates the actual joint probability, about $0.69$ in a large simulation, which individual marginal probabilities alone do not determine. This is the quantitative face of Exercise 1.3: the CMDP number is analytic and cheap, the chance-constraint number needs the joint law.</p>' 
assert before!=after and old.count(before.encode())==1
new=old.replace(before.encode(),after.encode(),1)
assert new.replace(after.encode(),before.encode(),1)==old and old.count(b'\n')==new.count(b'\n')
sys.path.insert(0,str(R/'book'));from validate import Document
A,B=Document(old.decode()),Document(new.decode())
assert len(A.nodes)==len(B.nodes) and all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line) for a,b in zip(A.nodes,B.nodes))
sim=Path('/tmp/modules-landscape-ar-numeric-precision-proposal19-simulation');assert not sim.exists()
(sim/'SafeLearning').mkdir(parents=True)
for p in (R/'SafeLearning').glob('*.html'):shutil.copyfile(p,sim/'SafeLearning'/p.name)
(sim/source).write_bytes(new)
spec=importlib.util.spec_from_file_location('landscape_ar_numeric19_inventory',R/'book/inventory_claims.py')
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
assert delta=={'exercises':['landscape.html::exercise-19'],'material_source_units':['landscape.html::node-1368']}
proofs={};ev=[]
for p in ['book/coverage/checks/modules-gaussian-tail-numerical-bounds19-trial1-standalone.json', 'book/coverage/checks/modules-landscape-ar-tail-table19-trial2-standalone.json', 'book/coverage/checks/modules-landscape-ar-count-numerics19-trial2-standalone.json', 'book/coverage/checks/modules-landscape-ar-stationary-numerics19-trial3-standalone.json']:
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
prefix='/tmp/modules-landscape-ar-numeric-precision19'
for suffix,b in [('-source-before.html',old),('-source-proposed-after.html',new)]:
 p=Path(prefix+suffix);assert not p.exists();p.write_bytes(b)
d=dict(schema_version=1,status='read_only_narrow_numerical_precision_proposal_not_applied',correction_index_proposed=None,
 prepared_by='/root/modules_resume',prepared_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 source=source,source_sha256_before=BH(old),proposed_source_sha256_after=BH(new),
 source_bytes_before_snapshot=prefix+'-source-before.html',source_bytes_before_snapshot_sha256=BH(old),
 source_bytes_proposed_after_snapshot=prefix+'-source-proposed-after.html',source_bytes_proposed_after_snapshot_sha256=BH(new),
 inventory_at_preparation=str(ip.relative_to(R)),inventory_sha256_at_preparation=H(ip),
 exercise_key=delta['exercises'][0],replacements=[dict(before=before,after=after,count=1,
 reason='Actual standalone Lean bounds certify every printed stationary and transient decimal as rounding, and disprove the former exact equalities. Keep the true unrounded stationary standard deviation inside the Gaussian CDF: substituting .1155 changes the last tail digit. The actual source integral expectation lies strictly between1.48415 and1.484355, so the Markov bound uses the genuine expectation and an upward1.485 bound rather than a rounded-down exact1.484 threshold. All other text and the independently reproduced finite explorer observation are preserved.')],
 affected_physical_material_units=[x for x in details if '::node-' in x['key']],
 affected_exercises=[x for x in details if '::exercise-' in x['key']],
 expected_changed_text_keys=delta['exercises']+delta['material_source_units'],
 full_temporary_inventory_parser=dict(actual_command=['python3','/tmp/modules-landscape-ar-numeric-precision-proposal19.py'],
 generator_completed=True,simulated_inventory=str(np),simulated_inventory_sha256=H(np),counts=N['counts'],actual_delta=delta,
 all_keys_lines_locators_tags_attributes_order_and_other_fields_unchanged=True),
 actual_proof_source_sha256=proofs,actual_standalone_evidence=ev,
 proof_declarations=['SafeLearning.CompleteModulesLandscapeARStationaryNumerics.actual_source_stationary_variance_is_one_over_seventy_five',
 'SafeLearning.CompleteModulesLandscapeARStationaryNumerics.actual_source_stationary_sd_has_the_printed_four_decimal_rounding',
 'SafeLearning.CompleteModulesLandscapeARStationaryNumerics.actual_source_stationary_standardized_threshold_has_the_printed_three_decimal_rounding',
 'SafeLearning.CompleteModulesLandscapeARStationaryNumerics.actual_source_stationary_tail_has_the_printed_four_decimal_rounding',
 'SafeLearning.CompleteModulesLandscapeARStationaryNumerics.actual_forty_times_stationary_tail_has_the_printed_three_decimal_rounding',
 'SafeLearning.CompleteModulesLandscapeARCountNumerics.actual_expected_forty_step_count_has_a_true_enclosure_and_three_decimal_rounding',
 'SafeLearning.CompleteModulesLandscapeARCountNumerics.actual_source_integral_count_is_exactly_the_verified_forty_step_tail_sum',
 'SafeLearning.CompleteModulesLandscapeARCountNumerics.actual_three_source_transient_probabilities_have_four_decimal_roundings',
 'SafeLearning.CompleteModulesLandscapeARCountNumerics.actual_markov_bound_is_vacuous_because_the_true_expectation_exceeds_one'],
 hypotheses=['Literal original exercise parameters k=.5, sigma=.1, goal=.8, boundary1 and horizon40 with genuinely independent standard Gaussian noise.',
 'Stationary40p is explicitly an approximation to the transient expectation, not an equality of them.',
 'Every rounding is certified by true analytic Gaussian polynomial error, exact rational bounds and actual kernel computation, without floating point values assumed as real hypotheses.'],
 preservation_check=dict(frozen_manifest=str(cm.relative_to(R)),frozen_manifest_sha256=H(cm),selected_proofs=490,
 selected_source_evidence_paths=565,frozen_inputs=2431,all_hashes_exact=True),
 limits=['TMP-only under HOLD33; no live source/inventory/coverage/index mutation.',
 'Independent semantic approval, root serialization, source application and a fresh whole review remain separate gates.',
 'The original source review decisions/times and actual compiler logs, including genuine warnings and failed trial histories, remain immutable.',
 'This corrects only exact-decimal substitutions and the printed rounded Markov threshold; true variance, transient marginal sum, finite empirical observation and all other source clauses remain unchanged.'])
p=Path(prefix+'-proposal.json');assert not p.exists();p.write_text(json.dumps(d,indent=2)+'\n')
assert (R/source).read_bytes()==old and H(ip)==d['inventory_sha256_at_preparation']
print(json.dumps(dict(path=str(p),sha256=H(p),delta=delta),indent=2))

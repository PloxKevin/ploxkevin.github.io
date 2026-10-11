from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());ref=lambda p:{'file':str(p),'sha256':H(p)}
request=Path('/tmp/modules-verification-smoothing37-full-literal-independent-review-request26-v1.json');assert H(request)=='9e858fcf3375826a1273b62279c94b3db14a0f9ca5e446d37d278de70d130a3c';d=read(request)
for k in ['source','current_inventory','actual_TMP_standalone_record','actual_raw_log','actual_source_snapshot','actual_runner','original_author_gap_audit']:
 r=d[k];assert H(r['file'])==r['sha256'],k
source=Path(d['source']['file']).read_text();assert source==d['entire_source_body'];assert source==Path(d['actual_source_snapshot']['file']).read_text()
assert not re.search(r'\b(sorry|admit)\b',source)
namespace='';parsed=[]
for line in source.splitlines():
 m=re.match(r'namespace\s+(\S+)',line)
 if m:namespace=m[1]
 m=re.match(r'theorem\s+(\w+)',line)
 if m:parsed.append(namespace+'.'+m[1])
assert parsed==d['public_theorems'] and len(parsed)==d['public_theorem_count']==37
act=read(d['actual_TMP_standalone_record']['file']);assert act==d['entire_actual_TMP_record'];assert type(act['actual_exit_code'])is int and act['actual_exit_code']==0;assert type(act['actual_runner_exit_code'])is int and act['actual_runner_exit_code']==0
assert act['source_sha256_before']==act['source_sha256_after']==d['source']['sha256'] and act['source_unchanged']is True
assert H(act['raw_log'])==act['raw_log_sha256'];assert Path(act['raw_log']).read_text()==d['actual_raw_log_body'];assert len(re.findall(r'^.*\.lean:\d+:\d+: warning:',d['actual_raw_log_body'],re.M))==5
assert act['actual_command']==['lake','env','lean',d['source']['file']] and act['actual_workdir']==str(ROOT/'verification/lean')
for r in d['original_trial_and_source_byte_inputs']:assert H(r['file'])==r['sha256'] and Path(r['file']).stat().st_size==r['size_bytes']
inventory=read(d['current_inventory']['file']);assert [r for r in inventory['exercises'] if r['key']==d['entire_exercise_record']['key']]==[d['entire_exercise_record']]
bykey={r['key']:r for r in inventory['material_source_units']}
for r in d['entire_physical_unit_records']:assert bykey[r['key']]==r
page=ROOT/'SafeLearning/verification.html';assert H(page)==d['entire_exercise_record']['source_sha256'];assert d['entire_local_section_definition_theorem_np_proof_and_certify_algorithm']in page.read_text()
selection=read(ROOT/'reports/full-coverage/checkpoint-25-selection.json');assert selection['proof_file_count']==len(selection['proof_files'])==1156
for n,r in selection['proof_files'].items():assert H(ROOT/n)==r['sha256'],n
for n,h in inventory['source_sha256'].items():assert H(ROOT/n)==h
assert len(inventory['source_sha256'])==29
for n,h in act['installed25_owner_sha256'].items():assert H(ROOT/n)==h
for r in d['selected_exact_evidence_and_full_sources_read']:
 assert H(r['source']['file'])==r['source']['sha256'];assert Path(r['source']['file']).read_text()==r['source_body']
 for ev in r['checked_evidence']:assert H(ROOT/ev['file'])==ev['sha256']
assert len(d['selected_exact_evidence_and_full_sources_read'])==5
base=parsed[:11];nd=parsed[11:24];numeric=parsed[24:31];tail=parsed[31:]
components=[
 {'group':'true likelihood-ratio and scalar Gaussian transfer','lean_declarations':base,'reason':'Signed pointwise NP inequalities are integrated against genuine densities; Gaussian translation and low-halfspace mass are actual laws. Strict majority and deterministic winner are derived; confidence event is supplied by the exercise premise, never inferred from an observed returned statistic.'},
 {'group':'true finite-dimensional Gaussian decomposition and event-transfer','lean_declarations':nd,'reason':'Actual Gaussian dual covariance implies independent unit projection and orthogonal residual; genuine product law and reconstruction yield fiber/Fubini translation. Normalized perturbation in arbitrary direction derives strict majority for every Euclidean-ball perturbation. Class events are measurable and disjoint, deriving deterministic unique winner and a measurable sampling good-event.'},
 {'group':'literal quantile, rounding, abstention and norm conversion','lean_declarations':numeric,'reason':'Actual sInf threshold inversion at every CDF value proves Phi2 inverse2/Phi0=.5/zero quantile. Certified Taylor integrals prove nine-decimal rounding. The actual Option rule abstains at .5, and Fin100 pi/l2 conversion proves strict .1 radius; boundary vector reaches1.'},
 {'group':'actual variance-scaled noise and genuine coordinate/boundary models','lean_declarations':tail,'reason':'Every unit projection of sigma-scaled standardGaussian has actual sigma-squared Gaussian law. Actual halfspace Phi2 baseline/.5 shifted tie and WithLp2 norm correspondence close genuine ND noise and coordinate boundaries.'}]
for c in components:c.update(component_approved=True,missing_clauses=[],hypotheses=['Exact full theorem premises retained. Finite-dimensional real inner-product/Borel domain for ND noise; measurable deterministic classifier for winner exports; source-given confidence event with probability>=.999 and lower bound valid on that event.'])
gap='Linked Section4 explicitly also permits randomized base classifiers with an independent fixed internal law. The37 sources transfer arbitrary measurable bounded tests, but their exported ndIdealWinner/class probability correspondence and confidence conclusion use only deterministic E→Label. A separate normalized measurable class-probability/kernel winner and sampling-event bridge is needed for that inherited whole scope; no new binomial confidence premise is required.'
unit=[]
for r in d['entire_physical_unit_records']:
 k=r['key'];nf=k.endswith('1035');pending=k.endswith(('1034','1045','1049'))
 names=[] if nf else numeric if k.endswith('1041') else numeric+tail if k.endswith('1047') else parsed
 reason='Individual prerequisite navigation instruction has no mathematical assertion.' if nf else 'Complete literal arithmetic/norm or rule scope is covered by the exact reviewed declarations in the exercise parameter domain.' if not pending else 'All numeric, strict-radius, deterministic classifier and confidence-premise clauses are covered; inherited randomized classifier correspondence remains pending.'
 unit.append({'source_unit_key':k,'entire_inventory_record':r,'material_status':'non_formal' if nf else 'pending' if pending else 'proved','whole_unit_approved':not pending,'lean_declarations':names,'hypotheses':[] if nf else ['Source-given valid independent Monte-Carlo confidence procedure; confidence is over estimation samples.','sigma=.5, lower probability Phi2 or.5; strict perturbation inequalities; exact finite-label measurability and fixed independent internal-law scope retained.'],'per_unit_reason':reason,'components':[] if nf else components,'missing_clauses':[gap]if pending else []})
report={'status':'passed_independent_full37_body_components_with_precise_inherited_randomized_scope_gap','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Applied agent; Modules authored proof pack','request':ref(request),'entire_exercise_record':d['entire_exercise_record'],'whole_exercise_approved':False,'whole_exercise_status':'partial','components':components,'material_units':unit,'remaining_full_literal_bridges':[gap],'all37_complete_bodies_and_definitions_read':True,'proof_source':d['source'],'actual_TMP_standalone_record':d['actual_TMP_standalone_record'],'entire_original_actual_record':act,'actual_raw_log':d['actual_raw_log'],'actual_source_snapshot':d['actual_source_snapshot'],'original_author_gap_audit':d['original_author_gap_audit'],'entire_original_author_gap_audit_body_and_time':read(d['original_author_gap_audit']['file']),'original_trial_and_source_byte_inputs':d['original_trial_and_source_byte_inputs'],'selected_dependency_full_bodies':d['selected_exact_evidence_and_full_sources_read'],'primary_source':{'url':'https://proceedings.mlr.press/v97/cohen19c/cohen19c.pdf','scope':'Direct Theorem1, NP argument and Algorithm CERTIFY/Proposition2 read; source confidence event remains given, ideal classifier is certified, no observed-return conditional confidence is inferred.'},'protected_selected25_source_count':1156,'current52_source_pages_checked':29,'installed25_owner_count_checked':5,'scope':'Read-only complete37-body/literal/primary-scope component review. No compiler/named/canonical/selected/aggregate/live result inferred; new randomized-kernel supplement may close the precise whole gap. Current25 fixed.'}
out=Path('/tmp/modules-smoothing37-independent-applied-full-source-components-review26-v1.json');assert not out.exists();out.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'review':ref(out),'components':4,'all_bodies':37,'whole_exercise_approved':False,'whole_unit_approvals':3,'pending_mathematical_units':3}))

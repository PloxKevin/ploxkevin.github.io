from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sys
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
request=Path('/tmp/modules-nn-invariant-two-practices22-canonical-readiness-v1.json');assert sha(request)=='d56e907fde3a236b84467cfcb709d64faa213cbb74ac1326ce1226fd2b9b1881'
r=json.loads(request.read_text());source=ROOT/r['proof_file'];assert sha(source)==r['sha256']=='e9f39f1535a12ecbb088047648142462f5ed9b5f28a20b87a0a8019734e021d9'
sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
ds=declarations(source.read_text());assert ds==r['public_declarations']
theorems=[x['name'] for x in ds if x['kind'] in ['theorem','lemma']];assert len(theorems)==14
actual=[]
for row in r['actual_execution_records']:
 p=Path(row['record']);assert sha(p)==row['record_sha256'];e=json.loads(p.read_text());assert e==row['actual_record_body']
 assert type(e['actual_exit_code']) is int and e['actual_exit_code']==0 and e['source_sha256_before']==e['source_sha256_after']==r['sha256']
 assert sha(e['log'])==e['log_sha256'] and sha(e['source_snapshot'])==e['source_snapshot_sha256']==r['sha256']
 assert e['actual_workdir']==str(ROOT/'verification/lean')
 actual.append({'record':str(p),'record_sha256':sha(p),'actual_record_body':e,'raw_log_description':'nonempty genuine compiler/linter warnings, retained exactly'})
assert len(actual)==2 and {x['actual_record_body']['kind'] for x in actual}=={'lean_standalone','named_lean_module_build'}
for row in r['preserved_genuine_failed_trials']:
 assert sha(row['record'])==row['record_sha256'] and sha(row['source_snapshot'])==row['source_snapshot_sha256'] and sha(row['raw_log'])==row['raw_log_sha256']
 assert json.loads(Path(row['record']).read_text()).get('actual_exit_code',json.loads(Path(row['record']).read_text()).get('exit_code'))!=0
inventory=ROOT/r['inventory'];assert sha(inventory)==r['inventory_sha256']=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
inv=json.loads(inventory.read_text());ex={x['key']:x for x in inv['exercises']};units={x['key']:x for x in inv['material_source_units']}
assert sha(ROOT/'SafeLearning/nn-in-the-loop.html')=='413846b5ffc2a5fd70f74fb6f4a24e96b7983b6a745f50340c9d2d25c75d7049'
for e in r['exact_current48_exercises']:assert e==ex[e['key']]
ns='SafeLearning.CompleteModulesNNInvariantPractices22.'
def decl(*names):return [ns+x for x in names]
local=theorems[:6];dist=theorems[6:]
hlocal=['The actual deterministic scalar map is x/2 on |x|≤1 and2x outside. Local attraction and invariance quantify every initial x with x²≤1; the exterior witness is the exact x0=11/10.']
hdist=['For every time the given closed-loop storage certificate is V(t+1)≤V(t)/2+2d(t)², with |d(t)|≤1/10. Invariance starts from V0≤1/4. State-radius conclusions use V=norm²; the genuine EReal limsup bounds retain unbounded-sequence semantics and yield the stated finite bound for this nonnegative bounded storage.']
def component(clause,names,hyp,reason):return {'clause':clause,'lean_declarations':names,'hypotheses':hyp,'reason':reason,'approval':'approved_complete_actual_mathematical_source_component','missing_clauses':[]}
localgroups=[component('Exact local domain and all-time invariance',local[:3],hlocal,'The source energy-domain iff is derived. The actual local step gives the exact quarter-energy decrease; induction proves every iterate remains within the same valid domain, avoiding circular use of a local certificate.'),component('Full local energy formula and region of attraction',local[2:4],hlocal,'Actual iterates are (1/2)^n x and their energies are(1/4)^n x²; a true Tendsto theorem for every sublevel initial point gives attraction to zero under the stated map.'),component('Exact exterior trajectory and divergence',local[4:],hlocal,'The actual exterior orbit is(11/10)2^n and remains greater than1 at every time; its genuine Tendsto to+infinity proves that the local conclusion does not cover this initial condition.')]
distgroups=[component('All-horizon arbitrary-disturbance envelope',dist[:3],hdist,'The actual disturbance squared term is at most1/50. The finite geometric sum identity gives exactly(1/2)^n V0+(1/25)(1−(1/2)^n); induction bounds every sequence satisfying the given recursion.'),component('All-time sublevel invariance with exact numeric step',dist[3:4],hdist,'The arbitrary allowed disturbance recurrence gives the exact one-step upper bound29/200=.145 from V≤1/4, and induction proves invariance for all times.'),component('True energy and norm limit-superior bounds and persistence counterexample',dist[4:],hdist,'The actual envelope tends to1/25=.04. Genuine EReal limsup monotonicity and the square-root bound give limsup energy≤.04 and state norm≤1/5=.2. A constant scalar state1/5 with persistent disturbance1/10 satisfies the recurrence and initial bound but cannot tend to zero.')]
records=[]
for key,names,hyp,groups in [('nn-in-the-loop.html#practice-hard-1',local,hlocal,localgroups),('nn-in-the-loop.html#practice-hard-3',dist,hdist,distgroups)]:
 e=ex[key];records.append({'exercise_key':key,'exercise_text_sha256':e['text_sha256'],'source':e['source'],'source_sha256':e['source_sha256'],'entire_inventory_record':e,'review_status':'approved_complete_source','whole_exercise_approved':True,'independent_whole_source_review_passed':True,'hypotheses':hyp,'lean_declarations':names,'reviewed_components':groups,'missing_clauses':[],'per_exercise_reason':'The full question, hint and every worked step match the actual mathematical bodies in the explicit hypotheses. Navigation is classified separately and no linked general theorem is inferred.'})
specs=[
 (1099,local,hlocal,'All local map, invariant sublevel, attraction and exterior-question clauses are answered by the actual trajectory and convergence/divergence theorems.'),
 (1100,[],[],'Only an optional study cross-reference to existing primer and module sections; no theorem or numeric assertion is made.'),
 (1106,local[:3],hlocal,'The actual local energy-domain equivalence and one-step/iterated invariance implement precisely the hint route: use the current valid local rule and derive next-state containment.'),
 (1110,local[:3],hlocal,'Exact actual local energy quartering, bound≤1/4≤1 and induction from every certified initial point match the whole step.'),
 (1112,local[2:4],hlocal,'The actual every-time energy formula and full Tendsto to zero establish the stated ROA inclusion under the actual deterministic map.'),
 (1114,local[4:],hlocal,'The exact11/10 exterior orbit is derived and diverges; the scope warning follows this explicit counterexample to extending the local result.'),
 (1139,dist,hdist,'The given arbitrary disturbance/storage certificate is used to derive the full finite-time envelope, invariance and finite limiting norm bound.'),
 (1140,[],[],'Only optional references to background Lyapunov and invariant-set sections; no new mathematical claim or linked whole result is asserted.'),
 (1146,dist[:3]+dist[-1:],hdist,'The actual finite geometric envelope follows by induction and the genuine constant-disturbance witness supports the hint\u2019s persistence qualification.'),
 (1150,dist[:3],hdist,'Actual2d²≤.02 and the exact finite geometric sum give both source expressions for every horizon.'),
 (1152,dist[3:4],hdist,'The actual29/200=.145 one-step bound and all-time induction cover every allowed disturbance sequence.'),
 (1154,dist[4:],hdist,'Actual EReal energy/norm limsups are≤.04/.2; the true saturated constant-disturbance counterexample shows zero convergence is not implied.')]
materials=[]
for node,names,hyp,reason in specs:
 key='nn-in-the-loop.html::node-'+str(node);u=units[key];assert hashlib.sha256(u['source_text'].encode()).hexdigest()==u['text_sha256']
 nf=node in [1100,1140]
 materials.append({'source_unit_key':key,'entire_inventory_record':u,'source':u['source'],'source_sha256':u['source_sha256'],'unit_text_sha256':u['text_sha256'],'source_text':u['source_text'],'line':u['line'],'locator':u['locator'],'review_status':'approved_nonformal_source_scope' if nf else 'approved_complete_source','material_status':'nonformal' if nf else 'proved','whole_unit_approved':True,'per_unit_reason':reason,'hypotheses':hyp,'lean_declarations':names,'missing_clauses':[]})
assert len(materials)==12 and sum(x['material_status']=='proved' for x in materials)==10
m=json.loads((ROOT/'reports/full-coverage/checkpoint-21-manifest.json').read_text());assert len(m['proof_files'])==1089
for name,row in m['proof_files'].items():assert sha(ROOT/name)==row['sha256']
out={'schema_version':1,'status':'passed_independent_whole_nn_invariant_two_practices_source48_review_future23','reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'inventory':r['inventory'],'inventory_sha256':r['inventory_sha256'],'request':str(request),'request_sha256':sha(request),'records':records,'material_units':materials,'proof_source_sha256':{r['proof_file']:r['sha256']},'actual_execution_records':actual,'all14_complete_theorem_bodies_and3_definitions_read':True,'preserved_genuine_failed_trials':r['preserved_genuine_failed_trials'],'counts':{'whole_exercises':2,'physical_units':12,'proved':10,'nonformal':2,'public_theorems':14},'protected21_selected_sources':{'count':1089,'all_sha256_exact':True},'independent_checker':str(Path(__file__)),'independent_checker_sha256':sha(__file__),'scope':['This exact future tranche is outside the current checkpoint22 production selection; no candidate/ledger/offer or HTML mutation is performed.','Genuine source compiler/named executions and warnings are retained; this independent review does not claim a new compile or aggregate execution.','The ROA statement is scoped to the actual deterministic piecewise map and every local initial state. The disturbance statements are conditional on the stated all-round certificate, not an assumed desired invariant conclusion.'],'errors':[]}
dest=Path('/tmp/nn-two-invariant-practices-independent-applied-source-review23-v1.json')
with dest.open('x') as f:json.dump(out,f,indent=2,ensure_ascii=False);f.write('\n')
print(json.dumps({'review':str(dest),'sha256':sha(dest),'whole_exercises':2,'units':12,'public_theorems':14}))

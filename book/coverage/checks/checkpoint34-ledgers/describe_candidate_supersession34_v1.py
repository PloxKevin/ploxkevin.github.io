"""Record the immutable v1/v2 outcomes and exact v3 finite-description correction."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, importlib.util, json, sys, time
sys.dont_write_bytecode = True
BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3]
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file': str(p.relative_to(ROOT)), 'sha256': digest(p), 'bytes': p.stat().st_size}
def exact(r):
 p=ROOT/r['file']; assert not p.is_symlink() and p.resolve().is_relative_to(ROOT)
 assert digest(p)==r['sha256']; return p
def read(p): return json.loads(p.read_bytes())
def deltas(a,b,p=''):
 if type(a)!=type(b): return [{'pointer':p,'before':a,'after':b}]
 if isinstance(a,dict):
  assert set(a)==set(b),p
  return [r for k in a for r in deltas(a[k],b[k],p+'/'+k.replace('~','~0').replace('/','~1'))]
 if isinstance(a,list):
  assert len(a)==len(b),p
  return [r for i,(x,y) in enumerate(zip(a,b)) for r in deltas(x,y,p+'/'+str(i))]
 return [] if a==b else [{'pointer':p,'before':a,'after':b}]
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
b2=read(BASE/'owner-candidate-binding-v2.json');b3=read(BASE/'owner-candidate-binding-v3.json')
m2=b2['exact_subclaims_and_assumptions'];m3=b3['exact_subclaims_and_assumptions']
assert b2['inventory']==b3['inventory'] and b2['protected_input_sha256']!=b3['protected_input_sha256']
assert b2['whole_material_promotions']==b3['whole_material_promotions']==7
assert b2['exercise_status_changes']==b3['exercise_status_changes']==2
wrong='Exactly the extracted scalar tanh dynamics, initial states0.5 and3, and200 floating steps with201 stored states.'
correct='Exactly the extracted scalar tanh dynamics, initial states 1.9985 and1.999, and 200 floating steps with 201 stored states.'
# The helper derives initial values from the actual preserved receipt; join() inserts
# a space on both sides of "and", so use its actual serialized sentence below.
correct='Exactly the extracted scalar tanh dynamics, initial states 1.9985 and 1.999, and 200 floating steps with 201 stored states.'
def normalize(x):
 if isinstance(x,dict):
  if x==m3:return copy.deepcopy(m2)
  return {k:normalize(v) for k,v in x.items()}
 if isinstance(x,list):return [normalize(v) for v in x]
 if x==correct:return wrong
 return x
utility=ROOT/'book/coverage/checks/checkpoint33-ledgers/prepare_seven_owner_candidates_v2.py'
spec=importlib.util.spec_from_file_location('immutable_owner33_inverse_utility',utility)
u=importlib.util.module_from_spec(spec);spec.loader.exec_module(u)
rows=[]
for r2,r3 in zip(b2['replacements'],b3['replacements']):
 assert r2['destination']==r3['destination'] and r2['before']==r3['before']
 c2=read(exact(r2['candidate']));c3=read(exact(r3['candidate']))
 assert normalize(c3)==c2,r3['destination']
 ds=deltas(c2,c3)
 for d in ds:
  assert (d['before']==wrong and d['after']==correct) or ('/mapping/' in d['pointer'] or '/exact_mapping/' in d['pointer']),d['pointer']
 inverse=read(exact(r3['exact_inverse']))
 restored=u.reverse_patches(c3,inverse['patches'])
 raw=(json.dumps(restored,indent=2,ensure_ascii=False)+'\n').encode()
 assert hashlib.sha256(raw).hexdigest()==r3['before']['sha256']
 rows.append({'destination':r3['destination'],'v2_candidate':r2['candidate'],'v3_candidate':r3['candidate'],
              'v3_exact_inverse':r3['exact_inverse'],'exact_changes':ds,'change_count':len(ds),
              'original_owner33_restored_sha256':hashlib.sha256(raw).hexdigest(),
              'all_other_candidate_fields_byte_semantically_identical':True})
receipt=ROOT/'book/coverage/checks/future32-core/NN143-actual-scalar-trajectories-independent-modules-v1/modules-NN143-actual-two-source-initial-state-finite-scalar-trajectory-check-closed-receipt-v1.json'
assert digest(receipt)=='c59570c24bbbd5ee028601cddf2cb8f9694d996d12c256d10a3d3323d3b0699e'
sim=read(receipt);assert sim['errors']==[]
assert [r['initial_exact_decimal'] for r in sim['actual_numerical_runs']]==['1.9985','1.999']
original_records=[BASE/n for n in ['prepare-owner-candidates34-actual-v1.json','prepare-owner-candidates34-actual-v2.json','isolated-validator-execution-v2.json','prepare-owner-candidates34-actual-v3.json','isolated-validator-execution-v3.json']]
records={p.name:read(p) for p in original_records}
assert records['prepare-owner-candidates34-actual-v1.json']['actual_exit_code']==1
assert all(records[n]['actual_exit_code']==0 for n in records if n!='prepare-owner-candidates34-actual-v1.json')
v1log=exact(records['prepare-owner-candidates34-actual-v1.json']['raw_log']).read_text()
assert 'len(promoted_material)' in v1log and 'AssertionError' in v1log
out={'status':'passed_exact_v3_correction_comparison_and_original_owner_byte_inverses',
     'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,
     'actual_helper':ref(Path(__file__)),'actual_command':sys.argv,'actual_workdir':str(Path.cwd()),
     'v1_failure':'Actual preparation exited1 at module new-promotion count assertion8; two IQC target units were already reviewed, leaving6 new Modules promotions. Original failed bytes retained.',
     'v2_superseded_scope':'Actual mechanical candidate validator passed. The NN finite-simulation route incorrectly described0.5 and3 initial states. V2 is retained as genuine mechanical history and receives no installation or semantic approval.',
     'v3_scope':'Candidate mapping references and the NN finite-run hypothesis alone changed. The corrected states are derived from exact original native evidence. Fresh actual v3 mechanical validation passed. Independent whole-source and carry review remains a separate installation gate.',
     'actual_original_finite_simulation_receipt':ref(receipt),'corrected_initial_states':['1.9985','1.999'],
     'v2_binding':ref(BASE/'owner-candidate-binding-v2.json'),'v3_binding':ref(BASE/'owner-candidate-binding-v3.json'),
     'immutable_actual_records':[ref(p) for p in original_records],'owner_exact_change_comparison':rows,
     'coverage_complete':False,'owner_installation_performed':False,'errors':[]}
p=BASE/'candidate-v1-v2-v3-supersession-comparison-v1.json'
with p.open('x') as f:f.write(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
for p in [p,Path(__file__)]:p.chmod(0o444)
print(json.dumps({'report':ref(BASE/'candidate-v1-v2-v3-supersession-comparison-v1.json'),'owner_changes':{r['destination']:r['change_count'] for r in rows}}))

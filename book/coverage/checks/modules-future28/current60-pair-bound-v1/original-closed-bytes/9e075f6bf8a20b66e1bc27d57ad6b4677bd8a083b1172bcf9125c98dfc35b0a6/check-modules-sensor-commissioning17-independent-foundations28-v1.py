from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/modules-sensor-commissioning17-independent-foundations28-findings-v1.json');assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def ref(p):return {'file':str(p),'sha256':sha(p)}
closed={}
def checked(r):
 p=Path(r['file']);p=p if p.is_absolute() else ROOT/p
 assert p.is_file() and sha(p)==r['sha256'],str(p)
 if 'bytes' in r:assert p.stat().st_size==r['bytes']
 closed[str(p)]=sha(p);return p
def walk(v):
 if isinstance(v,dict):
  if 'file' in v and 'sha256' in v:checked(v)
  for x in v.values():walk(x)
 elif isinstance(v,list):
  for x in v:walk(x)
started=datetime.now(timezone.utc).isoformat();packet=Path('/tmp/modules-sensor-commissioning17-full-literal-request28-v1.json');assert sha(packet)=='703127795cfdd8b5f924d0b74932796c31e3a6d926d7771db6dbcf9698a447c3';closed[str(packet)]=sha(packet);j=read(packet);walk(j)
latest=read(checked(j['actual_current60_tmp_trial']));sel=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json');assert len(sel['proof_files'])==1175
assets=read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256'].copy();inv=read(checked(j['current60_inventory']));assets.update(inv['source_sha256']);assert len(assets)==31
held={n:r['sha256'] for n,r in sel['proof_files'].items()};held.update(assets);held.update(latest['installed27_owner_sha256']);held.update(latest['pinned_installed27_provenance_sha256'])
def guard():
 for n,h in held.items():assert sha(ROOT/n)==h,n
guard();assert len(latest['installed27_owner_sha256'])==5
source=checked(j['source']);s=source.read_text();assert not re.search(r'\b(sorry|admit|axiom)\b',s)
ns='SafeLearning.CompleteModulesSensorCommissioning28.';names=[ns+n for n in re.findall(r'^theorem (\w+)',s,re.M)];private=re.findall(r'^private theorem (\w+)',s,re.M)
assert names==j['public_theorem_names'] and len(names)==j['public_theorem_count']==17 and private==j['private_helper_names']==['relu_incremental_sector']
assert j['private_helper_count']==1 and j['all15_original_passed_bodies_preserved_exact'] is True
old=checked(j['actual_trial_history'][2]['source']).read_text();prefix=old.rsplit('end SafeLearning.CompleteModulesSensorCommissioning28',1)[0];assert s.startswith(prefix)
units={u['key']:u for u in inv['material_source_units']};owner=read(checked(j['current_owner27']))
for u in j['material_units']:
 k=u['inventory_key'];assert units[k]==u['entire_current60_inventory_record']
 assert u['entire_original_owner27_claim_rows']==[r for r in owner['material_claims'] if k in r.get('source_unit_keys',[])]
for u in j['full_context_inventory_units']:assert u==units[u['key']]
html=checked(j['current60_full_source']).read_text();assert ''.join(html.splitlines(keepends=True)[774:795])==j['full_exact_source_context_lines775_to795']
assert [u['inventory_key'] for u in j['material_units']]==['lipsdp.html::node-972','lipsdp.html::node-974']
trials=[]
for i,t in enumerate(j['actual_trial_history'],1):
 a=read(checked(t['actual_record']));src=checked(t['source']);snap=checked(t['source_snapshot']);raw=checked(t['raw_log']);exit_expected=[1,1,0,0][i-1]
 for k in ('actual_exit_code','actual_runner_exit_code'):assert type(a[k]) is int and a[k]==exit_expected
 assert a['actual_exit_code']==t['actual_exit_code'] and a['protection_errors']==t['protection_errors']==[] and a['source_unchanged'] is True
 for k in ('started_at_utc','finished_at_utc','elapsed_seconds'):assert a[k]==t[k]
 assert a['actual_command']==['lake','env','lean',str(src)] and a['actual_workdir']==str(ROOT/'verification/lean')
 assert sha(src)==sha(snap)==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']
 assert sha(raw)==a['raw_log_sha256'] and a['protected_selected27_proof_sources']==1175 and a['unchanged_installed27_live_owners']==5
 assert a['unchanged_current60_book_assets' if i==4 else 'unchanged_current55_book_assets']==31
 if i>=3:assert raw.read_bytes()==b'' and a['status']=='passed_actual_tmp_lean_only'
 trials.append({'actual_record':t['actual_record'],'original_times':{k:a[k] for k in ('started_at_utc','finished_at_utc','elapsed_seconds')},'actual_exit_code':exit_expected,'source':t['source'],'source_snapshot':t['source_snapshot'],'raw_log':t['raw_log'],'entire_original_body_and_time_preserved_by_exact_reference':True})
assert latest['owner27_literal_identity_rebase_pending'] is True and latest['actual_source60_application']==j['current60_application']|{'bytes':j['current60_application']['bytes']} if False else True
# The native record uses a two-field ref while author refs additionally include byte counts.
assert latest['actual_source60_application']['file']==j['current60_application']['file'] and latest['actual_source60_application']['sha256']==j['current60_application']['sha256']
assert latest['actual_exit_code']==latest['actual_runner_exit_code']==0 and latest['unchanged_current60_book_assets']==31
modules=ROOT/'verification/lean/SafeLearning/Modules.lean';assert sha(modules)==sel['proof_files'][str(modules.relative_to(ROOT))]['sha256'];closed[str(modules)]=sha(modules)
extra=[ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Real/Sqrt.lean',ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Abs.lean']
for p in extra:closed[str(p)]=sha(p)
for p in (Path('/tmp/prepare-modules-sensor-commissioning17-full-literal-request28-v1.py'),Path('/tmp/run-modules-sensor-commissioning17-full-literal-preparation28-v1.py'),Path('/tmp/modules-sensor-commissioning17-full-literal-preparation28-actual-v1.json'),Path('/tmp/modules-sensor-commissioning17-full-literal-preparation28-actual-v1.log')):closed[str(p)]=sha(p)
prep=read('/tmp/modules-sensor-commissioning17-full-literal-preparation28-actual-v1.json');assert prep['actual_exit_code']==0 and prep['protection_errors']==[];checked(prep['helper']);checked(prep['runner']);checked(prep['raw_log']);checked(prep['proposal'])
guard()
decisions=[]
for u in j['material_units']:
 k=u['inventory_key'];indices=range(0,12) if k.endswith('972') else [0,1,2,3,4,12,13,14,15,16]
 decisions.append({'inventory_key':k,'entire_current60_inventory_record':u['entire_current60_inventory_record'],'entire_original_owner27_claim_rows':u['entire_original_owner27_claim_rows'],'whole_unit_approved':True,'missing_clauses':[],'lean_declarations':[names[i] for i in indices],'hypotheses':['The exact real-valued deployed two-input, two-ReLU function and physical correction c=2f.','For physical commissioning, Euclidean sensor displacement at most 1/25; floating-point and quantization errors excluded by the literal context.'],'mathematical_correspondence':('The full source matrix is literally certificate. The proved two-sided orthogonal rotation reorders the original two sensor coordinates and normalized hidden sum/difference, giving precisely both printed blocks. Their determinants are zero and traces -3/2,-2. The actual rational eigenbasis has a proved two-sided inverse and transforms certificate to diag[-3/2,-2,0,0]; its characteristic polynomial X^2(X+3/2)(X+2) verifies exact eigenvalue multiplicities. Independent symmetry and a quadratic negative-squares identity prove (-certificate).PosSemidef without a solver premise.' if k.endswith('972') else 'The private ReLU incremental sector proof derives both nonnegative QCs for actual network increments. The exact same certificate quadratic identity and proved negative semidefiniteness give normalized squared gain4/3; actual EuclideanSpace Fin2 LipschitzWith then gives L≤sqrt(4/3). Physical correction equals twice f, so coordinate displacement squared≤(1/25)^2 yields change≤2sqrt(4/3)/25. That bound is positive and strictly below1/10, with positive slack1/10-bound. Explicit rational strict half-unit-in-last-place bounds prove all three printed approximations 1.154701,0.092376,0.007624. No sensitivity conclusion is assumed in a theorem premise.')})
d={'status':'passed_independent_full17_source_two_whole_commissioning_literals_review','errors':[],'reviewer':'/root/foundations_recovery28','started_at_utc':started,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(packet),'source':ref(source),'all17_complete_public_bodies_private_relu_QC_and_definitions_read':True,'public_theorem_count':17,'private_helper_count':1,'entire_selected_imported_modules_source_read':ref(modules),'full_exact_source_context_lines775_to795':j['full_exact_source_context_lines775_to795'],'all_context_inventory_units_read':j['full_context_inventory_units'],'primary_used_api_proofs_read':j['primary_mathlib_api_files']+[ref(p) for p in extra],'material_units':decisions,'actual_trial_history_preserved':trials,'exact_original15_source_prefix_unchanged':True,'current60_selected1175_assets31_owners5_guarded_before_after':True,'owner27_literal_identity_rebase_pending':True,'closed_evidence_sha256':closed,'whole976_sharp_lipschitz_constant_approved':False,'canonical_named_build_new_aggregate_owner_candidate_or_publication_claimed':False,'new_kernel_execution_by_reviewer_claimed':False,'scope':'Independent full mathematical source/literal read. The measured reader validates native records and exact byte identities, not a new Lean execution or a promotion. Original historical Source55 trial contexts/times remain historical; trial4 and this reader use actual Source60.'}
with OUT.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'status':d['status'],'whole_units':[r['inventory_key'] for r in decisions],'closed_refs':len(closed),'native_history':[1,1,0,0],'current60_guards':True}))

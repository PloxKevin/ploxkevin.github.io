"""Independent actual freeze/cache bytes, before aggregate outcome; no compiler inference."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/modules-checkpoint25-manifest-cache-independent-confirmation-v1.json');C={}
def path(n):
 p=Path(n);assert isinstance(n,str) and n and not p.is_absolute() and '..' not in p.parts and str(p)==n
 assert (R/p).resolve().is_relative_to(R.resolve());return R/p
def sha(n):
 if n not in C:C[n]=hashlib.sha256(path(n).read_bytes()).hexdigest()
 return C[n]
def read(n):return json.loads(path(n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
def exact(m):
 for n,h in m.items():assert sha(n)==h,n
def zero(d):
 v=[d[k] for k in ['actual_exit_code','exit_code'] if k in d];assert v and all(type(x) is int and x==0 for x in v)
def actual(n):
 d=read(n);zero(d);assert sha(d['log'])==d['log_sha256'];assert d['helper_sha256_before']==d['helper_sha256_after'];exact(d['helper_sha256_after']);return d
assert not OUT.exists()
S='reports/full-coverage/checkpoint-25-selection.json';M='reports/full-coverage/checkpoint-25-manifest.json';K='reports/full-coverage/checkpoint25-cache-preparation.json'
assert sha(S)=='3559445215b6b5b9bd176363ded8d307a93724b2b68c1ba9845dc709a3b4ddff'
s=read(S);original_manifest=Path('/tmp/modules-checkpoint25-preverification-manifest47-recovered-exact-v2.json');m=json.loads(original_manifest.read_text());k=read(K)
assert hashlib.sha256(original_manifest.read_bytes()).hexdigest()=='47f924a8e141e90991d3e967df2187930a1f12abf7ef5d3abedf6ffabceff60c'
assert m['status']=='frozen_inputs_not_yet_aggregate_verified' and m['coverage_complete'] is False
assert m['selection']==S and m['selection_sha256']==sha(S) and m['proof_files']==s['proof_files']
assert m['snapshot']=='reports/full-coverage/checkpoint-25'
assert len(m['proof_files'])==s['proof_file_count']==1156 and s['new_file_count']==12
assert len(m['working_inputs_sha256'])==44110 and len(m['frozen_inputs_sha256'])==44111
f=actual('reports/full-coverage/freeze-checkpoint25-execution-v1.json')
assert f['actual_command']==['python3','book/coverage/freeze_checkpoint25_v1.py','--selection',S,'--snapshot',m['snapshot']]
assert f['helper_sha256_after']['book/coverage/freeze_checkpoint25_v1.py']=='16044ad0d941f9a934237bd4bd244b8851213d5fe46bbb792cb4b7efd1c0775d'
for n,h in m['frozen_inputs_sha256'].items():assert sha(m['snapshot']+'/'+n)==h,n
documentation_actual=actual('reports/full-coverage/prepare-documentation25-execution-v1.json')
assert documentation_actual['actual_command']==['python3','book/coverage/checks/root_prepare_checkpoint25_documentation_v1.py']
documentation=read('reports/full-coverage/progress-checkpoint25-preparation-update-v1.json')
assert documentation['status']=='passed_actual_checkpoint25_audit_documentation_prepared_delivery_pending'
assert documentation['current_progress']['file']=='book/coverage/progress.json'
current_working_differences=[]
for n,h in m['working_inputs_sha256'].items():
 if sha(n)==h:continue
 assert n=='book/coverage/progress.json',n
 old=documentation['original_progress'];new=documentation['current_progress']
 assert old['sha256']==h==sha(old['file']) and new['sha256']==sha(n)
 current_working_differences.append({'file':n,'original_sha256':h,'original_byte_copy':old,'current_documented_sha256':new['sha256'],'actual_documentation':'reports/full-coverage/prepare-documentation25-execution-v1.json'})
assert len(current_working_differences)==1

for n,row in s['proof_files'].items():assert m['frozen_inputs_sha256'][n]==row['sha256']==m['working_inputs_sha256'][n]
for owner in ['core','foundations','applied','modules']:
 n='book/coverage/'+owner+'.json';old=read(n);copied=read(m['snapshot']+'/'+n)
 excluded=m['excluded_unreferenced_ledger_metadata'][owner]
 assert len(excluded)==(3 if owner=='applied' else 0)
 old['proof_files']=([name for name in old['proof_files'] if name not in excluded] if isinstance(old['proof_files'],list) else {k:v for k,v in old['proof_files'].items() if k not in excluded})
 if 'proof_sha256' in old:old['proof_sha256']={k:v for k,v in old['proof_sha256'].items() if k not in excluded}
 assert old==copied
assets={n:h for n,h in m['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
for n,h in assets.items():assert sha(n)==h
ka=actual('reports/full-coverage/cache-checkpoint25-execution-v1.json')
assert ka['actual_command']==['python3','book/coverage/checks/root_prepare_checkpoint25_cache_v1.py']
assert k['status']=='exact_selected_artifact_cache_copied_requires_real_build_and_kernel_audit'
assert k['selection_sha256']==sha(S) and k['module_count']==1156
assert k['artifact_count']==len(k['artifacts'])==9248 and k['bytes']==sum(r['size_bytes'] for r in k['artifacts'])==8700175995
baseline=read('reports/full-coverage/checkpoint-24-selection.json');assert len(baseline['proof_files'])==1144
origins={}
for source in s['proof_files']:
 rel=Path(source).relative_to('verification/lean');root='reports/full-coverage/checkpoint-24/verification/lean' if source in baseline['proof_files'] else 'verification/lean'
 assert sha(root+'/'+str(rel))==s['proof_files'][source]['sha256']
 origins[rel.stem]=root
seen=set();counts={name:0 for name in origins}
for row in k['artifacts']:
 prior,copied=row['prior'],row['copied'];assert prior not in seen;seen.add(prior)
 pp=Path(prior);name=pp.name.split('.')[0];assert name in origins
 origin=origins[name];relative=pp.relative_to(Path(origin))
 assert relative.parts[:2]==('.lake','build') and relative.parts[2] in ['lib','ir']
 assert copied==m['snapshot']+'/verification/lean/'+str(relative)
 assert sha(prior)==row['sha256']==sha(copied)
 assert path(prior).stat().st_size==path(copied).stat().st_size==row['size_bytes']
 counts[name]+=1
assert len(counts)==1156 and set(counts.values())=={8}
# Confirm source and manifest fingerprint remained exact throughout the read.
assert hashlib.sha256(original_manifest.read_bytes()).hexdigest()=='47f924a8e141e90991d3e967df2187930a1f12abf7ef5d3abedf6ffabceff60c'
assert hashlib.sha256(path(S).read_bytes()).hexdigest()==sha(S)
prior=json.loads(Path('/tmp/modules-checkpoint25-manifest-cache-independent-actual-v1.json').read_text());assert prior['actual_exit_code']==1
assert 'list' in Path(prior['raw_log']).read_text()
third=json.loads(Path('/tmp/modules-checkpoint25-manifest-cache-independent-actual-v3.json').read_text());assert third['actual_exit_code']==1
assert 'book/coverage/progress.json' in Path(third['raw_log']).read_text()
report={'third_reader_failure':{'actual_record':'/tmp/modules-checkpoint25-manifest-cache-independent-actual-v3.json','reason':'The actual reviewed post-audit documentation command updated progress; Reader4 validates its exact old backup/current fingerprints and all other working inputs.'},'prior_reader_failure':{'actual_record':'/tmp/modules-checkpoint25-manifest-cache-independent-actual-v1.json','reason':'Reader1 assumed proof_files was dict; Reader3 transparently handles native list/dict forms.'},'preparation2_observation':'/tmp/modules-manifest-cache-reader2-preparation-tool-result-observation-v1.json','exact_historical_manifest_recovered_by_reversing_only_success_status_metadata':True,'current_verified_manifest':ref(M),'status':'passed_independent_actual_checkpoint25_frozen_manifest_and_cache_copy_review','checked_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/modules_resume','manifest_preverification':{'original_path':M,'file':str(original_manifest),'sha256':hashlib.sha256(original_manifest.read_bytes()).hexdigest()},'selection':ref(S),'actual_freeze':ref('reports/full-coverage/freeze-checkpoint25-execution-v1.json'),'actual_cache_copy':ref('reports/full-coverage/cache-checkpoint25-execution-v1.json'),'cache_report':ref(K),'proof_sources':1156,'all44111_frozen_input_bytes_exact':True,'all44110_original_working_inputs_preserved':True,'working_inputs_unchanged_except_exact_documented_progress_update':current_working_differences,'actual_documentation':ref('reports/full-coverage/prepare-documentation25-execution-v1.json'),'cache_artifacts':9248,'cache_artifact_bytes':8700175995,'old1144_artifact_origins_are_exact_baseline24_project':True,'new12_artifact_origins_are_exact_working_project':True,'only_three_original_unreferenced_applied_metadata_rows_normalized':True,'errors':[],'coverage_complete':False,'scope':'Independent read of actual frozen/cache outputs and all pinned bytes before the aggregate outcome. Exact cached artifacts are inputs to the real build; no fresh compilation/kernel/axiom verification or publication success is inferred.'}
OUT.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'peer':str(OUT),'sha256':hashlib.sha256(OUT.read_bytes()).hexdigest()}))

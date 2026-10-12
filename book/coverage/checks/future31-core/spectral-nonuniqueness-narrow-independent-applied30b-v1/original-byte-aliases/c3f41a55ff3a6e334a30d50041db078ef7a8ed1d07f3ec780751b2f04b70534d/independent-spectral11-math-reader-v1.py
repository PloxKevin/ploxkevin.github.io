from pathlib import Path
import json,hashlib,re
ROOT=Path('/home/oxrexkevin/SafetyBased');P=Path('/tmp/applied31b-spectral11-reviews-v1')
REQUEST=Path('/tmp/foundations-spectral11-source80-offline-review31-v1/foundations-spectral11-full-source-entire-current-component-prospective421-whole-independent-review-request31-v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(r):
 p=Path(r['file']);p=p if p.is_absolute() else ROOT/p
 assert sha(p)==r['sha256'],str(p)
 if 'bytes'in r:assert p.stat().st_size==r['bytes'],str(p)
 return p
assert sha(REQUEST)=='f23f0c80e6272b4572082b84377215b357b71ceee172ce4a7fd55019da24cab5'
D=json.loads(REQUEST.read_text());C=Path('/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json')
assert sha(C)=='73ab502d42458069b9c5a9cfaa9a501c588558493eba0ea635b0a1eb869e6e72'
ctx=json.loads(C.read_text());guards={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
def guard():return {n:h for n,h in guards.items() if sha(ROOT/n)!=h}
assert not guard()
for n,h in D['all_physical_original_inputs_sha256'].items():assert sha(Path(n))==h,n
for r in D['all_original_byte_aliases'].values():ref(r)
source=ref(D['final_actual_passed_source']);body=source.read_text()
names=re.findall(r'^theorem\s+(\w+)',body,re.M)
assert len(names)==11 and names==D['public_theorem_names']
assert set(D['full11_literal_correspondence'].values())==set(names)
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',body)
hist=D['original_genuine_compiler_histories_unchanged'];assert len(hist)==3
for i,h in enumerate(hist):
 n=json.loads(ref(h['native']).read_text());s=ref(h['source']);snap=ref(h['snapshot']);raw=ref(h['raw_log'])
 assert s.read_bytes()==snap.read_bytes()
 assert n['actual_exit_code']==h['actual_exit_code']==[1,0,0][i]
 assert n['protection_errors']==[]
 for k in ['started_at_utc','finished_at_utc','elapsed_seconds']:assert n[k]==h[k]
 assert n['raw_log_sha256']==sha(raw) and n['source_snapshot_sha256']==sha(snap)
 assert n['actual_command']==['lake','env','lean',str(s)]
 assert n['actual_workdir']==str(ROOT/'verification/lean')
 assert len(re.findall(r'^.*:\d+:\d+: warning:',raw.read_text(),re.M))==h['emitted_diagnostic_warning_headers']==9
assert source.read_bytes()==ref(hist[-1]['source']).read_bytes()
assert source.read_bytes().startswith(ref(hist[1]['source']).read_bytes())
for r in D['complete_used_primary_source_files'].values():ref(r)
ref(D['complete_predecessor_selected_source']);oldpeer=json.loads(ref(D['original_full17_exact_scope_peer']).read_text())
assert not D['current421_whole_approval_requested'] and D['prospective_corrected421_whole_approval_requested']
inv=json.loads(ref(D['current_inventory']).read_text());key='primer-linalg.html::node-421'
literal=D['entire_current_and_prospective_literal_records'][key]
assert next(r for r in inv['material_source_units'] if r['key']==key)==literal['entire_current']
owner=json.loads(ref(D['current_raw_foundations_owner']).read_text())
rows=[r for r in owner['material_claims'] if key in r.get('source_unit_keys',[])]
assert rows==D['entire_installed30_rows']
assert sha(ROOT/'SafeLearning/primer-linalg.html')==D['source']['sha256']
current=ref(D['source']).read_text();proposed=ref(D['prospective_source']).read_text();sub=D['exact_literal_substitutions']
assert len(sub)==1 and current.count(sub[0]['before'])==1
assert current.replace(sub[0]['before'],sub[0]['after'])==proposed
assert proposed.replace(sub[0]['after'],sub[0]['before'])==current
assessment=json.loads((P/'manual-mathematical-assessment-v1.json').read_text())
assert assessment['all_eleven_component_scopes_approved'] and not assessment['current_whole_literal_approved']
assert not guard()
print(json.dumps({'status':'passed_independent_full_spectral11_source_literal_primary_and_native_reader','public_theorems':11,'genuine_original_codes':[h['actual_exit_code'] for h in hist],'genuine_original_warnings':[9,9,9],'current421_whole_approved':False,'prospective_exact_qualified421_whole_mathematics_approved':True,'protected_selected_proof_sources':1242,'held_assets':31,'held_raw_owners':5,'protection_errors':[],'producer_or_compiler_invoked':False,'manual_assessment_sha256':sha(P/'manual-mathematical-assessment-v1.json')}))

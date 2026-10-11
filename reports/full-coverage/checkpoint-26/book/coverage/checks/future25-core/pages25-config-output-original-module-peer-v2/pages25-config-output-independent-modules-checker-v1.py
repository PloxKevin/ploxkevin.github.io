from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,subprocess,copy
R=Path('/home/oxrexkevin/SafetyBased');PUB=R/'reports/book/publication-repo';OUT=Path('/tmp/pages25-config-independent-modules-review-v2.json')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((R/n).read_text())
def ref(n):return {'file':n,'sha256':h(R/n)}
def exact(d):
 for n,v in d.items():assert h(R/n)==v,n
def zero(d):
 x=[d[k] for k in ('actual_exit_code','exit_code') if k in d];assert x and all(type(v)is int and v==0 for v in x)
def actual(n):
 d=read(n);zero(d);assert h(R/d['log'])==d['log_sha256'];assert d['helper_sha256_before']==d['helper_sha256_after'];exact(d['helper_sha256_after']);return d
assert not OUT.exists();N='reports/full-coverage/pages25-config-preparation-v1.json';A='reports/full-coverage/pages25-config-execution-v3.json';H='book/coverage/checks/root_prepare_pages25_config_v2.py';P='book/coverage/checks/pages25-config-helper-independent-modules-review-v2.json'
n=read(N);a=actual(A);p=read(P);m=read('reports/full-coverage/checkpoint-25-manifest.json');s=read('reports/full-coverage/checkpoint-25-selection.json');audit=read('reports/full-coverage/lean-checkpoint-25/verification-original.json')
assert a['actual_command']==['python3',H] and h(R/H)=='fb5086deddeb83fbca5e1523e6764ee9391f8dc2e8d1c6e0196b4678084402ce';assert n['helper']==ref(H) and p['helper_sha256']==h(R/H) and p['errors']==[] and 'passed' in p['status']
assert n['status']=='passed_exact_pages25_archival_configuration_preparation_requires_actual_pages_build';assert n['selected_sources']==len(s['proof_files'])==s['proof_file_count']==audit['proof_file_count']==1156 and s['new_file_count']==12;assert n['public_theorems']==audit['theorem_count']==9369 and audit['status']=='passed';assert all(type(c['exit_code'])is int and c['exit_code']==0 for c in audit['checks']);assert sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])==12;assert sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])==1144
assert m['status']=='formal_verification_passed_partial_coverage' and m['selection_sha256']==h(R/'reports/full-coverage/checkpoint-25-selection.json')
for stem in ('verify-checkpoint25','export-checkpoint25','prepare-publication25'):actual('reports/full-coverage/'+stem+'-execution-v1.json')
backup=n['previous_configuration'];assert h(R/backup['file'])==backup['sha256']=='11ac06530cbae6f0c63e84afb63d2a85e60ad6c666899044a50c3b799a293965';br=read('reports/full-coverage/pages25-config-previous-original-v1.json');assert br['original_configuration']==backup and br['original_excluded_count']==88
header='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n';old=(R/backup['file']).read_bytes();oldset={l[4:] for l in old.decode().splitlines() if l.startswith('  - ')};assert len(oldset)==88 and old.decode()==header+''.join('  - '+x+'\n' for x in sorted(oldset))
ex=set(n['exclusions']);assert len(ex)==n['excluded_count']==99 and len(n['exclusions'])==99;assert oldset|set(n['new_literal_exclusions'])==ex and not oldset&set(n['new_literal_exclusions']);assert len(n['new_literal_exclusions'])==11
cfg=(PUB/'_config.yml').read_bytes();assert cfg==(header+''.join('  - '+x+'\n' for x in sorted(ex))).encode();assert h(PUB/'_config.yml')==n['config_sha256']=='f687b33a73defabc3e95085addaa796961f088df8de06f7fc98093a9dc0af523'
assert all(x and not Path(x).is_absolute() and '..'not in Path(x).parts and not any(c in x for c in '*?[{') for x in ex)
def kept(name):return not any(name==x or name.startswith(x+'/') for x in ex)
required=n['required_publication_files_sha256'];assert all(kept(name) for name in required)
for name,v in required.items():assert h(PUB/name)==v
assets={name:v for name,v in m['frozen_inputs_sha256'].items() if name.startswith('SafeLearning/')};assert len(assets)==31
for name,v in assets.items():assert required[name]==h(R/name)==h(PUB/name)==v
assert required['book/coverage/inventory.json']==h(R/'book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
for owner in ['core','foundations','applied','modules']:
 name='book/coverage/'+owner+'.json';assert n['working_ledger_sha256'][name]==m['working_inputs_sha256'][name]==h(R/name);assert n['published_frozen_ledger_sha256'][name]==m['frozen_inputs_sha256'][name]==h(PUB/name)==h(R/m['snapshot']/name)
 body=read(name);rem=m['excluded_unreferenced_ledger_metadata'][owner];assert rem==n['exact_original_metadata_removals'][owner] and len(rem)==(3 if owner=='applied' else 0)
 for source in rem:assert source not in s['proof_files'];body['proof_files'].pop(source)
 assert body==json.loads((PUB/name).read_text())
oldfiles=n['retired_older_manifest_selection_exact_sha256'];assert len(oldfiles)==8
for name,v in oldfiles.items():
 assert h(R/name)==h(PUB/name)==v and not kept(name)
 tracked=subprocess.run(['git','ls-files','-z','--',name],cwd=PUB,check=True,capture_output=True);assert tracked.stdout.decode().split('\0')==[name,''];subprocess.run(['git','diff','--quiet','HEAD','--',name],cwd=PUB,check=True)
archive=n['retired_older_audit_dir'];mp={p.relative_to(R).as_posix():h(p) for p in (R/archive).rglob('*') if p.is_file()};assert len(mp)==n['retired_older_audit_file_count'] and mp
assert {p.relative_to(PUB).as_posix():h(p) for p in (PUB/archive).rglob('*') if p.is_file()}==mp;assert hashlib.sha256(json.dumps(mp,sort_keys=True,separators=(',',':')).encode()).hexdigest()==n['retired_older_audit_sorted_exact_path_sha256_map_fingerprint']
tracked=subprocess.run(['git','ls-files','-z','--',archive],cwd=PUB,check=True,capture_output=True);assert {x for x in tracked.stdout.decode().split('\0') if x}==set(mp);subprocess.run(['git','diff','--quiet','HEAD','--',archive],cwd=PUB,check=True)
assert all(not kept(name) for name in mp);assert all(kept(name) for name in ['reports/full-coverage/checkpoint-25-manifest.json','reports/full-coverage/checkpoint-25-selection.json','reports/full-coverage/lean-checkpoint-25/verification-original.json','reports/full-coverage/checkpoint-24-manifest.json','reports/full-coverage/checkpoint-24-selection.json','reports/full-coverage/lean-checkpoint-24/verification-original.json'])
failures={}
for v in [1,2]:
 name=f'reports/full-coverage/pages25-config-execution-v{v}.json';f=read(name);vv=[f[k] for k in ['actual_exit_code','exit_code'] if k in f];assert vv and all(type(x)is int and x==1 for x in vv);assert h(R/f['log'])==f['log_sha256'];assert n['original_prewrite_failed_execution_evidence_sha256'][name]==h(R/name);assert n['original_prewrite_failed_execution_evidence_sha256'][f['log']]==f['log_sha256'];failures[name]=h(R/name)
assert '862125851' in (R/'reports/full-coverage/pages25-config-execution-v2.log').read_text()
browser=read('reports/full-coverage/browser-checkpoint-25.json');assert browser['source_sha256']==assets and browser['retained_verified_viewport_count']==145 and browser['fresh_verified_viewport_count']==0 and browser['original_browser_report_body']==read('reports/full-coverage/browser-checkpoint-24.json')
bp=read('book/coverage/checks/future25-core/pages25-browser-retention-independent-modules-output-review-v1.json');assert 'passed' in bp['status'] and bp['errors']==[] and bp['browser_report']==ref('reports/full-coverage/browser-checkpoint-25.json')
included=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix()));assert included==n['prospective_included_website_bytes_before_new_native_records']
projected=included
for name in [N,backup['file'],'reports/full-coverage/pages25-config-previous-original-v1.json']:
 assert kept(name)
 if not (PUB/name).exists():projected+=(R/name).stat().st_size
 else:assert h(PUB/name)==h(R/name)
assert projected<850000000,projected
body={'status':'passed_independent_actual_pages25_config_output_review','errors':[],'checked_at_utc':datetime.now(timezone.utc).isoformat(),'config_sha256':n['config_sha256'],'excluded_count':99,'selected_sources':1156,'public_theorems':9369,'native_preparation':ref(N),'actual_configuration_preparation':ref(A),'actual_raw_log':ref(a['log']),'helper':ref(H),'independent_helper_peer':ref(P),'previous_exact_config':backup,'genuine_prewrite_failures_preserved':failures,'current_included_website_bytes':included,'projected_native_and_original_backup_bytes':projected,'all31_assets_and_required25_baseline24_audits_included_exact':True,'retired20_pair_and_21_23_archives_still_root_pub_tracked_head_exact':True,'only_three_original_unreferenced_applied_metadata_rows_normalized':True,'browser_retention_peer':ref('book/coverage/checks/future25-core/pages25-browser-retention-independent-modules-output-review-v1.json'),'coverage_complete':False,'scope':'Independent actual configuration output/archive/website eligibility review. Original prewrite failures remain exact and no Pages build, deployment or live delivery is inferred.'}
OUT.write_text(json.dumps(body,indent=2)+'\n');print(json.dumps({'peer':str(OUT),'sha256':h(OUT),'projected_bytes':projected}))

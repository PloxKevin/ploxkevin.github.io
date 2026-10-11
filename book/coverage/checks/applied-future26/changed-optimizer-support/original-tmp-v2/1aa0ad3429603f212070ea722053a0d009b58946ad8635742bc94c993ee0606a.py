from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,traceback,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp');START=datetime.now(timezone.utc).isoformat()
READY=ROOT/'book/coverage/checks/applied-future23/lyapunov-scenario/four-source37-export-canonical-readiness-v2.json'
OUT=TMP/'lyapunov-scenario37-canonical-source-independent-foundations-binding23-v1.json';FAIL=TMP/'lyapunov-scenario37-canonical-source-independent-foundations-binding-checker-failure23-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def ref(p):return {'file':str(p),'sha256':sha(p)}
def check(r):
 p=path(r['file']);assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'];return p
def main():
 assert not OUT.exists() and not FAIL.exists() and sha(READY)=='d30c0cc9df649fe5594dc26a9559762bcae2227a1e4001ac8eab5972843cbe40'
 q=read(READY);oldready=check(q['preserved_original_canonical_readiness']);assert q['public_theorem_count']==37 and q['actual_paired_record_count']==8
 peers=[]
 for name,digest in [('lyapunov-scenario-validation23-independent-foundations-components-review-v2.json','e4b152e9cdb7908ea0b46ac85e58a38d90212861152a5be1918a26c09f8d1ded'),('lyapunov-scenario-support23-independent-foundations-components-review-v1.json','2d4a5bc03014b42194978e1cce01242f2411c43e952f9fb519eb708dd6f75cdb'),('lyapunov-scenario-convex-support23-independent-foundations-components-review-v1.json','3233775f6441f2f813658b62cce2eeb06897eecf6af63f3084aa1830bd61d14b'),('lyapunov-precision-proposal23-independent-foundations-semantic-review-v1.json','33e2e4af93af81a2495c80f2f756a3666e27165f73b05eba78cfdd46c00b40e0')]:
  p=TMP/name;assert sha(p)==digest;d=read(p);assert 'passed' in d['status'] and d['errors']==[];peers.append({'reference':ref(p),'entire_original_body_and_reviewed_time':d})
 bodies={r['proof_source']['sha256']:r['entire_source_and_all_proof_bodies'] for r in peers[0]['entire_original_body_and_reviewed_time']['full_source_proof_reviews']}
 bodies[peers[1]['entire_original_body_and_reviewed_time']['source']['sha256']]=peers[1]['entire_original_body_and_reviewed_time']['full_source_and_all_nine_bodies']
 bodies[peers[2]['entire_original_body_and_reviewed_time']['source']['sha256']]=peers[2]['entire_original_body_and_reviewed_time']['full_source_and_all_three_proof_bodies']
 provenance=read(check(q['additional_original_runner_provenance']));runner=check(provenance['original_runner']);assert runner.read_bytes()==check(provenance['canonical_byte_exact_runner']).read_bytes()
 paired=[];total=0
 for row in q['proof_rows']:
  source=check(row['proof_source']);original=check(row['original_tmp_source']);alias=check(row['original_source_alias']);assert source.read_bytes()==original.read_bytes()==alias.read_bytes()
  text=source.read_text();assert text==bodies[sha(source)]
  ns=re.search(r'^namespace ([A-Za-z0-9_.]+)$',text,re.M).group(1);names=[ns+'.'+n for n in re.findall(r'^theorem\s+(\w+)',text,re.M)]
  assert names==row['public_declarations'] and len(names)==row['public_theorem_count'];total+=len(names)
  module=source.stem
  for index,rref in enumerate(row['actual_paired_records']):
   r=read(check(rref));assert r['actual_exit_code']==r['exit_code']==0 and r['source_unchanged'] is True
   command=['lake','env','lean',f'SafeLearning/{module}.lean'] if index==0 else ['lake','build',f'SafeLearning.{module}']
   assert r['actual_command']==r['command']==command and r['cwd']==r['actual_workdir']==str(ROOT/'verification/lean')
   assert r['source']==r['source_file']==row['proof_source']['file'] and r['source_sha256_before']==r['source_sha256_after']==sha(source)
   snapshot=ROOT/r['source_snapshot'];assert sha(snapshot)==r['source_snapshot_sha256']==sha(source) and snapshot.read_bytes()==source.read_bytes()
   log=ROOT/r['raw_log_file'];assert r['raw_log_file']==r['log'] and sha(log)==r['log_sha256']==r['raw_log_sha256'] and not re.search(r'\berror(?:\(|:)',log.read_text())
   assert r['runner_file']==str(runner) and r['runner_sha256']==sha(runner)
   paired.append({'reference':rref,'entire_original_actual_record':r,'raw_log':ref(log),'snapshot':ref(snapshot)})
 assert total==37 and len(paired)==8
 archives=read(check(q['original_tmp_archives']));assert len(archives['aliases'])==q['original_tmp_file_count']==63
 for name,row in archives['aliases'].items():assert Path(name).read_bytes()==check(row).read_bytes()
 assert [r['reference']['file'] for r in peers]==q['preserved_original_component_peer_paths']
 manifest=read(check(q['protected_selected22']['manifest']));assert len(manifest['proof_files'])==1113
 for n,r in manifest['proof_files'].items():assert sha(ROOT/n)==r['sha256']
 inventory=check(q['inventory']);assert sha(inventory)=='67c800179f90c6d152f5934be9187ad4c4b18275e6cd6678a2b2a2f7ff20ca99'
 result={'status':'passed_independent_four_canonical_source37_and_original_semantic_evidence_binding_future23','reviewed_by':'/root/config21_next','started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'errors':[],'readiness':ref(READY),'original_readiness_v1_unchanged':ref(oldready),'four_exact_canonical_source_rows':q['proof_rows'],'all37_canonical_full_source_bodies_equal_original_fully_read_peers':True,'actual_eight_paired_records_and_raw_logs_snapshots':paired,'all63_original_TMP_bytes_unchanged':q['original_tmp_archives'],'canonical_actual_runner_provenance':q['additional_original_runner_provenance'],'entire_original25_9_3_and_precision_peer_bodies_and_review_times':peers,'original_source49_inventory':q['inventory'],'all1113_selected22_source_hashes_exact':True,'new_semantic_decisions_or_original_times_rewritten':False,'whole_exercise_or_material_unit_approved':False,'coverage_complete':False,'limits':['This is a narrow exact canonical-source/actual-evidence binding to the existing independently read25/9/3 theorem components and separate precision proposal. All original scopes, semantic decisions and times remain unchanged.','Eight actual canonical standalone/named executions and raw logs are checked; aggregate23/selection/mapping and publication remain separate.','The later corrected global source50 identity and any further source51 proposal do not retrospectively replace archived49 literal records or prior review times.','The separate fifth continuous-law risk6 source and its fresh semantic peer are not included in this four-source37 binding.','Only new TMP read-only checker/review outputs are written.']}
 with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'review':ref(OUT),'public_theorems':37,'actual_pairs':8}))
if __name__=='__main__':
 try:main()
 except Exception:
  msg=traceback.format_exc()
  if not FAIL.exists():
   with FAIL.open('x') as f:f.write(json.dumps({'status':'failed','started_at_utc':START,'failed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'failure':msg},indent=2)+'\n')
  sys.stderr.write(msg);sys.exit(1)

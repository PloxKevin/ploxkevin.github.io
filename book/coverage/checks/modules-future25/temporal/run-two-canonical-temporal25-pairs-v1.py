from pathlib import Path
from datetime import datetime,timezone
import sys,json,hashlib,time,subprocess
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/modules-future25/temporal'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(ROOT)),'sha256':H(p)}
def readj(p):return json.loads(p.read_text())
prep=BASE/'canonical-source-and-original-history-preparation-v1.json'
assert H(prep)=='292d6223e81880103ce818516d8c60369f6235b9e6a617432d9f33da8ec9cd80'
inputs=readj(prep);selection=readj(ROOT/'reports/full-coverage/checkpoint-24-selection.json')
assert len(selection['proof_files'])==1144
owners=inputs['current24_owner_inventory_sha256_before_after_exact']
assets=readj(ROOT/'book/coverage/inventory-after-correction52.json')['source_sha256']
assets=dict(assets)
for name in ['SafeLearning/style.css','SafeLearning/components.js']:assets[name]=H(ROOT/name)
def guards():
 for f,row in selection['proof_files'].items():assert H(ROOT/f)==row['sha256'],f
 for f,sha in owners.items():assert H(ROOT/f)==sha,f
 for f,sha in assets.items():assert H(ROOT/f)==sha,f
 for f in inputs['source_files']:
  assert H(ROOT/f['source']['file'])==f['source']['sha256']
  assert H(ROOT/f['source_snapshot']['file'])==f['source_snapshot']['sha256']
guards();results=[]
for row in inputs['source_files']:
 source=ROOT/row['source']['file'];module='SafeLearning.'+source.stem
 for kind,command in [('standalone',['lake','env','lean',str(source.relative_to(ROOT/'verification/lean'))]),('named-build',['lake','build',module])]:
  record=BASE/(source.stem+'-'+kind+'-v1.json');log=record.with_suffix('.log')
  assert not record.exists() and not log.exists(),str(record)
  guards();before=H(source);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
  with log.open('xb') as raw:process=subprocess.run(command,cwd=ROOT/'verification/lean',stdout=raw,stderr=subprocess.STDOUT)
  finish=datetime.now(timezone.utc).isoformat();guards()
  body={'status':'passed' if process.returncode==0 else 'failed','actual_exit_code':process.returncode,'actual_command':command,'actual_workdir':str(ROOT/'verification/lean'),'started_at_utc':start,'finished_at_utc':finish,'elapsed_seconds':time.monotonic()-tick,'execution_kind':'actual_future25_canonical_'+kind.replace('-','_'),'source':row['source']['file'],'source_sha256_before':before,'source_sha256_after':H(source),'source_snapshot':row['source_snapshot']['file'],'source_snapshot_sha256':row['source_snapshot']['sha256'],'raw_log':str(log.relative_to(ROOT)),'raw_log_sha256':H(log),'actual_runner':str(Path(__file__).relative_to(ROOT)),'actual_runner_sha256':H(Path(__file__)),'all1144_selected24_sources_exact_before_after':True,'current24_owner_inventory_sha256_before_after_exact':owners,'current52_all31_assets_sha256_before_after_exact':assets,'original_proof_statements_and_bodies_preserved_with_explicit_namespace_aliases':True,'scope':'New genuine uniquely named future25 canonical standalone or named build. All original TMP commands/status/body/time remain historical. No candidate, live owner, source HTML, inventory, kernel/aggregate or publication claim.'}
  record.write_text(json.dumps(body,indent=2)+'\n');results.append({'source':row['source'],'kind':kind,'actual_record':ref(record),'raw_log':ref(log),'source_snapshot':row['source_snapshot'],'actual_exit_code':process.returncode})
  print(json.dumps(results[-1]),flush=True)
  if process.returncode:sys.exit(process.returncode)
guards();ready=BASE/'two-source-nine-export-canonical-paired-readiness25-v1.json';assert not ready.exists()
body={'status':'two_distinct_future25_canonical_sources_actual_standalone_and_named_build_pairs_passed','created_at_utc':datetime.now(timezone.utc).isoformat(),'source_preparation':ref(prep),'source_files':inputs['source_files'],'actual_paired_records':results,'public_export_count':9,'new_source_count':2,'all1144_selected24_sources_exact':True,'current24_owners_and_current52_assets_exact':True,'original_component_peer':inputs['original_component_peer'],'original_whole_answer_b_peer':inputs['original_whole_answer_b_peer'],'original_selected_universal_monotonicity_supplement':inputs['original_selected_universal_monotonicity_supplement'],'scope':'New actual compiler pairs only, preserving original semantic source correspondence. Precise temporal components only; whole(c) and Exercise20 remain pending. No isolated candidate or live/aggregate verification claimed.'}
ready.write_text(json.dumps(body,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'readiness':str(ready.relative_to(ROOT)),'sha256':H(ready)}),flush=True)

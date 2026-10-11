from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,sys,time
ROOT=Path('/home/oxrexkevin/SafetyBased');n=int(sys.argv[1]);p=Path(f'/tmp/foundations-coercivity-margin24-trial{n}.lean');log=p.with_suffix('.log');out=p.with_suffix('.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((ROOT/'reports/full-coverage/checkpoint-22-manifest.json').read_text());assert len(manifest['proof_files'])==1113
held={n:h for n,h in manifest['working_inputs_sha256'].items() if n in {'book/coverage/core.json','book/coverage/modules.json','book/coverage/applied.json','book/coverage/foundations.json'}}
def guard():
 for name,row in manifest['proof_files'].items():assert sha(ROOT/name)==row['sha256'],name
 for name,digest in held.items():assert sha(ROOT/name)==digest,name
 assert sha(ROOT/'book/coverage/inventory.json')=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
 assert sha(ROOT/'SafeLearning/primer-basics.html')=='d6e03363fed45ed19f2747cf29d7c7cfed4c6b163aceeecf93c9fba21321d3d0'
guard();before=sha(p);started=datetime.now(timezone.utc).isoformat();tick=time.monotonic();cmd=['lake','env','lean',str(p)]
with log.open('xb') as f:r=subprocess.run(cmd,cwd=ROOT/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
record={'status':'passed' if r.returncode==0 else 'failed','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT/'verification/lean'),'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'source':str(p),'source_sha256_before':before,'source_sha256_after':sha(p),'raw_log':str(log),'raw_log_sha256':sha(log),'actual_runner':str(Path(__file__)),'actual_runner_sha256':sha(Path(__file__)),'protected_all1113_selected22_sources_exact':True,'held22_owner_ledger_sha256':held,'current_inventory_sha256':'d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41','scope':'Genuine standalone unique TMP trial only; no named/canonical selection or current ledger/source changes inferred.'}
with out.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
guard();print(json.dumps(record));print(log.read_text());sys.exit(r.returncode)

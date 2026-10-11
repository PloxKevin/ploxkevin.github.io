from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,time,subprocess,sys
root=Path('/home/oxrexkevin/SafetyBased');src=Path(sys.argv[1]);stem=src.with_suffix('');log=Path(str(stem)+'.log');record=Path(str(stem)+'.json');snap=Path(str(stem)+'-source.lean');assert not any(p.exists() for p in (log,record,snap))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();selection=json.load(open(root/'reports/full-coverage/checkpoint-24-selection.json'));protected={n:v['sha256'] for n,v in selection['proof_files'].items()}
for n in ('book/coverage/inventory.json','book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied_promotions.py','SafeLearning/verification.html'):protected[n]=sha(root/n)
for n,h in protected.items():assert sha(root/n)==h,n
snap.write_bytes(src.read_bytes());before=sha(src);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();cmd=['lake','env','lean',str(src)]
with log.open('xb') as f:r=subprocess.run(cmd,cwd=root/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
protected_ok=all(sha(root/n)==h for n,h in protected.items());after=sha(src)
out={'status':'passed' if r.returncode==0 and protected_ok and before==after else 'failed','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(root/'verification/lean'),'source':str(src),'source_sha256_before':before,'source_sha256_after':after,'source_snapshot':str(snap),'source_snapshot_sha256':sha(snap),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'raw_log':str(log),'raw_log_sha256':sha(log),'actual_runner':str(Path(__file__)),'actual_runner_sha256':sha(Path(__file__)),'protected_inputs_unchanged':protected_ok,'selected24_proof_sources_checked':len(selection['proof_files']),'protected_sha256':protected,'scope':'Actual standalone TMP Lean execution only; no named build, canonical mapping or whole exercise approval.'}
record.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='protected_sha256'}));raise SystemExit(0 if out['status']=='passed' else r.returncode or 1)

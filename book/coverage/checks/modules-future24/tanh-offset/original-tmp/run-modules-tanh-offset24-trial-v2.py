from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,sys,time
R=Path('/home/oxrexkevin/SafetyBased');W=Path('/tmp/CompleteModulesNNTanhOffset24-wip.lean')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
num=sys.argv[1];assert num.isdecimal();stem=Path('/tmp/modules-tanh-offset24-trial'+num)
source=stem.with_suffix('.lean');record=stem.with_suffix('.json');log=stem.with_suffix('.log')
assert not source.exists() and not record.exists() and not log.exists()
manifest=json.loads((R/'reports/full-coverage/checkpoint-22-manifest.json').read_text())
owners={p:H(R/p) for p in ['book/coverage/core.json','book/coverage/applied.json','book/coverage/foundations.json','book/coverage/modules.json']}
for p,d in manifest['proof_files'].items():assert H(R/p)==d['sha256']
source.write_bytes(W.read_bytes());before=H(source);command=['lake','env','lean',str(source)]
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:p=subprocess.run(command,cwd=R/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
for f,d in manifest['proof_files'].items():assert H(R/f)==d['sha256']
owners_after={f:H(R/f) for f in owners}
row={'status':'passed' if p.returncode==0 else 'failed','actual_exit_code':p.returncode,'actual_command':command,'actual_workdir':str(R/'verification/lean'),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'source':str(source),'source_sha256_before':before,'source_sha256_after':H(source),'raw_log':str(log),'raw_log_sha256':H(log),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(Path(__file__)),'all1113_selected22_sources_exact':True,'observed_owner_ledger_sha256_before':owners,'observed_owner_ledger_sha256_after':owners_after,'owner_byte_identities_unchanged_during_trial':owners==owners_after,'scope':'Genuine standalone unique TMP trial only; source HTML/inventory may be separately serialized by Root, no named/canonical/compiler aggregate or live owner mapping inferred. Root may legitimately install new owner candidates separately; actual before/after ledger hashes are observed without asserting that they must remain equal.'}
assert before==H(source);record.write_text(json.dumps(row,indent=2)+'\n');print(json.dumps({'record':str(record),'record_sha256':H(record),'actual_exit_code':p.returncode,'raw_log':str(log),'raw_log_sha256':H(log)}));sys.exit(p.returncode)

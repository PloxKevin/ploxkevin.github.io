from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/check-pages28-config4-independent-foundations-v1.py');O=Path('/tmp/pages28-config4-independent-foundations-actual-v1.json');L=O.with_suffix('.log')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def j(p):return json.loads(p.read_bytes())
assert not O.exists() and not L.exists()
selected=j(R/'reports/full-coverage/checkpoint-28-selection.json');assets=j(R/'reports/full-coverage/browser-checkpoint-28.json')['source_sha256'];assert len(assets)==31
pins={n:r['sha256'] for n,r in selected['proof_files'].items()};pins.update(assets)
for n in ['book/coverage/inventory.json','book/coverage/material-corrections.json','reports/full-coverage/checkpoint-28-selection.json','book/coverage/checks/root_prepare_pages28_config_v3.py','book/coverage/checks/root_prepare_pages28_config_v4.py']+['book/coverage/'+x+'.json' for x in ['core','foundations','applied','modules','applied-promotions']]:pins[n]=sha(R/n)
before={n:sha(R/n) for n in pins};assert before==pins
cmd=['python3',str(H)];hp=sha(H);start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with L.open('xb') as f:cp=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
after={n:sha(R/n) for n in pins};errors=[n for n in pins if after[n]!=pins[n]]
d={'status':'passed' if cp.returncode==0 and not errors else 'failed','actual_exit_code':cp.returncode,'command':cmd,'cwd':str(R),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'checker':{'file':str(H),'sha256_before':hp,'sha256_after':sha(H)},'runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'raw_log':{'file':str(L),'sha256':sha(L)},'protected_before_sha256':before,'protected_after_sha256':after,'protection_errors':errors,'producer_or_compiler_or_live_source_owner_writer_executed':False}
O.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'actual':str(O),'sha256':sha(O),'actual_exit_code':cp.returncode,'elapsed_seconds':d['elapsed_seconds'],'protection_errors':errors}));raise SystemExit(cp.returncode or int(bool(errors)))

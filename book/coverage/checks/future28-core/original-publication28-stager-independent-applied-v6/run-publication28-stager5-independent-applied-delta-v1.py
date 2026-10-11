from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time
ROOT=Path('/home/oxrexkevin/SafetyBased')
CHECKER=Path('/tmp/check-publication28-stager5-independent-applied-delta-v1.py')
ACTUAL=Path('/tmp/publication28-stager5-independent-applied-delta-actual-v1.json');LOG=ACTUAL.with_suffix('.log')
assert not ACTUAL.exists() and not LOG.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
helpers={str(CHECKER):sha(CHECKER),str(Path(__file__)):sha(__file__),'book/coverage/checks/root_stage_publication28_v5.py':sha(ROOT/'book/coverage/checks/root_stage_publication28_v5.py')}
selection=json.loads((ROOT/'reports/full-coverage/checkpoint-28-selection.json').read_bytes())
names=list(selection['proof_files'])+['book/coverage/'+n+'.json' for n in ['core','foundations','applied','applied-promotions','modules']]+['book/coverage/inventory.json','book/coverage/material-corrections.json']+[p.relative_to(ROOT).as_posix() for p in (ROOT/'SafeLearning').iterdir() if p.suffix in {'.html','.css','.js'}]
before={n:sha(ROOT/n) for n in names}
command=['/usr/bin/python3',str(CHECKER)];started=datetime.now(timezone.utc).isoformat();tick=time.perf_counter()
p=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
with LOG.open('xb') as f:f.write(p.stdout)
after={n:sha(ROOT/n) for n in names};after_helpers={n:sha(n if Path(n).is_absolute() else ROOT/n) for n in helpers}
errors=[n for n in before if before[n]!=after[n]]+[n for n in helpers if helpers[n]!=after_helpers[n]]
d={'status':'passed' if p.returncode==0 and not errors else 'failed','actual_exit_code':p.returncode,'actual_command':command,'actual_workdir':str(ROOT),'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.perf_counter()-tick,'helper_sha256_before':helpers,'helper_sha256_after':after_helpers,'log':str(LOG),'log_sha256':sha(LOG),'protection_errors':errors,'protected_sources':1186,'native_producer_or_actual_pub_git_invoked':False,'temporary_git_and_synthetic_prepare_stage_only':True}
with ACTUAL.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'actual':str(ACTUAL),'actual_exit_code':p.returncode,'protection_errors':errors,'elapsed_seconds':d['elapsed_seconds'],'raw':str(LOG)}))
raise SystemExit(p.returncode or bool(errors))

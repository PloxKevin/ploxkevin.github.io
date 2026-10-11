from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,shutil,subprocess,time,sys
ROOT=Path('/home/oxrexkevin/SafetyBased')
source=Path(sys.argv[1]);snapshot=Path(sys.argv[2]);log=snapshot.with_suffix('.log');record=snapshot.with_suffix('.json')
assert source.is_file() and source.parent==snapshot.parent==Path('/tmp')
assert all(not p.exists() for p in [snapshot,log,record])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
selection=json.loads((ROOT/'reports/full-coverage/checkpoint-23-selection.json').read_text())
manifest=json.loads((ROOT/'reports/full-coverage/checkpoint-23-manifest.json').read_text())
protected={n:r['sha256'] for n,r in selection['proof_files'].items()}
protected.update({n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/modules.json','book/coverage/applied.json','book/coverage/applied-promotions.json','book/coverage/inventory.json']})
def guard():
    for n,h in protected.items():assert sha(ROOT/n)==h,n
guard();shutil.copyfile(source,snapshot);before=sha(snapshot)
cmd=['lake','env','lean',str(snapshot)];started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:result=subprocess.run(cmd,cwd=ROOT/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
guard();assert sha(snapshot)==before
record.write_text(json.dumps({'status':'passed' if result.returncode==0 else 'failed','actual_exit_code':result.returncode,
    'actual_command':cmd,'actual_workdir':str(ROOT/'verification/lean'),'started_at_utc':started,
    'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,
    'source_sha256_before':before,'source_sha256_after':sha(snapshot),'source_snapshot':str(snapshot),
    'log':str(log),'log_sha256':sha(log),'actual_trial_runner':str(Path(__file__)),
    'actual_trial_runner_sha256':sha(Path(__file__)),'protected_selected23_sources':1131,
    'scope':'Actual TMP trial only; no canonical build, kernel replay, selection or whole-unit completion inferred.',
    'coverage_complete':False},indent=2)+'\n')
print(record.read_text());raise SystemExit(result.returncode)

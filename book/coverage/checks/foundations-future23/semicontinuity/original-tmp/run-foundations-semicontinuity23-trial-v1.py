from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,sys,time
ROOT=Path('/home/oxrexkevin/SafetyBased');N=int(sys.argv[1]);TMP=Path('/tmp')
SOURCE=TMP/f'foundations-semicontinuity23-trial{N}.lean'
RECORD=TMP/f'foundations-semicontinuity23-trial{N}.json'
LOG=TMP/f'foundations-semicontinuity23-trial{N}.log'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not RECORD.exists() and not LOG.exists()
manifest=json.loads((ROOT/'reports/full-coverage/checkpoint-22-manifest.json').read_text())
protected={n:r['sha256'] for n,r in manifest['proof_files'].items()}
protected.update({n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in {'book/coverage/inventory.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/core.json'}})
def guard():
 for n,h in protected.items():assert sha(ROOT/n)==h,n
guard();before=sha(SOURCE);command=['lake','env','lean',str(SOURCE)];start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with LOG.open('xb') as f:result=subprocess.run(command,cwd=ROOT/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();after=sha(SOURCE);guard()
data={'status':'passed' if result.returncode==0 else 'failed','actual_exit_code':result.returncode,'command':command,'actual_workdir':str(ROOT/'verification/lean'),'source':str(SOURCE),'source_sha256_before':before,'source_sha256_after':after,'started_at_utc':start,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-t,'raw_log':str(LOG),'raw_log_sha256':sha(LOG),'actual_runner':str(Path(__file__)),'actual_runner_sha256':sha(Path(__file__)),'all1113_selected22_sources_exact':True,'current48_assets_inventory_and_four_working22_ledgers_exact':True,'scope':'Genuine standalone TMP source only; no canonical/named execution, owner ledger or coverage mutation.'}
with RECORD.open('x') as f:f.write(json.dumps(data,indent=2)+'\n')
print(json.dumps(data));print(LOG.read_text());assert before==after;sys.exit(result.returncode)

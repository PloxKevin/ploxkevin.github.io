from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,sys,time
ROOT=Path('/home/oxrexkevin/SafetyBased');N=int(sys.argv[1]);TMP=Path('/tmp')
SOURCE=TMP/f'foundations-linalg-refresher23-trial{N}.lean'
RECORD=TMP/f'foundations-linalg-refresher23-trial{N}.json'
LOG=TMP/f'foundations-linalg-refresher23-trial{N}.log'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not RECORD.exists() and not LOG.exists()
manifest=json.loads((ROOT/'reports/full-coverage/checkpoint-22-manifest.json').read_text())
protected={n:r['sha256'] for n,r in manifest['proof_files'].items()}
old_assets={n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(old_assets)==31
current_assets=dict(old_assets)
current_assets['SafeLearning/cmdp.html']='5a503475452eacbeb8d5b8f4b3dd846bc3d88ff6817bd900a3cf3b2e2b23f6e9'
protected.update(current_assets)
protected['book/coverage/inventory.json']='67c800179f90c6d152f5934be9187ad4c4b18275e6cd6678a2b2a2f7ff20ca99'
protected.update({n:h for n,h in manifest['working_inputs_sha256'].items() if n in {'book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/core.json'}})
for n,h in old_assets.items():assert sha(ROOT/'reports/full-coverage/checkpoint-22'/n)==h
observed_new_inventory=json.loads((ROOT/'book/coverage/inventory.json').read_text())
assert observed_new_inventory['source_sha256']['SafeLearning/cmdp.html']==current_assets['SafeLearning/cmdp.html']

def guard():
 for n,h in protected.items():assert sha(ROOT/n)==h,n
guard();before=sha(SOURCE);command=['lake','env','lean',str(SOURCE)];start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with LOG.open('xb') as f:result=subprocess.run(command,cwd=ROOT/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();after=sha(SOURCE);guard()
data={'status':'passed' if result.returncode==0 else 'failed','actual_exit_code':result.returncode,'command':command,'actual_workdir':str(ROOT/'verification/lean'),'source':str(SOURCE),'source_sha256_before':before,'source_sha256_after':after,'started_at_utc':start,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-t,'raw_log':str(LOG),'raw_log_sha256':sha(LOG),'actual_runner':str(Path(__file__)),'actual_runner_sha256':sha(Path(__file__)),'all1113_selected22_sources_exact':True,'frozen22_all31_source48_assets_exact':True,'observed_new_source49_all31_assets_inventory_and_four_held22_working_ledgers_exact':True,'observed_source49_inventory_sha256':protected['book/coverage/inventory.json'],'current_source49_delta':{'SafeLearning/cmdp.html':current_assets['SafeLearning/cmdp.html']},'scope':'Genuine standalone TMP source only; old31 source48 assets bound to frozen22 snapshots, current Root corrected source49 assets/inventory separately hash-pinned. No Root apply completion, canonical/named execution, owner ledger or coverage mutation is claimed.'}
with RECORD.open('x') as f:f.write(json.dumps(data,indent=2)+'\n')
print(json.dumps(data));print(LOG.read_text());assert before==after;sys.exit(result.returncode)

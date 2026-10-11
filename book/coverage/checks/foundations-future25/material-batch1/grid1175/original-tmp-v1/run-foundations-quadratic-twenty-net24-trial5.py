from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time
ROOT=Path('/home/oxrexkevin/SafetyBased');SOURCE=Path('/tmp/foundations-quadratic-twenty-net24-trial5.lean');OUT=SOURCE.with_suffix('.json');LOG=SOURCE.with_suffix('.log');SNAP=Path('/tmp/foundations-quadratic-twenty-net24-trial5-source.lean');assert not OUT.exists()and not LOG.exists()and not SNAP.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());m=read(ROOT/'reports/full-coverage/checkpoint-23-manifest.json')
proofs={n:r['sha256']for n,r in m['proof_files'].items()};assert len(proofs)==1131
frozenassets={n:h for n,h in m['working_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(frozenassets)==31
assets=dict(frozenassets);assets['SafeLearning/nn-in-the-loop.html']='1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'
owners={n:m['working_inputs_sha256'][n]for n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json','book/coverage/inventory.json']}
owners['book/coverage/inventory.json']='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
def guard():
 for n,h in {**proofs,**assets,**owners}.items():assert H(ROOT/n)==h,n
 for n,h in {**proofs,**frozenassets}.items():assert H(ROOT/'reports/full-coverage/checkpoint-23'/n)==h,n
guard();before=H(SOURCE);SNAP.write_bytes(SOURCE.read_bytes());start=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['lake','env','lean',str(SOURCE)]
r=subprocess.run(cmd,cwd=ROOT/'verification/lean',stdout=subprocess.PIPE,stderr=subprocess.STDOUT);LOG.write_bytes(r.stdout);guard()
OUT.write_text(json.dumps({'status':'passed'if r.returncode==0 else'failed','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT/'verification/lean'),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'source':str(SOURCE),'source_sha256_before':before,'source_sha256_after':H(SOURCE),'source_snapshot':str(SNAP),'source_snapshot_sha256':H(SNAP),'raw_log':str(LOG),'raw_log_sha256':H(LOG),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(Path(__file__)),'selected23_proof_count':1131,'selected23_and_frozen_sources_and31_assets_before_after_exact':True,'current23_owner_current52_inventory_sha256':owners,'current52_asset_sha256':assets,'frozen23_original_asset_sha256':frozenassets,'scope':'Genuine distinct TMP-only scalar grid proof trial; no named/canonical build, candidate or current live mapping.'},indent=2)+'\n')
print(r.stdout.decode());print(OUT.read_text());raise SystemExit(r.returncode)

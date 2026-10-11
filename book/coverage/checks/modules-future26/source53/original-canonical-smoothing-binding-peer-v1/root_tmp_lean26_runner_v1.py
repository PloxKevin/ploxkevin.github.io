from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,time,subprocess,sys
root=Path('/home/oxrexkevin/SafetyBased');source=Path(sys.argv[1]);record=Path(sys.argv[2]);log=record.with_suffix('.log');snapshot=record.with_name(record.stem+'-source.lean')
assert source.is_absolute() and source.is_file() and not record.exists() and not log.exists() and not snapshot.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((root/'reports/full-coverage/checkpoint-24-manifest.json').read_text());assert len(m['proof_files'])==1144
held={n:r['sha256'] for n,r in m['proof_files'].items()};held.update({n:h for n,h in m['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in {'book/coverage/'+o+'.json' for o in ['core','foundations','applied','modules','applied-promotions']}})
def guard():
 for n,h in held.items():assert sha(root/n)==h,n
 assert sha(root/'book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
guard();snapshot.write_bytes(source.read_bytes());before=sha(source);command=['lake','env','lean',str(source)];started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:result=subprocess.run(command,cwd=root/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();after=sha(source);guard()
out=dict(status='passed_actual_tmp_lean_only' if result.returncode==0 and before==after else 'failed_actual_tmp_lean',actual_exit_code=result.returncode,actual_command=command,actual_workdir=str(root/'verification/lean'),started_at_utc=started,finished_at_utc=finished,elapsed_seconds=time.monotonic()-tick,source=str(source),source_sha256_before=before,source_sha256_after=after,source_unchanged=before==after,source_snapshot=str(snapshot),source_snapshot_sha256=sha(snapshot),raw_log=str(log),raw_log_sha256=sha(log),original_actual_runner={'file':str(Path(__file__)),'sha256':sha(Path(__file__))},unchanged_baseline24_selected_proof_sources=1144,unchanged_current52_book_assets=31,unchanged_current52_held_live_owners=5,canonical_installation_or_aggregate_verification_claimed=False)
with record.open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps(out));raise SystemExit(result.returncode if before==after else 1)

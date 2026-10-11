from pathlib import Path
import json,hashlib,subprocess,datetime,time,shutil
ROOT=Path('/home/oxrexkevin/SafetyBased')
src=Path('/tmp/CompleteAppliedFiniteMixtureMaterial24.lean')
prefix=Path('/tmp/applied-finite-mixture-material24-trial1')
record=prefix.with_suffix('.json');log=prefix.with_suffix('.log');snapshot=Path(str(prefix)+'-source.lean')
assert not any(p.exists() for p in (record,log,snapshot))
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
shutil.copyfile(src,snapshot);before=h(src);cmd=['lake','env','lean',str(src)];cwd=ROOT/'verification/lean'
start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic()
with log.open('wb') as f:r=subprocess.run(cmd,cwd=cwd,stdout=f,stderr=subprocess.STDOUT)
finish=datetime.datetime.now(datetime.timezone.utc).isoformat()
M=json.loads((ROOT/'reports/full-coverage/checkpoint-22-manifest.json').read_text())
assert len(M['proof_files'])==1113
for p,d in M['proof_files'].items():assert h(ROOT/p)==d['sha256'],p
out={'kind':'actual_tmp_standalone_lean_compilation','status':'passed' if r.returncode==0 else 'failed','actual_command':cmd,'actual_workdir':str(cwd),'actual_exit_code':r.returncode,'source':str(src),'source_sha256_before':before,'source_sha256_after':h(src),'source_unchanged':before==h(src),'source_snapshot':str(snapshot),'source_snapshot_sha256':h(snapshot),'started_at_utc':start,'finished_at_utc':finish,'elapsed_seconds':time.monotonic()-t,'log':str(log),'log_sha256':h(log),'actual_runner':str(Path(__file__)),'actual_runner_sha256':h(__file__),'protected_selected22_sources_exact':1113,'scope':'TMP-only future24 actual standalone; no named/canonical build, ledger amendment, selection, aggregate or current23 coverage assertion.'}
record.write_text(json.dumps(out,indent=2)+'\n');print(log.read_text());print(json.dumps({'record':str(record),'actual_exit_code':r.returncode,'source_sha256':h(src)}));raise SystemExit(r.returncode)

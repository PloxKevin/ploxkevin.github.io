from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/check-modules29-current65-two-source-final-mapping-independent-applied-v1.py');C=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json');O=Path('/tmp/modules29-current65-final-mapping-independent-applied-actual-v1.json');L=O.with_suffix('.log')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n):p=Path(n);return p if p.is_absolute() else R/p
assert not O.exists() and not L.exists();ctx=json.loads(C.read_bytes());held={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
for n,h in held.items():assert sha(path(n))==h
before={str(H):sha(H),str(Path(__file__)):sha(__file__)};started=datetime.now(timezone.utc).isoformat();t=time.monotonic();cmd=['python3',str(H)]
with L.open('xb') as f:p=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
errors=[n for n,h in held.items() if sha(path(n))!=h]
d={'status':'passed_actual_independent_modules29_current65_final_mapping_reader' if p.returncode==0 and not errors else 'failed_actual_independent_modules29_current65_final_mapping_reader','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(R),'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':{n:sha(n) for n in before},'log':str(L),'log_sha256':sha(L),'protection_errors':errors,'compiler_source_owner_selection_or_publication_written':False,'coverage_complete':False}
with O.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps(d));raise SystemExit(p.returncode or bool(errors))

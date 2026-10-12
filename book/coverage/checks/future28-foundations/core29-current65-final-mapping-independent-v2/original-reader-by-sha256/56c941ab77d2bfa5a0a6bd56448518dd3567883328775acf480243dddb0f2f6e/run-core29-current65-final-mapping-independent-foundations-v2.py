from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/review-core29-current65-final-mapping-independent-foundations-v2.py');N=Path('/tmp/core29-current65-final-mapping-independent-foundations-actual-v2.json');L=N.with_suffix('.log')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not N.exists() and not L.exists();ctx=json.loads(Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json').read_bytes());pins={}
for k in ('pins_sha256','held_current_source_sha256','owners_sha256'):
 for n,h in ctx[k].items():assert n not in pins or pins[n]==h;pins[n]=h
before={n:sha(R/n)for n in pins};assert before==pins
cmd=['python3',str(H)];hp=sha(H);start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with L.open('xb') as f:out=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
after={n:sha(R/n)for n in pins};errors=[n for n in pins if after[n]!=pins[n]]
d={'status':'passed' if out.returncode==0 and not errors else 'failed','actual_exit_code':out.returncode,'actual_command':cmd,'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':{str(H):hp},'helper_sha256_after':{str(H):sha(H)},'log':str(L),'log_sha256':sha(L),'protected_inputs_sha256':pins,'protected_before_sha256':before,'protected_after_sha256':after,'protection_errors':errors,'compiler_started':False,'live_owner_source_selected_or_publication_written':False}
N.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'native':str(N),'native_sha256':sha(N),'actual_exit_code':out.returncode,'elapsed_seconds':d['elapsed_seconds'],'raw_log_sha256':sha(L),'protection_errors':errors}));raise SystemExit(out.returncode or int(bool(errors)))

from pathlib import Path
from datetime import datetime,timezone
import subprocess,time,json,hashlib
C=Path('/tmp/check-leakyqc30-independent-applied29-v2.py');O=Path('/tmp/leakyqc30-independent-applied-actual29-v2.json');L=O.with_suffix('.log')
assert not O.exists() and not L.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
started=datetime.now(timezone.utc).isoformat();h=sha(C);t=time.monotonic()
r=subprocess.run(['python3',str(C)],cwd='/home/oxrexkevin/SafetyBased',capture_output=True);L.write_bytes(r.stdout+r.stderr)
O.write_text(json.dumps({'status':'passed' if r.returncode==0 else 'failed','actual_exit_code':r.returncode,'actual_command':['python3',str(C)],'actual_workdir':'/home/oxrexkevin/SafetyBased','started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':{str(C):h},'helper_sha256_after':{str(C):sha(C)},'raw_log':str(L),'raw_log_sha256':sha(L),'semantic_read_vs_checker_scope':'Full semantic decisions authored by independent reader; checker validates exact source/literal/provenance and held current context. No Lean rerun.','protection_errors':[]},indent=2)+'\n')
print(O, r.returncode, sha(O));print((r.stdout+r.stderr).decode());raise SystemExit(r.returncode)

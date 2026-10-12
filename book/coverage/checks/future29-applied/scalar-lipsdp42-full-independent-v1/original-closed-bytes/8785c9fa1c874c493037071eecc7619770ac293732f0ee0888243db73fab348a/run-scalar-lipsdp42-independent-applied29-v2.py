from pathlib import Path
from datetime import datetime,timezone
import subprocess,time,json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');C=Path('/tmp/check-scalar-lipsdp42-independent-applied29-v2.py')
O=Path('/tmp/scalar-lipsdp42-independent-applied-actual29-v2.json');L=O.with_suffix('.log')
CTX=Path('/tmp/root_tmp_lean_current64_owner28_context_v1.json')
assert not O.exists() and not L.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
ctx=json.loads(CTX.read_bytes());held={}
for m in (ctx['pins_sha256'],ctx['held_current_source_sha256'],ctx['owners_sha256']):
 for n,h in m.items():assert n not in held or held[n]==h;held[n]=h
def path(n):return Path(n)if Path(n).is_absolute()else R/n
for n,h in held.items():assert sha(path(n))==h,n
before={str(C):sha(C),str(Path(__file__)):sha(Path(__file__))}
started=datetime.now(timezone.utc).isoformat();t=time.monotonic()
r=subprocess.run(['python3',str(C)],cwd=R,capture_output=True)
with L.open('xb')as f:f.write(r.stdout+r.stderr)
errors=[n for n,h in held.items()if not path(n).is_file()or sha(path(n))!=h]
record={'status':'passed'if r.returncode==0 and not errors else 'failed','actual_exit_code':r.returncode,
 'actual_command':['python3',str(C)],'actual_workdir':str(R),'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),
 'elapsed_seconds':time.monotonic()-t,'helper_sha256_before':before,'helper_sha256_after':{n:sha(n)for n in before},
 'raw_log':str(L),'raw_log_sha256':sha(L),'actual_source64_installed28_context':{'file':str(CTX),'sha256':sha(CTX)},
 'protection_errors':errors,'no_compiler_or_parser_started':True,
 'scope':'Independent full semantic reading; measured checker verifies full source/literal/native histories/current guards, not fresh Lean or Source65 parser.'}
with O.open('x')as f:f.write(json.dumps(record,indent=2)+'\n')
print(O,r.returncode,sha(O));print((r.stdout+r.stderr).decode());raise SystemExit(r.returncode or bool(errors))

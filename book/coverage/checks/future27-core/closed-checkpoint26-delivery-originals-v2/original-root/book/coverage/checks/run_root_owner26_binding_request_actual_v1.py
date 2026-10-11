"""Actual wrapper for authorized request preparation only; no binding/install run."""
from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time
ROOT=Path(__file__).resolve().parents[3]
HELPER='book/coverage/checks/create_root_owner26_binding_request_v3.py'
EXPECTED='c6a2191e575a4ecd54c58749a532f396be74850a8f8f0944e5df953bc1fa1681'
PEER='book/coverage/checks/future26-core/owner26-integration-and-binding-helpers-independent-modules-code-review-v1.json'
PS='5dda8c13fe95e89ebe628155e49f439076cc8f72885d026c7d79aed13c685e31'
CORE='reports/full-coverage/finalize-root-core26-offer-execution-v1.json'
CS='90700718b348314c1fdd6f10b2b91eb0581cce3363919a25a695e3846a152306'
OUT='reports/full-coverage/prepare-owner26-binding-request-execution-v1.json';LOG=OUT.removesuffix('.json')+'.log'
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
assert sha(HELPER)==EXPECTED and sha(PEER)==PS and sha(CORE)==CS
assert not (ROOT/OUT).exists() and not (ROOT/LOG).exists()
core=json.loads((ROOT/CORE).read_text());assert type(core['actual_exit_code'])is int and core['actual_exit_code']==0
command=['python3',HELPER,'--independent-peer',PEER,'--peer-sha256',PS,'--core-finalization-execution',CORE,'--core-finalization-execution-sha256',CS,'--root-authorized-binding-request-preparation']
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();before={HELPER:sha(HELPER)}
with (ROOT/LOG).open('xb') as f:r=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
record={'status':'passed_actual_request_preparation' if r.returncode==0 else 'failed_actual_request_preparation','actual_exit_code':r.returncode,'actual_command':command,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':{HELPER:sha(HELPER)},'log':LOG,'log_sha256':sha(LOG),'actual_runner':{'file':str(Path(__file__).relative_to(ROOT)),'sha256':sha(str(Path(__file__).relative_to(ROOT)))},'scope':'Genuine authorized NEW request preparation only. Binder validation was read-only; no production binding manifest, integration, global validator, Lean, publication or Git execution.'}
with (ROOT/OUT).open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps(record));raise SystemExit(r.returncode)

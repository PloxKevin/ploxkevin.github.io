from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,subprocess,sys,time
R=Path('/home/oxrexkevin/SafetyBased');HELP=Path('/tmp/prepare-applied28-source60-identity-candidate-v2.py');REC=Path('/tmp/applied28-source60-identity-candidate-preparation-actual-v1.json');LOG=REC.with_suffix('.log');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert not REC.exists()and not LOG.exists();before=H(HELP);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with LOG.open('xb')as f:r=subprocess.run([sys.executable,str(HELP)],cwd=R,stdout=f,stderr=subprocess.STDOUT)
out={'status':'passed_actual_isolated_candidate_preparation'if r.returncode==0 else'failed_actual_isolated_candidate_preparation','actual_exit_code':r.returncode,'actual_command':[sys.executable,str(HELP)],'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':{str(HELP):before},'helper_sha256_after':{str(HELP):H(HELP)},'log':str(LOG),'log_sha256':H(LOG),'live_owner_or_proof_source_or_publication_written':False}
REC.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));sys.exit(r.returncode)

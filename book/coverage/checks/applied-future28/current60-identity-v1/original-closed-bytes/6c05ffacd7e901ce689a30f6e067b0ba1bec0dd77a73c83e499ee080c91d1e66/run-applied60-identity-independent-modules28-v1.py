from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');HELPER=Path('/tmp/review-applied60-identity-independent-modules28-v1.py')
OUT=Path('/tmp/applied60-identity-independent-modules28-actual-v1.json');LOG=OUT.with_suffix('.log');READER=Path('/tmp/applied60-identity-independent-modules28-reader-v1.json')
assert not OUT.exists() and not LOG.exists() and not READER.exists()
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':H(p),'bytes':Path(p).stat().st_size}
selection=R/'reports/full-coverage/checkpoint-27-selection.json'
assert H(selection)=='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
assert H(R/'book/coverage/inventory.json')=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
s=json.loads(selection.read_bytes());proofs={R/k:v['sha256']for k,v in s['proof_files'].items()};assert len(proofs)==1175
assets={p:H(p)for p in (R/'SafeLearning').glob('*')if p.is_file()};assert len(assets)==31
held={p:H(p)for p in [HELPER,Path(__file__),selection,R/'book/coverage/inventory.json',R/'book/inventory_claims.py',R/'book/coverage/material-corrections.json']}
held.update(assets);held.update(proofs)
held.update({R/'book/coverage'/n:H(R/'book/coverage'/n)for n in ('modules.json','core.json','foundations.json','applied.json','applied-promotions.json')})
for p,h in held.items():assert H(p)==h
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic();command=['python3',str(HELPER)]
with LOG.open('xb')as f:run=subprocess.run(command,cwd=R,stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();errors=[str(p)for p,h in held.items()if H(p)!=h]
out={'status':'passed_actual_independent_applied60_candidate_mechanics_and_protection'if run.returncode==0 and not errors else 'failed_actual_independent_applied60_candidate_mechanics_or_protection','actual_exit_code':run.returncode,'actual_command':command,'actual_workdir':str(R),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,'helper':ref(HELPER),'runner':ref(Path(__file__)),'raw_log':ref(LOG),'reader':ref(READER)if READER.exists()else None,'protected_selected27_proof_sources':1175,'protected_current60_assets':31,'protected_installed27_owner_ledgers':5,'protection_errors':errors,'source_owner_selection_bytes_unchanged':not errors,'live_owner_or_proof_source_or_publication_written':False,'coverage_complete':False}
OUT.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));raise SystemExit(0 if run.returncode==0 and not errors else 1)

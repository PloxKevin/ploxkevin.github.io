from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/check-pages28-config1-independent-foundations-v1.py');O=Path('/tmp/pages28-config1-independent-foundations-actual-v1.json');L=O.with_suffix('.log')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def j(p):return json.loads(p.read_bytes())
assert not O.exists()and not L.exists()
ready=j(R/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json');ready2=j(R/'book/coverage/checks/future28-core/current60-commissioning17-canonical-pair-v1/actual-current60-commissioning17-canonical-paired-readiness28-v1.json')
mutable={'book/coverage/'+n+'.json'for n in ['core','foundations','applied','modules','applied-promotions']}
pins={n:s for n,s in ready['protected_inputs_sha256'].items()if n not in mutable}
for row in ready['sources']+ready2['sources']:pins[row['canonical_source']]=row['original_tmp_source']['sha256']
for n in ['book/coverage/checks/root_prepare_pages28_config_v1.py','book/coverage/lean_names.py']:pins[n]=sha(R/n)
before={n:sha(R/n)for n in pins};assert before==pins
cmd=['python3',str(H)];hp=sha(H);start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with L.open('xb')as f:p=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-t;after={n:sha(R/n)for n in pins};errors=[n for n,s in pins.items()if after[n]!=s]
d={'status':'passed'if p.returncode==0 and not errors else'failed','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':end,'elapsed_seconds':elapsed,'checker':{'file':str(H),'sha256':hp},'checker_sha256_before':hp,'checker_sha256_after':sha(H),'runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'raw_log':str(L),'raw_log_sha256':sha(L),'protected_before_sha256':before,'protected_after_sha256':after,'protection_errors':errors,'five_mutable_owners_excluded_for_root_authorized_concurrent_integration':True,'production_selector_retention_outputs_or_compiler_written':False}
with O.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'actual_record':str(O),'sha256':sha(O),'actual_exit_code':p.returncode,'elapsed_seconds':elapsed,'raw_log_sha256':sha(L),'protection_errors':errors}))
raise SystemExit(p.returncode or int(bool(errors)))

from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');helper=ROOT/'book/coverage/checks/root_apply_source56_60_v2.py';actual=Path('/tmp/source56-60-helper2-readonly-ready-independent-foundations28-actual-v1.json');log=actual.with_suffix('.log');snapshot=Path('/tmp/source56-60-helper2-readonly-ready-independent-foundations28-source-v1.py');assert not actual.exists()and not log.exists()and not snapshot.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
sel=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json');assets=read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256'];owners={r['destination']:r['candidate']['sha256']for r in read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']};held={n:r['sha256']for n,r in sel['proof_files'].items()};held.update(assets);held.update(owners);held.update({'book/coverage/inventory.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf','book/coverage/material-corrections.json':'21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'})
for n,h in held.items():assert sha(ROOT/n)==h,n
before=sha(helper);assert before=='47549e54160582325e8d340db2a803d9df1a459999e5fb388bd155fb2606f389';snapshot.write_bytes(helper.read_bytes());assert sha(snapshot)==before
cmd=['python3',str(helper),'--closure-sha256','43bdd1aaa2f93b358a0697ffeb4ae29ffa5c2d18784834cf9cc370929924d71d'];start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb')as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
errors=[]
for n,h in held.items():
 if sha(ROOT/n)!=h:errors.append(n)
if sha(helper)!=before:errors.append('helper changed')
if (ROOT/'reports/full-coverage/source56-60-corrections-application-v1.json').exists()or(ROOT/'reports/full-coverage/source-history/approved-corrections56-60-20261011').exists():errors.append('producer output/history exists')
a={'scope':'Genuine read-only ready CLI, no --apply. Full five cumulative parsers may write only temporary directories. Code semantic guard-order approval remains separate.','actual_exit_code':r.returncode,'actual_command':cmd,'actual_workdir':str(ROOT),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'helper_sha256_before':before,'helper_sha256_after':sha(helper),'original_helper_source_snapshot':{'file':str(snapshot),'sha256':sha(snapshot)},'actual_runner':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},'raw_log':str(log),'raw_log_sha256':sha(log),'protected_selected27_proof_sources':1175,'unchanged_current55_book_assets':31,'unchanged_installed27_live_owners':5,'protection_errors':errors,'canonical_source_owner_proof_or_publication_mutation_claimed':False}
with actual.open('x')as f:json.dump(a,f,indent=2);f.write('\n')
print(json.dumps(a));assert errors==[];raise SystemExit(r.returncode)

from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');HELPER=Path('/tmp/prepare-modules-current60-owner28-durable-pair-bound-v3.py')
OUT=Path('/tmp/modules28-current60-durable-pair-bound-preparation-actual-v1.json');LOG=OUT.with_suffix('.log');READER=R/'book/coverage/checks/modules-future28/current60-pair-bound-v1/modules28-current60-pair-binding-preparation-v1.json'
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
prior=R/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json'
a=json.loads(prior.read_bytes());held[prior]=H(prior)
for r in a['sources']:held[R/r['canonical_source']]=r['original_tmp_source']['sha256']
for r in a['actual_paired_records']:
 for k in ('actual_record','raw_log','source_snapshot'):held[R/r[k]['file']]=r[k]['sha256']
for p in [R/'reports/full-coverage/current60-canonical-pairs28-execution-v1.json',R/'reports/full-coverage/current60-canonical-pairs28-execution-v1.log',R/'book/coverage/checks/run_root28_current60_commissioning17_canonical_pair_v1.py',Path('/tmp/root28-current60-commissioning17-canonical-plan-v1.json')]:held[p]=H(p)
commission=R/'book/coverage/checks/future28-core/current60-commissioning17-canonical-pair-v1/actual-current60-commissioning17-canonical-paired-readiness28-v1.json'
d=json.loads(commission.read_bytes());held[commission]=H(commission)
for r in d['sources']:held[R/r['canonical_source']]=r['original_tmp_source']['sha256']
for r in d['actual_paired_records']:
 for k in ('actual_record','raw_log','source_snapshot'):held[R/r[k]['file']]=r[k]['sha256']
for p,h in held.items():assert H(p)==h
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic();command=['python3',str(HELPER)]
with LOG.open('xb')as f:run=subprocess.run(command,cwd=R,stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();errors=[str(p)for p,h in held.items()if H(p)!=h]
out={'status':'passed_actual_independent_modules28_durable_pair_bound_preparation_and_protection'if run.returncode==0 and not errors else 'failed_actual_independent_modules28_durable_pair_bound_preparation_or_protection','actual_exit_code':run.returncode,'actual_command':command,'actual_workdir':str(R),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,'helper':ref(HELPER),'runner':ref(Path(__file__)),'raw_log':ref(LOG),'reader':ref(READER)if READER.exists()else None,'protected_selected27_proof_sources':1175,'protected_current60_assets':31,'protected_installed27_owner_ledgers':5,'protection_errors':errors,'source_owner_selection_bytes_unchanged':not errors,'live_owner_or_proof_source_or_publication_written':False,'coverage_complete':False}
OUT.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));raise SystemExit(0 if run.returncode==0 and not errors else 1)

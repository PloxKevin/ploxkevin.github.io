from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased')
C=Path('/tmp/check-modules28-current60-final-pair-bound-independent-applied-v2.py')
O=Path('/tmp/modules28-current60-final-pair-bound-independent-applied-actual-v2.json')
L=O.with_suffix('.log')
F=Path('/tmp/modules28-current60-final-pair-bound-independent-applied-findings-v2.json')
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':H(p)}
assert not O.exists() and not L.exists() and not F.exists()
selection=R/'reports/full-coverage/checkpoint-27-selection.json'
assert H(selection)=='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
s=json.loads(selection.read_bytes());held={R/n:d['sha256'] for n,d in s['proof_files'].items()};assert len(held)==1175
held.update({p:H(p) for p in (R/'SafeLearning').iterdir() if p.is_file()})
assert len([p for p in (R/'SafeLearning').iterdir() if p.is_file()])==31
for n in ('core','foundations','applied','applied-promotions','modules','inventory','material-corrections'):p=R/'book/coverage'/f'{n}.json';held[p]=H(p)
assert H(R/'book/coverage/inventory.json')=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
for n in ('book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json','book/coverage/checks/future28-core/current60-commissioning17-canonical-pair-v1/actual-current60-commissioning17-canonical-paired-readiness28-v1.json'):
    p=R/n;held[p]=H(p);d=json.loads(p.read_bytes())
    for row in d['sources']:held[R/row['canonical_source']]=row['original_tmp_source']['sha256']
    for row in d['actual_paired_records']:
        for k in ('actual_record','raw_log','source_snapshot'):held[R/row[k]['file']]=row[k]['sha256']
held[C]=H(C);held[Path(__file__)]=H(Path(__file__));held[selection]=H(selection)
for p,h in held.items():assert H(p)==h
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();command=['python3',str(C)]
with L.open('xb')as f:r=subprocess.run(command,cwd=R,stdout=f,stderr=subprocess.STDOUT)
finish=datetime.now(timezone.utc).isoformat();errors=[str(p) for p,h in held.items() if H(p)!=h]
d={'status':'passed_actual_read_only_independent_modules28_pair_bound_candidate_review'if r.returncode==0 and not errors else 'failed_actual_read_only_independent_modules28_pair_bound_candidate_review','actual_exit_code':r.returncode,'actual_command':command,'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':finish,'elapsed_seconds':time.monotonic()-tick,'checker':ref(C),'runner':ref(Path(__file__)),'raw_log':ref(L),'findings':ref(F)if F.exists()else None,'protected_selected27_proof_sources':1175,'protected_new_canonical28_sources':11,'protected_current60_assets':31,'protected_installed27_owners':5,'protection_errors':errors,'production_installer_or_compiler_executed':False}
with O.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps(d));raise SystemExit(0 if r.returncode==0 and not errors else 1)

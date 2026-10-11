from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased')
HELPER=Path('/tmp/prepare-modules28-final-offer-primary-real-root-closure-v4.py')
OUT=Path('/tmp/modules28-final-offer-primary-real-root-closure-actual-v4.json')
LOG=OUT.with_suffix('.log');READER=Path('/tmp/modules28-final-offer-primary-real-root-closure-no-reader-v4.json')
assert not OUT.exists() and not LOG.exists() and not READER.exists()
def H(n):return hashlib.sha256(Path(n).read_bytes()).hexdigest()
def ref(n):return {'file':str(n),'sha256':H(n),'bytes':Path(n).stat().st_size}
selection=R/'reports/full-coverage/checkpoint-27-selection.json';s=json.loads(selection.read_bytes())
assert H(selection)=='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd' and len(s['proof_files'])==1175
held={R/n:p['sha256'] for n,p in s['proof_files'].items()}
assets={p:H(p) for p in (R/'SafeLearning').glob('*') if p.is_file()};assert len(assets)==31;held.update(assets)
for n in ['book/coverage/inventory.json','book/coverage/inventory-after-correction60.json','book/coverage/material-corrections.json','reports/full-coverage/checkpoint-27-selection.json','reports/full-coverage/source56-60-corrections-application-v1.json','reports/full-coverage/source56-60-corrections-application28-execution-v1.json']:
 held[R/n]=H(R/n)
for n in ['modules.json','core.json','foundations.json','applied.json','applied-promotions.json']:held[R/'book/coverage'/n]=H(R/'book/coverage'/n)
new_sources=0;new_pairs=0
for base in ['current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json','current60-commissioning17-canonical-pair-v1/actual-current60-commissioning17-canonical-paired-readiness28-v1.json']:
 p=R/'book/coverage/checks/future28-core'/base;held[p]=H(p);ready=json.loads(p.read_bytes())
 for x in ready['sources']:held[R/x['canonical_source']]=x['original_tmp_source']['sha256'];new_sources+=1
 for pair in ready['actual_paired_records']:
  new_pairs+=1
  for k in ['actual_record','raw_log','source_snapshot']:held[R/pair[k]['file']]=pair[k]['sha256']
assert (new_sources,new_pairs)==(11,22)
held[HELPER]=H(HELPER);held[Path(__file__)]=H(Path(__file__))
for p,h in held.items():assert H(p)==h,p
helpers={str(HELPER):H(HELPER),str(Path(__file__)):H(Path(__file__))}
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic();cmd=['python3',str(HELPER)]
with LOG.open('xb') as f:run=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();errors=[str(p) for p,h in held.items() if H(p)!=h]
d={'status':'passed' if run.returncode==0 and not errors else 'failed','actual_exit_code':run.returncode,'actual_command':cmd,'actual_workdir':str(R),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,'helper':ref(HELPER),'runner':ref(Path(__file__)),'helper_sha256_before':helpers,'helper_sha256_after':{str(p):H(p) for p in [HELPER,Path(__file__)]},'log':str(LOG),'log_sha256':H(LOG),'reader':ref(READER) if READER.exists() else None,'protected_selected27_proofs':1175,'protected_current60_assets':31,'protected_live_owner27_files':5,'protected_new_canonical_sources':11,'protected_new_native_pairs':22,'protection_errors':errors,'canonical_owner_source_selection_or_publication_written':False,'coverage_complete':False}
OUT.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({k:d[k] for k in ['status','actual_exit_code','started_at_utc','finished_at_utc','elapsed_seconds','log_sha256','reader','protection_errors']}));raise SystemExit(0 if run.returncode==0 and not errors else 1)

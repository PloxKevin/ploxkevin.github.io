from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,subprocess,time
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/review-source65-owner29-context-producer-independent-modules-v1.py');O=Path('/tmp/source65-owner29-context-producer-independent-modules-actual-v1.json');L=O.with_suffix('.log');assert not O.exists()and not L.exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
selection=json.loads((R/'reports/full-coverage/checkpoint-28-selection.json').read_bytes());pins={n:v['sha256']for n,v in selection['proof_files'].items()}
for p in (R/'SafeLearning').glob('*'):
 if p.is_file()and p.suffix in {'.html','.css','.js'}:pins[str(p.relative_to(R))]=sha(p)
for n in ['book/coverage/inventory.json','book/coverage/material-corrections.json','book/inventory_claims.py','reports/full-coverage/checkpoint-28-selection.json']+['book/coverage/'+n+'.json'for n in ['core','foundations','applied','applied-promotions','modules']]:pins[n]=sha(R/n)
integration=json.loads((R/'reports/full-coverage/owner29-reviewed-candidate-integration-v1.json').read_bytes());binding=json.loads((R/integration['binding_manifest']).read_bytes())
for batch in binding['canonical_pair_batches']:
 readiness=json.loads((R/batch['readiness']['file']).read_bytes())
 for row in readiness['sources']:pins[row['canonical_source']]=row['original_tmp_source']['sha256']
for n in ['reports/full-coverage/root-source65-final-owner-integration29-v1.json','reports/full-coverage/owner29-reviewed-candidate-integration-v1.json','reports/full-coverage/owner29-reviewed-candidate-integration-execution-v1.json',integration['binding_manifest'],'verification/lean/lakefile.toml','verification/lean/lake-manifest.json','verification/lean/lean-toolchain']:
 pins[n]=sha(R/n)
assert len([n for n in pins if n.startswith('verification/lean/SafeLearning/')and n.endswith('.lean')])==1197
before={n:sha(R/n)for n in pins};assert before==pins
cmd=['python3',str(H)];hp=sha(H);start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with L.open('xb')as f:p=subprocess.run(cmd,cwd=R,stdout=f,stderr=subprocess.STDOUT)
end=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-t;after={n:sha(R/n)for n in pins};errors=[n for n in pins if after[n]!=pins[n]]
d={'status':'passed'if p.returncode==0 and not errors else'failed','actual_exit_code':p.returncode,'actual_command':cmd,'actual_workdir':str(R),'started_at_utc':start,'finished_at_utc':end,'elapsed_seconds':elapsed,'helper':str(H),'helper_sha256_before':hp,'helper_sha256_after':sha(H),'runner':str(Path(__file__)),'runner_sha256':sha(Path(__file__)),'raw_log':str(L),'raw_log_sha256':sha(L),'protected_current_selected_source_count':len(selection['proof_files']),'protected_current_selected_plus_actual_canonical_source_count':1197,'protected_inputs_sha256':pins,'protected_before_sha256':before,'protected_after_sha256':after,'protection_errors':errors,'only_new_future_evidence_files_written':True,'compiler_started':False}
O.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'actual_record':str(O),'sha256':sha(O),'actual_exit_code':p.returncode,'elapsed_seconds':elapsed,'protection_errors':errors,'raw_log_sha256':sha(L)}));raise SystemExit(p.returncode or int(bool(errors)))

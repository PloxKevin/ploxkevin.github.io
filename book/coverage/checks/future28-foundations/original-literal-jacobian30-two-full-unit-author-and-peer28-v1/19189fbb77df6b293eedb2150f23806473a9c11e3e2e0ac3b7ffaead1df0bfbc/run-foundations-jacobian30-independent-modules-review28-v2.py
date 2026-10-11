from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=Path('/tmp/review-foundations-jacobian30-independent-modules28-v2.py')
OUT=Path('/tmp/foundations-jacobian30-independent-modules-review28-checker-actual-v2.json');LOG=OUT.with_suffix('.log')
assert not OUT.exists() and not LOG.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
selection=ROOT/'reports/full-coverage/checkpoint-27-selection.json'
assert sha(selection)=='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
S=json.loads(selection.read_bytes());proofs={ROOT/k:v['sha256'] for k,v in S['proof_files'].items()};assert len(proofs)==1175
held={p:sha(p) for p in [HELPER,Path(__file__),selection,ROOT/'book/coverage/inventory.json',ROOT/'book/inventory_claims.py',ROOT/'book/coverage/material-corrections.json']}
held.update({p:sha(p) for p in (ROOT/'SafeLearning').glob('*') if p.is_file()})
held.update({ROOT/'book/coverage'/n:sha(ROOT/'book/coverage'/n) for n in ('modules.json','core.json','foundations.json','applied.json','applied-promotions.json')})
held.update(proofs)
for p,h in held.items():assert sha(p)==h
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic();command=['python3',str(HELPER)]
with LOG.open('xb') as f:r=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();errors=[]
for p,h in held.items():
 if sha(p)!=h:errors.append(str(p))
proposal=Path('/tmp/foundations-jacobian30-independent-modules-review28-v2.json')
out={'status':'passed_actual_independent_semantic_reader_and_current55_protection' if r.returncode==0 and not errors else 'failed_actual_independent_semantic_reader_or_protection','actual_exit_code':r.returncode,'actual_command':command,'actual_workdir':str(ROOT),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,'helper':ref(HELPER),'runner':ref(Path(__file__)),'raw_log':ref(LOG),'proposal':ref(proposal) if proposal.exists() else None,'selection':ref(selection),'protected_selected_proof_sources':1175,'source_owner_selection_bytes_unchanged':not errors,'protection_errors':errors,'canonical_application_or_coverage_or_lean_kernel_approval_claimed':False}
with OUT.open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps(out));raise SystemExit(0 if r.returncode==0 and not errors else 1)

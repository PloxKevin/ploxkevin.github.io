"""Preserve existing independent closer reviews/actual logs, without rerunning."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/future27-core/closer26-independent-peer-originals-v1'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
assert not BASE.exists()
peer=Path('/tmp/root-checkpoint26-delivery-closer2-actual-two-deliveries-independent-foundations-review-v2.json')
assert sha(peer)=='3ba21d03879a8f279e11e8ad2e7d870a894568de2f1896aa7ba60167fa6d9609'
d=read(peer);prior=Path(d['original_full_code_review']['file'])
assert sha(prior)==d['original_full_code_review']['sha256']
assert read(prior)==d['entire_original_code_review_body_and_time']
assert d['errors']==[] and d['helper_sha256']==sha(ROOT/'book/coverage/checks/close_root_checkpoint26_delivery_originals_v2.py')
names=[peer,prior]
actuals=[]
for stem in ['root-checkpoint26-delivery-closer2-independent-foundations-actual-v1','root-checkpoint26-delivery-closer2-actual-two-deliveries-independent-foundations-actual-v2']:
 p=Path('/tmp')/(stem+'.json');a=read(p)
 assert type(a['actual_exit_code']) is int and a['actual_exit_code']==0
 assert a['actual_workdir']==str(ROOT)
 assert a['actual_command'][0]=='python3' and len(a['actual_command'])==2
 checker=Path(a['actual_command'][1]);log=Path(a['log'])
 assert sha(checker)==a['helper_sha256_before']==a['helper_sha256_after']
 assert sha(log)==a['log_sha256'];names.extend([p,checker,log]);actuals.append(a)
for n in ['run-root-checkpoint26-delivery-closer2-independent-foundations-v1.py','run-root-checkpoint26-delivery-closer2-actual-two-deliveries-independent-foundations-v2.py']:
 names.append(Path('/tmp')/n)
aliases={}
for p in names:
 assert p.is_file() and not p.is_symlink() and p.parent==Path('/tmp')
 target=BASE/p.name;target.parent.mkdir(parents=True,exist_ok=True)
 with target.open('xb') as f:f.write(p.read_bytes())
 assert sha(p)==sha(target);aliases[str(p)]=ref(target)
out={'status':'passed_exact_original_closer26_independent_full_reviews_and_actual_read_only_execution_bytes_closed',
 'closed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(Path(__file__)),
 'original_closed_byte_aliases':aliases,'original_peer':aliases[str(peer)],
 'entire_original_fresh269_review_body_and_time':d,'entire_original_focused17_fixture_review_body_and_time':read(prior),
 'entire_original_actual_read_only_execution_bodies_and_times':actuals,
 'actual_closer_execution':ref(ROOT/'reports/full-coverage/close-checkpoint26-delivery-originals-execution-v2.json'),
 'actual_closer_raw_log':ref(ROOT/'reports/full-coverage/close-checkpoint26-delivery-originals-execution-v2.log'),
 'actual_closed_delivery_catalogue':ref(ROOT/'book/coverage/checks/future27-core/closed-checkpoint26-delivery-originals-v2/closed-original-byte-aliases-v1.json'),
 'scope':'Exact original peer/checker/runner/actual/log bytes retained; no review/proof/source/owner/Git/deployment rewritten or repeated.'}
with (BASE/'closed-original-peer-byte-aliases-v1.json').open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'passed','original_aliases':len(aliases)}))

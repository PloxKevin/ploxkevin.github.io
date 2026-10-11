from pathlib import Path
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');F=Path('/tmp/core28-current60-identity-independent-foundations-findings-v1.json');A=Path('/tmp/core28-current60-identity-independent-foundations-actual-v1.json');OUT=Path('/tmp/core28-current60-identity-independent-foundations-review-v1.json')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def j(p):return json.loads(p.read_bytes())
def ref(p):return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':h(p)}
assert not OUT.exists() and h(F)=='0ade5478b5640b6cafbc0b095e8aff7ee6e0410cfe0c6b681a046c2798833348'and h(A)=='2233b9853982e7adc80c6bf662fc031061b4894f8b82ad61849b2b88c9ae67fa'
a=j(A);f=j(F);assert a['status']=='passed'and a['actual_exit_code']==0 and type(a['actual_exit_code'])is int and a['protection_errors']==[]
assert a['checker_sha256_before']==a['checker_sha256_after']==h(Path(a['checker']['file']))and a['raw_log_sha256']==h(Path(a['raw_log']))
for n,s in a['protected_before_sha256'].items():assert h(R/n)==s==a['protected_after_sha256'][n]
out=copy.deepcopy(f);out['actual_independent_reader']=ref(A);out['actual_independent_reader_raw_log']=ref(Path(a['raw_log']));out['independent_checker']=a['checker'];out['independent_runner']=a['runner'];out['original_findings']=ref(F);out['full_manual_read_and_native_guard_reader_are_distinct']=True
with OUT.open('x')as x:json.dump(out,x,indent=2);x.write('\n')
sources=[F,A,Path(a['raw_log']),Path(a['checker']['file']),Path(a['runner']['file']),Path(__file__),OUT]
B=R/'book/coverage/checks/future28-foundations/original-core28-current60-zero-proof-independent-foundations-peer-v1';plan={};aliases={}
for p in sources:
 q=B/h(p)/p.name;assert not q.exists();plan[q]=p.read_bytes();aliases[str(p)]=ref(p);aliases[str(p)]['file']=str(q.relative_to(R))
catalog=B/'original-closed-byte-aliases-v1.json';assert not catalog.exists();plan[catalog]=(json.dumps({'status':'closed_exact_original_core28_current60_identity_foundations_peer_bytes','original_byte_aliases':aliases,'original_reviewed_at_utc':f['reviewed_at_utc'],'original_reader_started_at_utc':a['started_at_utc'],'original_reader_finished_at_utc':a['finished_at_utc'],'original_reader_actual_exit_code':0,'canonical_owner_source_compiler_mutated':False},indent=2)+'\n').encode()
for n,s in a['protected_before_sha256'].items():assert h(R/n)==s
for p,b in plan.items():
 p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb')as x:x.write(b)
for n,s in a['protected_before_sha256'].items():assert h(R/n)==s
for p,b in plan.items():assert p.read_bytes()==b
print(json.dumps({'peer':ref(OUT),'durable_peer':aliases[str(OUT)],'catalog':ref(catalog),'actual_independent_reader':ref(A)}))

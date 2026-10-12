from pathlib import Path
import hashlib,json,copy
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future29-applied/scalar-lipsdp42-full-independent-v1'
F=Path('/tmp/scalar-lipsdp42-independent-applied-findings29-v2.json');A=Path('/tmp/scalar-lipsdp42-independent-applied-actual29-v2.json')
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':H(p)}
def P(n):return Path(n)if Path(n).is_absolute()else R/n
assert H(F)=='0515dd5c0cfca3a4f101a661ef92d9a5e6e10a4e28e6a1d3bcc7dd359980d666'
assert H(A)=='6438998823525c664de5491e7ce334d870ea5c82c477492f4a912fa24e0811d9'
findings=json.loads(F.read_bytes());actual=json.loads(A.read_bytes())
assert type(actual['actual_exit_code'])is int and actual['actual_exit_code']==0 and actual['protection_errors']==[]
B.mkdir(exist_ok=False,parents=True);D=B/'original-closed-bytes';D.mkdir()
aliases={};closed={}
def keep(p):
 p=Path(p);h=H(p);q=D/h/p.name;q.parent.mkdir(exist_ok=True)
 if not q.exists():
  with q.open('xb')as f:f.write(p.read_bytes())
 assert H(q)==h
 a=ref(q);aliases[str(p)]=a;closed[a['file']]=h;return a
paths=[F,A,Path('/tmp/scalar-lipsdp42-independent-applied-actual29-v2.log'),
 Path('/tmp/check-scalar-lipsdp42-independent-applied29-v1.py'),Path('/tmp/run-scalar-lipsdp42-independent-applied29-v1.py'),
 Path('/tmp/scalar-lipsdp42-independent-applied-actual29-v1.json'),Path('/tmp/scalar-lipsdp42-independent-applied-actual29-v1.log'),
 Path('/tmp/check-scalar-lipsdp42-independent-applied29-v2.py'),Path('/tmp/run-scalar-lipsdp42-independent-applied29-v2.py'),Path(__file__),
 R/'verification/lean/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean',
 R/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean']
for p in paths:keep(p)
evidence=dict(findings['required_evidence_artifacts_sha256'])
for n,h in closed.items():assert n not in evidence or evidence[n]==h;evidence[n]=h
for n,h in evidence.items():assert H(P(n))==h,n
peer=copy.deepcopy(findings)
peer['entire_original_measured_findings_body_and_time']=aliases[str(F)]
peer['actual_reader_execution']=aliases[str(A)];peer['actual_finalizer']=aliases[str(A)]
peer['original_checker1_failure']={'actual':aliases['/tmp/scalar-lipsdp42-independent-applied-actual29-v1.json'],
 'raw_log':aliases['/tmp/scalar-lipsdp42-independent-applied-actual29-v1.log'],
 'reason':'Reader1 expected9 definitions and51 total names; actual source has10 definitions including the explicit finite grid, hence52 public names. NEW reader2 corrects only this metadata count; original source and every mathematical decision are unchanged.'}
peer['public_declaration_count']=52;peer['public_theorem_count']=42
peer['original_closed_byte_aliases']=aliases
peer['publication_evidence_sha256']=closed
peer['required_evidence_artifacts_sha256']=evidence
peer['additional_primary_full_used_API_bytes']= [aliases[str(p)] for p in paths[-2:]]
P_OUT=B/'scalar-lipsdp42-full-source-independent-applied29-peer-v1.json'
with P_OUT.open('x')as f:f.write(json.dumps(peer,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'peer':ref(P_OUT),'bytes':P_OUT.stat().st_size,'closed_evidence_count':len(evidence),'own_original_byte_aliases':len(aliases),'status':peer['status'],'errors':peer['errors']}))

from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future30-core/owner30-binding-preparer1-independent-foundations-v1';F=Path('/tmp/owner30-binding-preparer1-independent-foundations-findings-v1.json');N=Path('/tmp/owner30-binding-preparer1-independent-foundations-actual-v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size}
assert not B.exists();d=json.loads(F.read_bytes());a=json.loads(N.read_bytes());assert a['status']=='passed' and a['actual_exit_code']==0 and a['protection_errors']==[] and a['helper_sha256_before']==a['helper_sha256_after'] and sha(a['log'])==a['log_sha256'];assert d['full_code_read'] is True and d['errors']==[]
protected=a['protected_inputs_sha256_before'];assert sum(n.startswith('verification/lean/SafeLearning/') for n in protected)==1242;assert all(sha(R/n)==h for n,h in protected.items())
closed={};aliases={}
def bind(p):
 p=Path(p);p=p if p.is_absolute() else R/p;h=sha(p)
 if p.is_relative_to(R) and p.resolve().is_relative_to(R) and not p.is_symlink():q=p
 else:
  q=B/'exact-original-by-sha256'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert sha(q)==h
  else:
   with q.open('xb') as f:f.write(p.read_bytes())
 r=ref(q);aliases[str(p)]=r;closed[r['file']]=h;return r
for n,h in d['required_evidence_artifacts_sha256'].items():assert sha(n)==h;bind(n)
for p in [F,N,Path(a['log']),Path(__file__),Path('/tmp/run-review-owner30-binding-preparer1-independent-foundations-v1.py')]:bind(p)
actualaliases={n:bind(n) for n in [*a['helper_sha256_before'],a['log']] if Path(n).is_absolute()}
peer={k:v for k,v in d.items() if k!='required_evidence_artifacts_sha256'};peer.update({'original_wrapper_scope_label_observation':'The original wrapper retained its integrator2 descriptive scope string. Its actual_command, checker source, helper-before/after pins and findings explicitly identify this binding-preparer1/protocol read; the original native body/times remain unchanged. This is not a producer failure or a second measured read.', 'closed_at_utc':datetime.now(timezone.utc).isoformat(),'original_full_code_read_findings':bind(F),'actual_finalizer':bind(N),'actual_finalizer_original_byte_aliases':actualaliases,'actual_independent_reader_raw':bind(a['log']),'reader_helper':bind('/tmp/review-owner30-binding-preparer1-independent-foundations-v1.py'),'reader_wrapper':bind('/tmp/run-review-owner30-binding-preparer1-independent-foundations-v1.py'),'protected_actual_canonical_source_count':1242,'unchanged_current79_book_assets':31,'unchanged_historical29_raw_owners':5,'actual1242_31_five_and_authoring_fragments_before_after_unchanged':True,'protection_errors':[],'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':closed})
p=B/'root-owner30-binding-preparer1-and-protocol-full-code-independent-foundations30-closed-peer-v1.json';p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists();p.write_text(json.dumps(peer,ensure_ascii=False,indent=2)+'\n')
assert all(not (R/n).is_symlink() and (R/n).resolve().is_relative_to(R) and sha(R/n)==h for n,h in closed.items());assert all(sha(R/n)==h for n,h in protected.items())
print(json.dumps({'peer':ref(p),'helper':d['helper'],'actual_reader_exit_code':a['actual_exit_code'],'actual_reader_seconds':a['elapsed_seconds'],'physical_refs':len(closed),'full_code_read':True,'errors':[]}))

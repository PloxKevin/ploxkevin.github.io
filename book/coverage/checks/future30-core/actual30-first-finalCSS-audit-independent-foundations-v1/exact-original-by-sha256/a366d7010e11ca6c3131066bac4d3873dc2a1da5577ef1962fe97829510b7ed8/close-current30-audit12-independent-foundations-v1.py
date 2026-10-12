from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future30-core/actual30-first-finalCSS-audit-independent-foundations-v1';F=Path('/tmp/current30-audit12-independent-foundations-findings-v1.json');N=Path('/tmp/current30-audit12-independent-foundations-actual-v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size}
assert not B.exists();d=json.loads(F.read_bytes());a=json.loads(N.read_bytes());assert a['status']=='passed' and a['actual_exit_code']==0 and a['protection_errors']==[] and a['helper_sha256_before']==a['helper_sha256_after'] and sha(a['log'])==a['log_sha256'] and a['old_owner29_context_used'] is False and d['errors']==[]
protected=a['protected_inputs_sha256_before'];assert sum(n.startswith('verification/lean/SafeLearning/') for n in protected)==1242 and sum(n.startswith('SafeLearning/') for n in protected)==31;assert all(sha(R/n)==h for n,h in protected.items())
closed={};aliases=dict(d['exact_installed30_owner_aliases']);mutableowners={R/'book/coverage'/f'{n}.json' for n in ['core','foundations','applied','modules','applied-promotions']}
def bind(p):
 p=Path(p);p=p if p.is_absolute() else R/p;h=sha(p);assert p not in mutableowners
 if p.is_relative_to(R) and p.resolve().is_relative_to(R) and not p.is_symlink():q=p
 else:
  q=B/'exact-original-by-sha256'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert sha(q)==h
  else:
   with q.open('xb') as f:f.write(p.read_bytes())
 r=ref(q);aliases[str(p)]=r;closed[r['file']]=h;return r
for n,h in d['required_evidence_artifacts_sha256'].items():assert sha(n)==h;bind(n)
for p in [F,N,Path(a['log']),Path(__file__),Path('/tmp/run-review-current30-audit12-independent-foundations-v1.py'),Path('/tmp/checkpoint30-runtime4-export2-static-code-read-foundations-v1.json')]:bind(p)
actualaliases={n:bind(n) for n in [*a['helper_sha256_before'],a['log']] if Path(n).is_absolute()}
peer={k:v for k,v in d.items() if k!='required_evidence_artifacts_sha256'};peer.update({'closed_at_utc':datetime.now(timezone.utc).isoformat(),'original_full_identity_findings':bind(F),'actual_finalizer':bind(N),'actual_finalizer_original_byte_aliases':actualaliases,'actual_independent_reader_raw':bind(a['log']),'reader_helper':bind('/tmp/review-current30-audit12-independent-foundations-v1.py'),'reader_wrapper':bind('/tmp/run-review-current30-audit12-independent-foundations-v1.py'),'original_static_runtime4_export2_code_read':bind('/tmp/checkpoint30-runtime4-export2-static-code-read-foundations-v1.json'),'protected_actual_proof_sources':1242,'unchanged_final_CSS_current31_assets_and_installed30_raw5_before_after':True,'actual_read_only_Git_dependency_identity_checks_not_compiler_calls':True,'protection_errors':[],'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':closed})
p=B/'actual30-first45fresh-and-finalCSS1242reuse-source-project-dependency-native-and-owner30-identity-independent-foundations30-closed-peer-v1.json';p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists();p.write_text(json.dumps(peer,ensure_ascii=False,indent=2)+'\n')
assert all(not (R/n).is_symlink() and (R/n).resolve().is_relative_to(R) and sha(R/n)==h for n,h in closed.items());assert all(sha(R/n)==h for n,h in protected.items())
print(json.dumps({'peer':ref(p),'actual_reader_exit_code':a['actual_exit_code'],'actual_reader_seconds':a['elapsed_seconds'],'physical_refs':len(closed),'proofs':1242,'theorems':11080,'first_fresh':45,'final_fresh':0,'coverage_complete':False,'errors':[]}))

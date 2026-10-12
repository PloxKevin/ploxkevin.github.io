from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/modules-future30/matrix42-independent-foundations-v1'
FIND=Path('/tmp/modules-matrix42-independent-foundations30-findings-v1.json')
ACTUAL=Path('/tmp/modules-matrix42-independent-foundations30-actual-v1.json')
CONTEXT=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(ROOT)),'sha256':sha(p),'bytes':p.stat().st_size}
assert not BASE.exists()
d=json.loads(FIND.read_bytes());a=json.loads(ACTUAL.read_bytes())
assert a['status']=='passed' and type(a['actual_exit_code']) is int and a['actual_exit_code']==0 and a['protection_errors']==[]
assert a['helper_sha256_before']==a['helper_sha256_after'] and sha(a['log'])==a['log_sha256']
assert a['actual_command']==['python3','/tmp/check-modules-matrix42-independent-foundations30-v1.py'] and a['actual_workdir']==str(ROOT)
assert d['errors']==[] and d['public_theorem_count']==42 and all(g['approved_in_exact_scope'] for g in d['component_decisions'])
ctx=json.loads(CONTEXT.read_bytes());protected={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
assert all(sha(ROOT/n)==h for n,h in protected.items())
closed={};aliases=dict(d['original_closed_byte_aliases'])
def bind(p):
 p=Path(p);p=p if p.is_absolute() else ROOT/p;h=sha(p)
 if p.is_relative_to(ROOT) and p.resolve().is_relative_to(ROOT) and not p.is_symlink():q=p
 else:
  q=BASE/'originals'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert sha(q)==h
  else:
   with q.open('xb') as f:f.write(p.read_bytes())
 r=ref(q);aliases[str(p)]=r;closed[r['file']]=h;return r
for n,h in d['required_evidence_artifacts_sha256'].items():assert sha(n)==h;bind(n)
for p in [FIND,ACTUAL,Path(a['log']),CONTEXT,Path(__file__),Path('/tmp/run-modules-matrix42-independent-foundations30-v1.py')]:bind(p)
peer={k:v for k,v in d.items() if k not in ['required_evidence_artifacts_sha256','original_closed_byte_aliases']}
peer['original_actual_wrapper_scope_description_observation']={'original_scope':a['scope'],'correct_scope':'Actual full Matrix42 exact23/strict30 prefixes plus19 new strict/printedPSD component proofs.','reason':'The genuine read-only command/helper/checker output bind Matrix42; its wrapper descriptive scope retained full23 from the earlier template. Exact actual0/body/time is preserved, with no missing mathematical read or fabricated reader failure.'}
peer.update({'closed_at_utc':datetime.now(timezone.utc).isoformat(),'original_full_semantic_findings':bind(FIND),'original_review_finished_at_utc':d['review_finished_at_utc'],'actual_independent_reader':bind(ACTUAL),'actual_independent_reader_raw':bind(a['log']),'reader_helper':bind('/tmp/check-modules-matrix42-independent-foundations30-v1.py'),'reader_wrapper':bind('/tmp/run-modules-matrix42-independent-foundations30-v1.py'),'protected_selected29_proof_sources':1197,'unchanged_current65_book_assets':31,'unchanged_installed29_live_owners':5,'protection_errors':[],'actual1197_31_five_before_after_unchanged':True,'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':closed})
p=BASE/'modules-matrix42-full-source-current-literal-components-independent-foundations30-closed-peer-v1.json'
assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(peer,ensure_ascii=False,indent=2)+'\n')
assert all(not (ROOT/n).is_symlink() and (ROOT/n).resolve().is_relative_to(ROOT) and sha(ROOT/n)==h for n,h in closed.items())
assert all(sha(ROOT/n)==h for n,h in protected.items())
print(json.dumps({'peer':ref(p),'physical_refs':len(closed),'aliases':len(aliases),'actual_reader_code':0,'actual_reader_seconds':a['elapsed_seconds'],'approved_new_public_components':19,'whole_decision':False,'protection_errors':[]}))

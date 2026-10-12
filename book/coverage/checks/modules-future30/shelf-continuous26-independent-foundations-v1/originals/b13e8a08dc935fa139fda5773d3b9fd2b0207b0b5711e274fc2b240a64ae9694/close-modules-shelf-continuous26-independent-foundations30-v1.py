from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/modules-future30/shelf-continuous26-independent-foundations-v1'
REQUEST=ROOT/'book/coverage/checks/modules-future30/shelf-continuous-control-association-v1/modules-shelf-continuous-control-full-association-and-prospective-whole-composition-review-request30-v1.json'
FIND=Path('/tmp/modules-shelf-continuous26-independent-foundations30-findings-v2.json')
ACTUAL=Path('/tmp/modules-shelf-continuous26-independent-foundations30-actual-v2.json')
CONTEXT=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(ROOT)),'sha256':sha(p),'bytes':p.stat().st_size}
assert not BASE.exists()
d=json.loads(FIND.read_bytes());a=json.loads(ACTUAL.read_bytes());request=json.loads(REQUEST.read_bytes())
assert a['status']=='passed' and type(a['actual_exit_code']) is int and a['actual_exit_code']==0 and a['protection_errors']==[]
assert a['helper_sha256_before']==a['helper_sha256_after'] and sha(a['log'])==a['log_sha256']
assert d['errors']==[] and all(g['approved_in_exact_scope'] for g in d['component_decisions'])
ctx=json.loads(CONTEXT.read_bytes());protected={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
assert all(sha(ROOT/n)==h for n,h in protected.items())
closed={};aliases=dict(request['original_closed_byte_aliases'])
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
for p in [FIND,ACTUAL,Path(a['log']),CONTEXT,Path(__file__)]:bind(p)
readers=[]
for n in [1,2]:
 check=Path(f'/tmp/check-modules-shelf-continuous26-independent-foundations30-v{n}.py')
 run=Path(f'/tmp/run-modules-shelf-continuous26-independent-foundations30-v{n}.py')
 actual=Path(f'/tmp/modules-shelf-continuous26-independent-foundations30-actual-v{n}.json')
 raw=actual.with_suffix('.log')
 aa=json.loads(actual.read_bytes());assert type(aa['actual_exit_code']) is int and aa['actual_exit_code']==(1 if n==1 else 0) and aa['protection_errors']==[]
 readers.append({'trial':n,'actual':bind(actual),'raw':bind(raw),'helper':bind(check),'wrapper':bind(run),'actual_exit_code':aa['actual_exit_code'],'original_actual_times':{k:aa[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
peer={k:v for k,v in d.items() if k not in ['required_evidence_artifacts_sha256','original_closed_byte_aliases','original_reader1_preserved']}
peer.update({'closed_at_utc':datetime.now(timezone.utc).isoformat(),'request':bind(REQUEST),'source':request['source'],'original_full_semantic_findings':bind(FIND),'original_review_finished_at_utc':d['review_finished_at_utc'],'actual_independent_reader':bind(ACTUAL),'actual_independent_reader_raw':bind(a['log']),'reader_helper':bind('/tmp/check-modules-shelf-continuous26-independent-foundations30-v2.py'),'reader_wrapper':bind('/tmp/run-modules-shelf-continuous26-independent-foundations30-v2.py'),'original_reader_histories':readers,'original_reader1_true_schema_failure_reason':d['original_reader1_preserved']['reason'],'actual_protected_original_context':bind(CONTEXT),'protected_selected29_proof_sources':1197,'unchanged_current65_book_assets':31,'unchanged_installed29_live_owners':5,'protection_errors':[],'actual1197_31_five_before_after_unchanged':True,'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':closed})
p=BASE/'modules-shelf-continuous26-full-source-actual-control-association-independent-foundations30-closed-peer-v1.json'
assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(peer,ensure_ascii=False,indent=2)+'\n')
assert all(not (ROOT/n).is_symlink() and (ROOT/n).resolve().is_relative_to(ROOT) and sha(ROOT/n)==h for n,h in closed.items())
assert all(sha(ROOT/n)==h for n,h in protected.items())
print(json.dumps({'peer':ref(p),'physical_refs':len(closed),'aliases':len(aliases),'actual_reader_code':0,'actual_reader_seconds':a['elapsed_seconds'],'approved_public_components':26,'public_declarations':38,'whole_decision':False,'protection_errors':[]}))

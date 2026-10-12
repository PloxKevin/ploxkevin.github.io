from pathlib import Path
import json,hashlib
ROOT=Path('/home/oxrexkevin/SafetyBased');DEST=ROOT/'book/coverage/checks/future31-core/aggregate31-identity-independent-foundations-v1'
assert not DEST.exists()
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def sha(p):return hashlib.sha256(path(p).read_bytes()).hexdigest()
def ref(p):
 p=path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
find=Path('/tmp/current31-aggregate-identity-independent-foundations31-findings-v3.json');native=Path('/tmp/current31-aggregate-identity-independent-foundations31-actual-v2.json');d=json.loads(find.read_bytes());n=json.loads(native.read_bytes());assert n['actual_exit_code']==0 and n['protection_errors']==[]
refs={}
def collect(x):
 if isinstance(x,dict):
  if {'file','sha256'}<=x.keys() and isinstance(x['file'],str):refs[x['file']]=x
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(d)
paths=[find,native,path(n['log']),Path('/tmp/review-current31-aggregate-identity-independent-foundations31-v3.py'),Path('/tmp/run-review-current31-aggregate-identity-independent-foundations31-v2.py'),Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json'),Path('/tmp/review-current31-aggregate-identity-independent-foundations31-v2.py'),Path('/tmp/run-review-current31-aggregate-identity-independent-foundations31-v1.py'),Path(__file__)]
for p in paths:refs[str(p)]=ref(p)
aliases={}
for name,r in refs.items():
 p=path(name);assert sha(p)==r['sha256']
 if p.is_relative_to(ROOT) and str(p.relative_to(ROOT))!='verification/lean/SafeLearning.lean':aliases[name]={'original':r,'already_durable_exact_reference':ref(p)};continue
 q=DEST/'exact-original-by-sha256'/r['sha256']/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:q.write_bytes(p.read_bytes())
 aliases[name]={'original':r,'original_byte_copy':ref(q)}
def alias(name):return aliases[name].get('original_byte_copy',aliases[name].get('already_durable_exact_reference'))
d['actual_reader']=d['actual_finalizer']=alias(str(native))
d['actual_finalizer_original_byte_aliases']={str(p):alias(str(p)) for p in paths[1:6]}
d['genuine_original_reader1_failure']=alias(d['genuine_original_reader1_failure']['file']);d['genuine_original_reader1_failure_log']=alias(d['genuine_original_reader1_failure_log']['file'])
d['live_book_aggregate_is_separate_not_relabelled_selected30_or_selected31']=alias(d['live_book_aggregate_is_separate_not_relabelled_selected30_or_selected31']['file'])
d['original_full_findings']=alias(str(find));d['bounded_original_ref_aliases']=aliases
for name,r in refs.items():d['required_evidence_artifacts_sha256'][alias(name)['file']]=r['sha256']
d['no_recursive_old_snapshot_or_lake_or_dependency_artifact_tree_copy']=True
d['protected_actual_current31_proof_count']=1248;d['fresh_current81_assets31_and_raw_owner31_five_guards_before_after_unchanged']=True
out=DEST/'actual31-selected1248-six-fresh1242-reused-all11184-axioms1251-checks-full-identity-independent-foundations31-closed-peer-v1.json';out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'peer':ref(out),'actual_finalizer':d['actual_finalizer'],'actual_elapsed_seconds':n['elapsed_seconds'],'bounded_metadata_refs':len(refs)}))

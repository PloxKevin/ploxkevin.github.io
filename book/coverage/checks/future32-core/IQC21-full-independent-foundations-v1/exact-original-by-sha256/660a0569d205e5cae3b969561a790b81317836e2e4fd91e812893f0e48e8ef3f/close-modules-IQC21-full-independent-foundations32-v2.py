from pathlib import Path
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased');DEST=ROOT/'book/coverage/checks/future32-core/IQC21-full-independent-foundations-v1'
assert not (DEST/'modules-IQC21-entire-current-Exercise14_6-four-literals-full-mathematical-independent-foundations32-closed-peer-v1.json').exists()
def path(n):return Path(n)if Path(n).is_absolute()else ROOT/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n);return {'file':str(p.relative_to(ROOT))if p.is_relative_to(ROOT)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
F=Path('/tmp/modules-IQC21-full-independent-foundations32-semantic-v1.json');N=Path('/tmp/modules-IQC21-full-independent-foundations32-actual-v1.json');Q=Path('/tmp/modules-shifted-temporal-IQC21-full-Exercise14_6-review31-v1/modules-shifted-temporal-IQC21-entire-current-Exercise14_6-four-literals-full-review-request31-v2.json')
d=json.loads(F.read_bytes());q=json.loads(Q.read_bytes());n=json.loads(N.read_bytes());assert n['actual_exit_code']==0 and n['protection_errors']==[] and d['errors']==[]
offline={r['file'] for r in q['offline_primary_PDF_and_fulltext_only'].values()};refs={}
def collect(x):
 if isinstance(x,dict):
  if {'file','sha256'}<=x.keys()and isinstance(x['file'],str):refs[x['file']]=x
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(d);collect(q)
for name,h in q['all_physical_original_inputs_sha256'].items():
 assert sha(name)==h;refs[name]=ref(name)
paths=[F,N,path(n['log']),Q,Path('/tmp/review-modules-IQC21-full-independent-foundations32-v1.py'),Path('/tmp/run-review-modules-IQC21-full-independent-foundations32-v1.py'),Path('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json'),Path(__file__)]
for p in paths:refs[str(p)]=ref(p)
aliases={}
for name,r in refs.items():
 p=path(name)
 if sha(p)!=r['sha256']:
  aliases[name]={'original_historical_declared_path_ref':r,'historical_path_is_not_current_Source81_identity':True,'original_receipt_bytes_preserved_in_full_request':True}
  continue
 if name in offline:aliases[name]={'original':r,'offline_TMP_only_no_repository_copy':True};continue
 if p.is_relative_to(ROOT):aliases[name]={'original':r,'already_durable_exact_reference':ref(p)};continue
 target=DEST/'exact-original-by-sha256'/r['sha256']/p.name;target.parent.mkdir(parents=True,exist_ok=True)
 if target.exists():assert target.read_bytes()==p.read_bytes()
 else:target.write_bytes(p.read_bytes())
 aliases[name]={'original':r,'original_byte_copy':ref(target)}
def alias(name):return aliases[str(name)].get('original_byte_copy',aliases[str(name)].get('already_durable_exact_reference'))
d['actual_reader']=d['actual_finalizer']=alias(N)
d['actual_finalizer_original_byte_aliases']={str(p):alias(p)for p in paths[1:]}
d['original_full_semantic_findings']=alias(F);d['original_full_request']=alias(Q)
d['bounded_original_ref_aliases']=aliases
d['required_evidence_artifacts_sha256']={alias(name)['file']:r['sha256']for name,r in refs.items()if name not in offline and alias(name) is not None}
d['historical_receipt_live_source_path_refs_not_reinterpreted_as_current81']={name:a for name,a in aliases.items() if a.get('historical_path_is_not_current_Source81_identity')}
d['original_unwrapped_closer1_failure_preserved']={'helper':ref('/tmp/close-modules-IQC21-full-independent-foundations32-v1.py'),'actual_tool_exit_code':1,'reported_failure':'AssertionError at line25 while collecting historical source-path refs','script_started_at_utc':None,'script_finished_at_utc':None,'script_elapsed_seconds':None,'unknown_script_body_times_not_reconstructed':True,'semantic_reader1_actual0_unchanged':True}
d['protected_current_selected31_proof_count']=1248;d['fresh_current_Source81_assets31_and_installed_raw_owner31_five_guards_unchanged']=True
d['no_recursive_old_snapshot_or_lake_tree_copy']=True
d['primary_full_remote_PDF_and_extracted_text_remain_offline_TMP_only']={name:refs[name]for name in offline}
out=DEST/'modules-IQC21-entire-current-Exercise14_6-four-literals-full-mathematical-independent-foundations32-closed-peer-v1.json';out.write_text(json.dumps(d,indent=2)+'\n')
print(json.dumps({'peer':ref(out),'actual_elapsed_seconds':n['elapsed_seconds'],'bounded_refs':len(refs),'offline_remote_full_sources_not_copied':len(offline)}))

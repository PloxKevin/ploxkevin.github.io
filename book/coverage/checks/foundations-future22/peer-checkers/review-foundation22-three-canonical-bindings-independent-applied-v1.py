from pathlib import Path
from datetime import datetime,timezone
import sys,json,hashlib,copy
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book/coverage'))
from lean_names import declarations
cache={}
def sha(p):
 p=Path(p);p=p if p.is_absolute() else R/p;s=p.stat();k=(str(p),s.st_size,s.st_mtime_ns)
 if k not in cache:cache[k]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[k]
def read(p):
 p=Path(p);return json.loads((p if p.is_absolute() else R/p).read_text())
root='book/coverage/checks/foundations-future22/';readiness=root+'four-canonical-paired-build-readiness-v1.json'
assert sha(readiness)=='00ebc5ed62737e4cba2fad07d7cd5206b918f6424079cae31bbb56f28939e38c'
invpath='book/coverage/inventory-after-correction48.json';inv=read(invpath);assert sha(invpath)=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
units={u['key']:u for u in inv['material_source_units']}
inputs=[('CompleteFoundationsRKHSBounds22','linalg-rkhs-bounds-two-units-independent-applied-source-review22-v1.json','1d76fb496a73220f33bc5a5930ea37192cdfee09dcba157c31d2f22147cc0428',5),('CompleteFoundationsContinuousLevels22','basics-continuous-levels-three-units-independent-applied-source-review22-v1.json','8dbd2db6414b60e00fc14702c98a36a462442a9db6b93467988f7e0ac3e2bb1a',7),('CompleteFoundationsMetricDefinitions22','basics-metric-definitions-two-units-independent-applied-source-review22-v1.json','6928d320b8e048d48b6bc1d02a610d4b6df363837efe8a88c44844c9439697b4',9)]
entries=[];material=[];allrecords=[];proofs={}
for module,basename,h,n in inputs:
 original='/tmp/'+basename; archived=root+'original-tmp/'+basename
 assert sha(original)==sha(archived)==h
 old=read(archived);assert old==read(original) and old['inventory_sha256']==sha(invpath)
 src='verification/lean/SafeLearning/'+module+'.lean';tmp='/tmp/'+module+'.lean'
 assert old['proof_source_sha256'][tmp]==sha(tmp)==sha(src)==sha(root+'sources/'+module+'-source-v1.lean')
 exported=[d['name'] for d in declarations((R/src).read_text()) if d['kind'] in ['theorem','lemma']];assert len(exported)==n
 evidence=[]
 for suffix in ['standalone','named-build']:
  p=root+module+'-'+suffix+'-v1.json';rec=read(p);assert rec['exit_code']==0
  assert rec['source']==src and rec['source_sha256_before']==rec['source_sha256_after']==sha(src)
  assert sha(rec['log'])==rec['log_sha256']
  if 'preserved_source' in rec:assert sha(rec['preserved_source'])==rec['preserved_source_sha256']==sha(src)
  if 'actual_tmp_passing_record' in rec:assert sha(rec['actual_tmp_passing_record'])==rec['actual_tmp_passing_record_sha256']
  evidence.append({'file':p,'sha256':sha(p),'record':rec,'raw_log_empty':(R/rec['log']).stat().st_size==0})
 allrecords.extend(evidence)
 for p,qh in old['proof_source_sha256'].items():assert sha(p)==qh
 proofs.update(old['proof_source_sha256']);proofs[src]=sha(src)
 for row in old['material_units']:
  key=row['source_unit_key'];current=units[key];assert current==row['entire_inventory_record']
  assert current['text_sha256']==row['unit_text_sha256'] and current['source_sha256']==row['source_sha256']==sha(current['source'])
  assert row['whole_unit_approved'] and row['review_status']=='approved_complete_source' and row['missing_clauses']==[]
  material.append(copy.deepcopy(row))
 entries.append({'module':module,'original_TMP_review':original,'original_TMP_review_sha256':h,'archived_original_review':archived,'archived_original_review_sha256':h,'original_reviewed_at_utc_preserved':old['reviewed_at_utc'],'entire_original_body_decisions_and_time_preserved':old,'canonical_source':src,'canonical_source_sha256':sha(src),'original_TMP_source':tmp,'original_TMP_source_sha256':sha(tmp),'canonical_preserved_source':root+'sources/'+module+'-source-v1.lean','canonical_preserved_source_sha256':sha(src),'public_theorems':exported,'actual_canonical_execution_records':evidence,'same_current48_entire_inventory_records':True,'semantic_scope':'Exactly the original independently read full literal definitions, assumptions, complete source correspondences, per-unit reasons, hypotheses, declaration groups and missing[] decisions. This new supplement changes evidence locations only; it does not create a new whole decision or expand any original scope.'})
m=read('reports/full-coverage/checkpoint-21-manifest.json');assert len(m['proof_files'])==1089 and len(m['frozen_inputs_sha256'])==32040
for n,row in m['proof_files'].items():
 assert sha(n)==row['sha256']
 for p,h in row['evidence_sha256'].items():assert sha(p)==h
for p,h in m['frozen_inputs_sha256'].items():assert sha(str(Path(m['snapshot'])/p))==h
out=R/root/'three-canonical-literal-peer-bindings-independent-applied-v1.json';assert not out.exists()
record={'schema_version':1,'status':'independent_original_whole_literal_decisions_exact_canonical_paired_evidence_bindings_confirmed','reviewer':'/root/applied_next','binding_checked_at_utc':datetime.now(timezone.utc).isoformat(),'inventory':invpath,'inventory_sha256':sha(invpath),'readiness':readiness,'readiness_sha256':sha(readiness),'bindings':entries,'material_units':material,'proof_source_sha256':proofs,'actual_canonical_execution_records':allrecords,'counts':{'unchanged_original_whole_material_decisions':7,'original_peer_reports_preserved':3,'new_canonical_proof_sources':3,'public_new_theorems':21,'actual_canonical_zero_execution_records':6,'new_semantic_whole_decisions_created':0},'protected21_integrity':{'selected_sources':1089,'frozen_inputs':32040,'all_exact':True},'checker':'/tmp/review-foundation22-three-canonical-bindings-independent-applied-v1.py','checker_sha256':sha('/tmp/review-foundation22-three-canonical-bindings-independent-applied-v1.py'),'limits':['Full original literal/body/context reviews remain immutable. In particular RKHS bound requires nonnegative B/kappa and bounded diagonal; continuous AE upgrade uses explicit full-support or immediately defined finite-Euclidean volume convention; metric topology remains in the stated norm/Euclidean context with positive radii.','Every original TMP proof body is byte-identical to the canonical source and preserved copy, and every canonical standalone/named record actually reports EXIT0 with matching raw log hashes. No aggregate execution is inferred.','This new final location/evidence supplement preserves original mathematical decisions/times; original reports are neither relabeled as fresh canonical semantic reviews nor rewritten.','No held21 owner/helper/ledger/offer/sourceHTML or inventory was changed. These three new sources remain outside selected21.'],'coverage_complete':False,'errors':[]}
out.write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'file':str(out.relative_to(R)),'sha256':sha(out),'counts':record['counts']}))

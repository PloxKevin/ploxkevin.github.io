from pathlib import Path
import hashlib,json,sys,re
from datetime import datetime,timezone
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
inv=R/'book/coverage/inventory-after-correction48.json';ij=json.loads(inv.read_text());assert H(inv)=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108';sel=R/'reports/full-coverage/checkpoint-21-selection.json';sj=json.loads(sel.read_text());assert H(sel)=='bf73119b16a9fbaf22e29ae9b673f940af29b5dc3950aabbf7032ad299b7334f'
for p,row in sj['proof_files'].items():assert H(R/p)==row['sha256']
rows=[]
for name,label in [('CompleteModulesMonitoringBlocksClosed22','modules-monitoring-blocks-closed22'),('CompleteModulesMonitoringBlockLimitsClosed22','modules-monitoring-block-limits-closed22')]:
 p=R/'verification/lean/SafeLearning'/(name+'.lean');dr=declarations(p.read_text());rs=[]
 for mode in ['standalone','named']:
  j=Path('/tmp/'+label+'-'+mode+'-actual1.json');d=json.loads(j.read_text());assert d['actual_exit_code']==0;assert d['source_sha256_before']==d['source_sha256_after']==H(p);assert H(d['log'])==d['log_sha256'];assert H(d['source_snapshot'])==H(p)
  rs.append({'record':str(j),'record_sha256':H(j),'kind':d['kind'],'actual_exit_code':0,'log':d['log'],'log_sha256':d['log_sha256'],'source_snapshot':d['source_snapshot'],'source_snapshot_sha256':d['source_snapshot_sha256']})
 rows.append({'lean_file':str(p.relative_to(R)),'sha256':H(p),'public_declarations':dr,'theorem_count':sum(x['kind'] in ['theorem','lemma'] for x in dr),'actual_execution_records':rs,'imports':re.findall(r'^import\s+(\S+)',p.read_text(),re.M)})
hist=[];hd=R/'reports/full-coverage/source-history/monitoring-growing-blocks22';hd.mkdir(parents=True,exist_ok=True)
for n in ['CompleteModulesMonitoringBlocks22','CompleteModulesMonitoringBlockLimits22']:
 p=R/'verification/lean/SafeLearning'/(n+'.lean');q=hd/(n+'.lean');assert not q.exists();b=p.read_bytes();q.write_bytes(b);assert H(p)==H(q);orig=str(p.relative_to(R));p.unlink();hist.append({'original_path':orig,'preserved_path':str(q.relative_to(R)),'sha256':H(q),'reuse_scope':'Historical actual-zero pre-closure source only; not offered as a current proof. The original compiler JSON/snapshot/log bodies remain unchanged.'})
failed=[]
for prefix,ns in [('modules-monitoring-blocks22-trial',range(1,4)),('modules-monitoring-block-limits22-trial',range(1,7))]:
 for n in ns:
  j=Path('/tmp/'+prefix+str(n)+'.json');d=json.loads(j.read_text());assert d['exit_code']!=0;failed.append({'record':str(j),'record_sha256':H(j),'actual_exit_code':d['exit_code'],'log':d['log'],'log_sha256':H(d['log']),'source_snapshot':d['source_snapshot'],'source_snapshot_sha256':H(d['source_snapshot'])})
units=[x for x in ij['material_source_units'] if x['key'] in ['cmdp.html::node-1138','cmdp.html::node-1139','cmdp.html::node-1140']]
assert len(units)==3;assert sum(x['theorem_count'] for x in rows)==15
obj={'status':'genuine_fixed_source_and_paired_actual_zero_readiness_passed','created_at_utc':datetime.now(timezone.utc).isoformat(),'inventory':str(inv.relative_to(R)),'inventory_sha256':H(inv),'source':'SafeLearning/cmdp.html','source_sha256':H(R/'SafeLearning/cmdp.html'),'proof_files':rows,'counts':{'new_proof_files':2,'public_theorems':15,'paired_actual_zero_records':4,'preserved_actual_failed_trials':len(failed)},'literal_scope':{'whole_unit_candidate':'cmdp.html::node-1140','components_only':['cmdp.html::node-1138','cmdp.html::node-1139'],'entire_literal_inventory_rows':units,'limitations':'This is the genuine growing-block trajectory component and count paragraph only. No whole Exercise8.6, dual-dynamics theorem, all-history maximizer face, stationary Markov average theorem or Saute claim is inferred.'},'passed_pre_closure_history':hist,'preserved_failed_trials':failed,'closure_change':'Distinct filename/namespaces add explicit EOF namespace closure; both old passing source byte sequences are preserved outside the active proof glob. Original execution JSON bodies/times/logs are unchanged. The two current sources have fresh genuine canonical standalone and named executions.','protected21':{'selection':str(sel.relative_to(R)),'selection_sha256':H(sel),'all_selected_source_hashes_checked':len(sj['proof_files']),'held_owner_metadata_mutations':False},'checker':str(Path(__file__)),'checker_sha256':H(__file__)}
j=Path('/tmp/modules-monitoring-growing-blocks22-proof-readiness-v1.json');assert not j.exists();j.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'readiness':str(j),'sha256':H(j),'counts':obj['counts']}))

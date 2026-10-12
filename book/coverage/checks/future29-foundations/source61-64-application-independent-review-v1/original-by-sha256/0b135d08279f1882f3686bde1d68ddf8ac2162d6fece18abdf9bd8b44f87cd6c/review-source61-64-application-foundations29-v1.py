from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book'))
from validate import Document
S='book/coverage/checks/root_apply_source61_64_v1.py'; C='book/coverage/checks/future29-core/source61-64-full29-application-contract-v1.json'; A='reports/full-coverage/source61-64-contract-preparation29-execution-v1.json'
def p(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(n):return hashlib.sha256(p(n).read_bytes()).hexdigest()
def read(n):return json.loads(p(n).read_bytes())
def ref(n):return {'file':n,'sha256':sha(n)}
def check(r):assert p(r['file']).is_file() and not p(r['file']).is_symlink() and sha(r['file'])==r['sha256'];return read(r['file']) if p(r['file']).suffix=='.json' else p(r['file']).read_bytes()
a=read(A); c=read(C)
assert a['status']=='passed' and type(a['actual_exit_code']) is int and a['actual_exit_code']==0
assert a['actual_command']==['python3',S,'prepare'] and a['actual_workdir']==str(R)
assert a['helper_sha256_before']==a['helper_sha256_after']=={S:sha(S)} and sha(a['log'])==a['log_sha256']
assert c['helper']==ref(S) and c['both_parser_ROOT_and_OUT_isolated'] is True and c['coverage_complete'] is False
assert [s['correction_id'] for s in c['steps']]==[61,62,63,64]
assert len({s['source'] for s in c['steps']})==4
closure=check(c['completed28_delivery']);assert closure['status']=='passed_actual_checkpoint28_content_and_metadata_delivery' and closure['metadata_commit']==c['metadata_commit']
for n,h in closure['exact_native_evidence_sha256'].items():assert sha(n)==h
for r in c['original_evidence']:check(r)
for n,h in c['five_owner28_sha256'].items():assert sha(n)==h
assert len(c['five_owner28_sha256'])==5
for n,h in c['all31_source60_assets_sha256'].items():assert sha(n)==h
assert len(c['all31_source60_assets_sha256'])==31
selection=read('reports/full-coverage/checkpoint-28-selection.json');assert len(selection['proof_files'])==1186
for n,r in selection['proof_files'].items():assert sha(n)==r['sha256']
check(c['before_inventory']);check(c['before_corrections'])
expected_keys=[{'exercises':[],'material_source_units':['primer-basics.html::node-1029','primer-basics.html::node-1031','primer-basics.html::node-1142']},{'exercises':[],'material_source_units':['primer-optimization.html::node-200','primer-optimization.html::node-202']},{'exercises':['lipsdp.html::exercise-16'],'material_source_units':['lipsdp.html::node-1293']},{'exercises':[],'material_source_units':['primer-linalg.html::node-141','primer-linalg.html::node-171']}]
for s,expected in zip(c['steps'],expected_keys):
 proposal=check(s['proposal']);peer=check(s['peer']);candidate=check(s['candidate']);old=p(s['source']).read_bytes()
 assert sha(s['source'])==s['source_sha256_before'] and proposal['source']['sha256']==s['source_sha256_before'] and proposal['source']['file']==s['source']
 assert peer['errors']==[] and peer['status'].startswith('passed_independent_')
 assert s['exact_changed_text_keys']==expected and s['counts']==read(c['before_inventory']['file'])['counts']
 new=old.decode()
 for r in s['exact_replacements']:assert new.count(r['before'])==1 and r['after'] not in new;new=new.replace(r['before'],r['after'],1)
 assert new.encode()==candidate
 rev=new
 for r in reversed(s['exact_replacements']):assert rev.count(r['after'])==1;rev=rev.replace(r['after'],r['before'],1)
 assert rev.encode()==old and new.count('\n')==old.decode().count('\n')
 assert [(n.tag,n.attrs,n.line) for n in Document(old.decode()).nodes]==[(n.tag,n.attrs,n.line) for n in Document(new).nodes]
assert sha('book/inventory_claims.py')=='b811c12224b47ec3089f72237600265077b2a46ca93a7eb4cf20ee8d181a140e'
result={'status':'passed_independent_full_source61_to64_application_helper_and_native_preparation_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewed_helper':ref(S),'native_preparation':ref(A),'native_preparation_raw_log':ref(a['log']),'prepared_contract':ref(C),'completed28_delivery':c['completed28_delivery'],'source_steps':[61,62,63,64],'four_distinct_sources_exact_forward_inverse_and_node_identity':True,'native_four_cumulative_full29_parser_runs_complete_before_preservation_or_live_source_write':True,'parser_ROOT_and_OUT_isolated_verified_from_full_pinned_implementation':True,'five_owner28_and_all1186_selected_proof_sources_unchanged_at_reader':True,'original_proposals_peers_native_bodies_logs_and_times_preserved_by_exact_byte_refs':True,'apply_not_invoked_by_reviewer':True,'scope':'Full helper and pinned dependencies read. Genuine Root preparation is actual0; actual apply remains unexecuted and belongs to Root. Original native records retain their own historical context. No new coverage promotion.','coverage_complete':False}
p('/tmp/source61-64-application-independent-foundations29-findings-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'errors':[],'steps':[61,62,63,64]}))

from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/foundations-basics-bibliography8-classification28-v1');C=Path('/tmp/root_tmp_lean_current60_owner28_context_v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def stamp():return datetime.now(timezone.utc).isoformat()
def ref(p):return {'file':str(p),'sha256':sha(p)}
def guard():
 d=json.loads(C.read_text());assert sha(C)=='35ac327b8d62c70dd9e0f83236716ee465d9b188cf656c58be97078b3eea5054'
 pins={**d['pins_sha256'],**d['held_current_source_sha256']}
 for n,h in pins.items():assert sha(R/n)==h,n
 return pins
start=stamp();before=guard();assert not OUT.exists();OUT.mkdir()
owner=json.loads((R/'book/coverage/foundations.json').read_text());inv=json.loads((R/'book/coverage/inventory.json').read_text())
old=R/'reports/full-coverage/checkpoint-28/book/coverage/foundations.json';assert sha(old)==sha(R/'book/coverage/foundations.json')
base=R/'reports/full-coverage/checkpoint-28/SafeLearning/primer-basics.html';assert sha(base)==sha(R/'SafeLearning/primer-basics.html')
facts=Path('/tmp/foundations-basics-bibliography-eight-primary-factual-observations28-v1.json');fd=json.loads(facts.read_text());assert len(fd['rows'])==8
nodes=[1648,1654,1660,1666,1672,1678,1684,1690];units={u['key']:u for u in inv['material_source_units']}
rows=[]
for fact in fd['rows']:
 n=fact['node'];assert n in nodes;key=f'primer-basics.html::node-{n}'
 matches=[x for x in owner['material_claims'] if x['source_unit_keys']==[key]];assert len(matches)==1
 oldrow=matches[0];assert oldrow['status']=='pending' and oldrow['lean_declarations']==[]
 assert units[key]['text_sha256']==oldrow['source_text_sha256']
 new=dict(oldrow);new.update(kind='individually_reviewed_bibliographic_and_curricular_reference',status='not_a_formal_claim',statement_in_prose=oldrow['source_text'],hypotheses=[],lean_declarations=[],remaining_gaps=[],correspondence=fact['classification_reason']+' Verified primary facts: '+fact['facts']+' Scope qualification: '+fact['qualification'])
 rows.append({'source_unit_key':key,'original_row':oldrow,'proposed_row':new,'primary_factual_observation':fact,'new_math_proof_or_external_whole_book_approval':False})
receipts=[];offline={};endpoints=[]
for folder in ['foundations-basics-eight-primary-bibliography28-v1','foundations-basics-primary-followups28-v1','foundations-basics-primary-chapter-checks28-v1']:
 p=Path('/tmp')/folder/'primary-http-receipts-v1.json';d=json.loads(p.read_text());assert d['protection_errors']==[] and d['protected_before']==d['protected_after'] and len(d['protected_before'])==1223
 receipts.append(ref(p))
 for r in d['results']:
  endpoints.append({'receipt_id':r['id'],'error':r.get('error'),'http_status':r.get('http_status'),'bytes':r.get('bytes')})
  if 'offline_file' in r:
   op=Path(r['offline_file']);assert sha(op)==r['sha256'];offline[str(op)]=r['sha256']
  if 'offline_text' in r:
   q=Path(r['offline_text']['file']);assert sha(q)==r['offline_text']['sha256'];assert type(r['text_conversion']['exit_code']) is int and r['text_conversion']['exit_code']==0;offline[str(q)]=sha(q)
assert len(rows)==8 and len({r['source_unit_key'] for r in rows})==8
preview=dict(owner['counts']['material_claim_statuses']);preview['pending']-=8;preview['not_a_formal_claim']+=8
ctx='\n'.join((R/'SafeLearning/primer-basics.html').read_text().splitlines()[1674:1698])
out={'schema_version':1,'status':'author_bounded_bibliographic_classification_proposal_requires_independent_full_literal_review','reviewer':'/root/foundations_recovery28','reader_started_at_utc':start,'reviewed_at_utc':stamp(),'original_owner':ref(old),'original_source':ref(base),'current_inventory':ref(R/'book/coverage/inventory-after-correction60.json'),'source_context':{'lines':[1675,1698],'text':ctx,'sha256':hashlib.sha256(ctx.encode()).hexdigest()},'rows':rows,'own_primary_factual_observations':ref(facts),'original_http_receipts':receipts,'offline_remote_originals_sha256':offline,'primary_endpoint_observations':endpoints,'historical_http_guard_scope':'1186 selected sources,29 HTML inputs,five owners,selection,inventory,corrections; these historical receipts do not claim the two extra CSS/JS assets were included in their guards.','current_author_guard_scope':{'selected_sources':1186,'source_browser_assets':31,'installed_owners':5},'proposed_local_count_preview_if_independently_approved':preview,'exercise_count_and_statuses':owner['counts']['exercise_statuses'],'inventory_units_dropped':0,'original_rows_and_all_other_live_owner_data_unchanged':True,'publication_of_remote_book_content_authorized_or_performed':False,'external_mathematical_topics_and_proof_obligations_remain_in_their_other_inventoried_units':True,'lean_compilation_or_math_whole_approval_claimed':False,'live_ledger_or_candidate_or_html_or_git_writer_executed':False,'coverage_complete':False,'errors':[]}
q=OUT/'foundations-basics-bibliography8-full-literal-classification-request28-v1.json';q.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');after=guard();assert before==after
print(json.dumps({'status':'passed_readonly_author_proposal','request':ref(q),'guard_count':len(before),'eight_exact_rows':8,'source_assets':31,'protected_errors':[],'count_preview_only':preview}))

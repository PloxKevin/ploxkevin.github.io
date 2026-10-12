from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');Q=R/'book/coverage/checks/future29-core/editorial13-v1/core-editorial13-full-literal-review-request29-v1.json';O=Path('/tmp/core-editorial13-independent-modules29-peer-original-v1.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not O.exists();start=datetime.now(timezone.utc).isoformat();q=json.loads(Q.read_bytes())
inv=json.loads((R/'book/coverage/inventory.json').read_bytes());units={u['key']:u for u in inv['material_source_units']};owner=json.loads((R/'book/coverage/core.json').read_bytes())
assert sha(R/q['core_owner']['file'])==q['core_owner']['sha256'] and sha(R/q['inventory']['file'])==q['inventory']['sha256']
assert len(q['literal_rows'])==13 and q['live_owner_or_source_changes'] is False
for n,h in q['source_sha256'].items():assert sha(R/n)==h
contexts=[];decisions=[]
for row in q['literal_rows']:
 old=row['original'];key=old['source_unit_keys'][0];u=units[key]
 assert old in owner['material_claims'] and old['status']=='pending' and old['lean_declarations']==[]
 assert old['source_text']==u['source_text'] and old['source_sha256']==u['source_sha256'] and old['text_sha256']==u['text_sha256']
 assert row['requested_status']=='not_a_formal_claim' and row['lean_declarations']==[]
 lines=(R/u['source']).read_text().splitlines();a=max(1,u['line']-2);b=min(len(lines),u['line']+2)
 contexts.append({'key':key,'source':u['source'],'line':u['line'],'context_lines':[a,b],'exact_full_source_context':'\n'.join(lines[a-1:b])})
 d={'claim_id':old['id'],'source_unit_key':key,'entire_literal_classification_approved':True,'approved_status':'not_a_formal_claim','lean_declarations':[],'rationale':row['classification_reason'],'classification_does_not_certify_mathematical_or_citation_truth':True}
 if key=='open-problems.html::node-16':d['explicit_excluded_scope']='The temporal assertion that all listed questions remain unsolved as of autumn2026 is NOT verified or endorsed. This is an editorial scope subtitle, not a reviewed research-status fact. Each substantive open-question claim and worked example remains separate and pending its own factual/mathematical review.'
 if key=='papers.html::node-13':d['explicit_excluded_scope']='Advice to consult a Key Papers table does not independently validate its bibliographic entries, publication dates, venues or claimed mathematical contributions.'
 if key=='formulas.html::node-16':d['explicit_excluded_scope']='The subtitle word All is not a completeness theorem or a guarantee that every displayed formula is valid without its hypotheses.'
 if key=='cmdp.html::node-68':d['explicit_excluded_scope']='The adjacent worked geometric-series sum, normalized occupancy identity and dual sign formula are separate mathematical literals and receive no approval here.'
 decisions.append(d)
print(json.dumps({'read_full_literals':len(decisions),'scope':'editorial only; no mirror tests or live changes'}))
d={'status':'passed_independent_core_editorial13_full_literal_nonformal_classification_review','errors':[],'reviewer':'/root/modules_finish28','reader_started_at_utc':start,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':{'file':str(Q.relative_to(R)),'sha256':sha(Q)},'individual_full_literal_decisions':decisions,'entire_thirteen_literal_source_contexts':contexts,'all_thirteen_original_live_pending_rows_exact':True,'no_mathematical_guarantee_exercise_citation_or_temporal_unsolved_status_promoted':True,'source_hashes':q['source_sha256'],'inventory_sha256':q['inventory']['sha256'],'core_owner_sha256':q['core_owner']['sha256'],'meaningful_scope':'Read complete literals, exact contextual DOM source, complete matching original owner rows and inventory records. Navigation/control/study classifications only. No mirror tests are warranted.','current_owners_or_sources_or_selection_changed':False,'compiler_started':False,'coverage_complete':False}
O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')

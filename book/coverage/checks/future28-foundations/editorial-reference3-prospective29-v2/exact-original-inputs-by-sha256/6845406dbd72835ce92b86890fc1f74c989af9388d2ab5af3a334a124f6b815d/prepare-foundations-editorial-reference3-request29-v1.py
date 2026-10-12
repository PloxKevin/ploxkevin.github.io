from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy,sys,re
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future28-foundations/editorial-reference3-prospective29-v1';assert not D.exists()
sys.path.insert(0,str(R/'book'));from validate import Document,clean_text
CTX=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json');context=json.loads(CTX.read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def ref(p):
 p=Path(p);return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p)}
def guard():
 for fld in ['pins_sha256','held_current_source_sha256','owners_sha256']:
  for n,h in context[fld].items():assert sha(Path(n) if Path(n).is_absolute() else R/n)==h,n
 return {k:copy.deepcopy(context[k]) for k in ['pins_sha256','held_current_source_sha256','owners_sha256']}
start=datetime.now(timezone.utc).isoformat();before=guard();inv=read(R/'book/coverage/inventory-after-correction65.json');owner=read(R/'book/coverage/foundations.json')
oldcontexts=Path('/tmp/foundations-editorial-reference3-full-target-contexts29-v1.json');raw=read(oldcontexts);assert len(raw)==3
units={u['key']:u for u in inv['material_source_units']};base=D.relative_to(R).as_posix();copies={};planned={};allrefs={}
def archived(p):
 p=Path(p);h=sha(p);n=D/'exact-original-inputs-by-sha256'/h/p.name
 if n in planned:assert planned[n]==p.read_bytes()
 planned[n]=p.read_bytes();r={'file':n.relative_to(R).as_posix(),'sha256':h};copies[str(p)]=r;allrefs[r['file']]=h;return r
contextref=archived(CTX);historicalcontexts=archived(oldcontexts)
patterns=[['open|interior|boundary','regular value','regular|nonzero|gradient|boundary','closed|failure','compact|annul','compact|region of interest','compact','minimi|attain','projection|QP|argmin|minimi','attain|compact','covering|tau|net','net|grid|subdiffer','grid|discret'],['ridge','inverse|Exercise 3.3','conjugate|Fisher|CG|Hessian','log.*det|tr\\(','Parseval|Cayley|gradient|inverse','sensitivity|sensitivities|KKT|implicit'],['positive semidefinite|Hessian','strong.*convex','convex.*potential|antiderivative','monotone|monotonic','subdiffer|superdiffer']]
decisions=[];contexts=copy.deepcopy(raw)
reasons={
 'primer-basics.html::node-1179':'The complete leaf div is a curricular map naming topology/attainment/covering topics and their module locations. It states no additional quantified mathematical implication, definition or theorem. Each mentioned concept has an exact target passage; mathematical assertions and regularity/attainment assumptions in the target sections remain separate inventoried obligations. This classification covers only this reference row.',
 'primer-optimization.html::node-380':'The complete leaf div lists uses of matrix calculus and links to the module sections that use those operations. The displayed beta(WW^T-I)W is the identifying formula of the separately inventoried Primer B Exercise B.2 (exercise30), whose current complete_math row and selected proof declarations are retained. It is a curricular citation rather than a second new gradient theorem; every referenced derivative, inverse expansion and application hypothesis remains subject to its existing separate exercise/material record.',
 'primer-optimization.html::node-738':'The complete list item names uses of convex-function concepts in linked sections: PSD Hessians, strong convexity, convex potentials, monotone relations and generalized differentials. It asserts no new universal result about those applications. The exact target passages and their hypotheses are retained; none of their mathematical content is classified or promoted by excluding this navigation row from formal claims.'}
for row,pats in zip(contexts,patterns):
 u=units[row['entire_literal']['key']];assert row['entire_literal']==u;indices=[i for i,r in enumerate(owner['material_claims']) if r['status']=='pending' and u['key'] in r['source_unit_keys']];assert len(indices)==1
 doc=Document((R/u['source']).read_text());node=doc.nodes[int(u['locator'].removeprefix('::node-'))-1];assert node.text()==u['source_text']
 actualhrefs=[n.attrs['href'] for n in node.descendants('a')];assert actualhrefs==[l['href'] for l in row['links']]
 topic=[]
 for link,pat in zip(row['links'],pats):
  p=R/link['source'];lines=p.read_text().splitlines(keepends=True);fragment=''.join(lines[link['line_start']-1:link['line_end']-1]);assert fragment==link['entire_linked_section_html']
  link['source_sha256']=sha(p);assert inv['source_sha256'][link['source']]==sha(p);allrefs[link['source']]=sha(p)
  section=Document(fragment);hits=[]
  for n in section.nodes:
   if n.tag not in ['p','li','div']:continue
   if re.search(pat,clean_text(n.text()),re.I):
    if any(k.tag in ['p','li','div','details','section','table'] and re.search(pat,clean_text(k.text()),re.I) for k in n.descendants()):continue
    hits.append({'tag':n.tag,'line':link['line_start']+n.line-1,'exact_text':n.text(),'text_sha256':hashlib.sha256(n.text().encode()).hexdigest()})
  assert hits,link['href'];topic.append({'href':link['href'],'source':ref(p),'complete_section_line_start':link['line_start'],'complete_section_line_end_exclusive':link['line_end'],'topic_regex_used_for_reader_index_only':pat,'entire_matching_topic_nodes':hits})
 decisions.append({'source_unit_key':u['key'],'entire_source_unit':u,'original_pending_owner_row_index':indices[0],'original_entire_pending_owner_row':copy.deepcopy(owner['material_claims'][indices[0]]),'proposed_classification':'not_a_formal_claim','proposed_kind':'individually_reviewed_curricular_reference_row','individual_scope_reason':reasons[u['key']],'exact_linked_topic_passages':topic,'independent_approval_pending':True,'formal_math_or_exercise_coverage_approval_claimed':False})
sourcecontexts=D/'foundations-editorial-reference3-full-linked-contexts-current65-v2.json';planned[sourcecontexts]=(json.dumps(contexts,indent=2)+'\n').encode();contextsref={'file':sourcecontexts.relative_to(R).as_posix(),'sha256':hashlib.sha256(planned[sourcecontexts]).hexdigest()};allrefs[contextsref['file']]=contextsref['sha256']
oldowner=R/'reports/full-coverage/checkpoint-28/book/coverage/foundations.json';assert sha(oldowner)==sha(R/'book/coverage/foundations.json');allrefs[oldowner.relative_to(R).as_posix()]=sha(oldowner)
inventoryref=ref(R/'book/coverage/inventory-after-correction65.json');allrefs[inventoryref['file']]=inventoryref['sha256']
ex=[e for e in owner['exercises'] if e['inventory_key']=='primer-optimization.html::exercise-30'];assert len(ex)==1 and ex[0]['status']=='complete_math'
proofs=[ref(R/'verification/lean/SafeLearning/CompleteFoundationsParsevalModels.lean'),ref(R/'verification/lean/SafeLearning/CompleteFoundationsParsevalTrace.lean')]
for p in proofs:allrefs[p['file']]=p['sha256']
request={'status':'prospective_three_individual_full_curricular_reference_classifications_pending_independent_review','errors':[],'started_at_utc':start,'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'current_inventory':inventoryref,'original_entire_owner28':ref(oldowner),'individual_full_literal_proposed_decisions':decisions,'all24_complete_linked_sections':contextsref,'old_source64_linked_contexts_exact_original':historicalcontexts,'parseval_exercise_B2_disambiguation':{'scope':'This is Primer B original Exercise B.2 exercise30, not Module13 B.2. The existing complete_math record and two selected sources are supplied to identify the separate formal obligation; no fresh independent whole-exercise approval is asserted.','entire_existing_exercise_row':ex[0],'selected_sources':proofs},'guard_context':contextref,'required_evidence_artifacts_sha256':allrefs,'exact_original_byte_aliases':copies,'preview_only_new_reference_row_count':3,'new_proof_or_exercise_or_whole_math_promotion_count':0,'all_inventory_units_and_current_live_statuses_retained':True,'independent_full_classification_peer_pending':True,'coverage_complete':False,'current_owner_source_canonical_selection_publication_mutated':False,'scope':'Only three exact navigation/reference rows. Full target mathematics remains in its own inventory and ledger queue. No blanket editorial exclusion, no whole target section or theorem approval, and no live ledger changes.'}
reqpath=D/'foundations-editorial-reference3-full-literal-classification-request29-v1.json';planned[reqpath]=(json.dumps(request,indent=2)+'\n').encode();assert guard()==before
for p,b in planned.items():assert p.is_relative_to(D) and not p.exists()
for p,b in planned.items():p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
assert guard()==before
print(json.dumps({'request':ref(reqpath),'full_linked_contexts':contextsref,'exact_unit_count':3,'actual_link_count':sum(len(r['links']) for r in contexts),'required_evidence_count':len(allrefs),'original_bytes_aliases':copies,'scope':request['scope'],'coverage_complete':False}))

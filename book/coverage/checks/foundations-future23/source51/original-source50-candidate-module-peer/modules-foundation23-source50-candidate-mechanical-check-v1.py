"""Independent readonly mapping mechanics; mathematical peer bodies remain exact."""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import hashlib,json,copy,re
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/foundations-future23/source50'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());ref=lambda p:{'file':str(Path(p).relative_to(R)) if Path(p).is_relative_to(R) else str(p),'sha256':H(p)}
offerpath=B/'foundations-audit23-candidate-source50-additions-v1.json';assert H(offerpath)=='dcc4056b55caecf0ec0068918fe56cc779f1833f5df95ff5dbe6cb791220775a';offer=J(offerpath)
candpath=R/offer['mapped_ledger'];assert H(candpath)==offer['mapped_ledger_sha256']=='ab48adca29ae6bc13fe87466700e07cb0b6112a2668ad494b98a6a4a34a93c79';cand=J(candpath)
bindpath=R/offer['material23_exact_interface_binding'];assert H(bindpath)==offer['material23_exact_interface_binding_sha256']=='99bad47ce7dcfc716e2da475ea0be820c01745b348f860d9bb73bc6e500e4b9c';binding=J(bindpath)
oldpath=R/offer['held22_ledger'];old=J(oldpath);assert H(oldpath)==offer['held22_ledger_sha256']==offer['working22_ledger_sha256']==H(R/offer['working22_ledger'])=='305229a7e1df78c23bc1af728c7f3f4e0ac09d13c55e4e687fe721160b43bf88'
inv48=J(R/'book/coverage/inventory-after-correction48.json');inv50path=R/offer['current_inventory'];assert H(inv50path)==offer['current_inventory_sha256']=='dec8a34d0313fbc19846489f4d8c2f6e51734a135df6145829993fae0f80d91c';inv50=J(inv50path);current=J(R/'book/coverage/inventory.json')
for kind,expected in [('exercises',119),('material_source_units',1756)]:
 rows=lambda inv:{r['key']:r for r in inv[kind] if r['source'] in old['scope_pages']}
 assert rows(inv48)==rows(inv50)==rows(current) and len(rows(inv48))==expected
for n,d in cand['source_sha256'].items():assert H(R/n)==d==old['source_sha256'][n]
assert cand['exercises']==old['exercises'] and len(cand['exercises'])==119 and cand['surrounding_prose_reviews']==old['surrounding_prose_reviews']
assert cand['proof_files']==sorted(old['proof_files']+list(offer['proof_files'])) and len(cand['proof_files'])==237 and len(old['proof_files'])==234
assert set(cand['proof_sha256'])==set(old['proof_sha256'])|set(offer['proof_files'])
for n,d in old['proof_sha256'].items():assert cand['proof_sha256'][n]==d and H(R/n)==d
for mapname in ['exact_source_reviews_sha256','actual_canonical_execution_records_sha256','canonical_readiness_sha256','canonical_source_peer_bindings_sha256']:
 for n,d in offer[mapname].items():assert H(R/n)==d
for p in offer['canonical_source_binding_reviews_with_original_bodies_and_times']:assert J(R/p['reference']['file'])==p['entire_original_body_and_time'] and H(R/p['reference']['file'])==p['reference']['sha256']
# Enriched offer is only builder/binding provenance added to immutable draft.
draftpath=R/offer['original_prepared_draft']['file'];assert H(draftpath)==offer['original_prepared_draft']['sha256']=='9fe17fd2e46b864bba9ba7b32644df971c577468136a110b4edd80bfabeab7ce';draft=J(draftpath)
back=copy.deepcopy(offer)
for k in set(back)-set(draft):del back[k]
for k in ['actual_builder_record_pending','scope']:back[k]=draft[k]
assert back==draft
expath=R/offer['actual_builder_record'];assert H(expath)==offer['actual_builder_record_sha256'];ex=J(expath);assert ex['actual_exit_code']==0
assert ex['actual_command']==['python3',offer['current_owner_builder']]
assert H(R/offer['current_owner_builder'])==offer['current_owner_builder_sha256']==ex['actual_checker_sha256_before']==ex['actual_checker_sha256_after']
assert H(R/offer['actual_builder_raw_log']['file'])==offer['actual_builder_raw_log']['sha256']==ex['log_sha256']
assert ex['log']==offer['actual_builder_raw_log']['file']
units={u['key']:u for u in inv50['material_source_units']};newids=set();removedids=set();all_decl=set();seen=set()
for p in binding['proof_packets']:
 source=R/p['source']['file'];assert H(source)==p['source']['sha256'];names=['SafeLearning.'+p['module']+'.'+n for n in re.findall(r'^theorem\s+(\w+)',source.read_text(),re.M)]
 assert names==p['public_theorem_names'] and len(names)==p['new_public_theorem_count'];all_decl.update(names)
 proof=offer['proof_files'][p['source']['file']];assert proof['sha256']==H(source)==cand['proof_sha256'][p['source']['file']]
 expected_evidence={}
 for index,pair in enumerate(p['actual_pair']):
  a=J(R/pair['reference']['file']);assert a==pair['entire_original_actual_record'] and H(R/pair['reference']['file'])==pair['reference']['sha256']
  assert a['actual_exit_code']==0 and a['source_sha256_before']==a['source_sha256_after']==H(source)
  assert a['command']==(['lake','env','lean','SafeLearning/'+p['module']+'.lean'] if index==0 else ['lake','build','SafeLearning.'+p['module']])
  assert H(R/a['log'])==a['log_sha256'] and H(R/a['preserved_source'])==a['preserved_source_sha256']==H(source)
  expected_evidence.update({pair['reference']['file']:pair['reference']['sha256'],a['log']:a['log_sha256'],a['preserved_source']:H(source)})
 assert expected_evidence==proof['evidence_sha256']
for m in binding['material_units']:
 key=m['source_unit_key'];assert key not in seen;seen.add(key);assert m['entire_current50_inventory_record']==units[key]
 peer=J(R/m['original_semantic_review']['file']);assert H(R/m['original_semantic_review']['file'])==m['original_semantic_review']['sha256'] and peer['reviewed_at_utc']==m['original_reviewed_at_utc']
 originalrow=next(r for r in peer['material_units'] if r['source_unit_key']==key);assert originalrow==m['original_unchanged48_or49_entire_unit_peer_row']
 row=m['new_candidate_claim'];assert row in cand['material_claims'] and row['lean_declarations']==originalrow['lean_declarations'] and row['hypotheses']==originalrow['hypotheses'] and row['correspondence']==originalrow['per_unit_reason']
 assert row['source_text']==units[key]['source_text'] and row['source_text_sha256']==units[key]['text_sha256'] and row['status']=='proved' and row['remaining_gaps']==[]
 assert originalrow['whole_unit_approved'] and originalrow['missing_clauses']==[] and row['source_review']['reviewed_at_utc']==peer['reviewed_at_utc']
 oldrows=[r for r in old['material_claims'] if key in r['source_unit_keys']]
 assert [r for r in oldrows if r['status']=='pending']==m['entire_original_pending_clauses']
 assert [r for r in oldrows if r['status']!='pending']==m['retained_original_proved_or_nonformal_clauses']
 removedids.update(r['id'] for r in m['entire_original_pending_clauses']);newids.add(row['id'])
assert len(seen)==14 and len(removedids)==15 and len(all_decl)==39
assert set(d for m in binding['material_units'] for d in m['new_candidate_claim']['lean_declarations'])==all_decl
assert [r for r in cand['material_claims'] if r['id'] not in newids]==[r for r in old['material_claims'] if r['id'] not in removedids]
assert len([r for r in old['material_claims'] if r['status']=='proved'])==1080
reverse=copy.deepcopy(cand)
reverse['material_claims']=old['material_claims'];reverse['proof_files']=old['proof_files'];reverse['proof_sha256']=old['proof_sha256'];reverse['counts']=old['counts'];reverse['limits']=old['limits']
del reverse['current23_owner_identity'];del reverse['current23_material_mapping'];assert reverse==old
manifestpath=R/'reports/full-coverage/checkpoint-22-manifest.json';manifest=J(manifestpath);assert len(manifest['proof_files'])==1113
for n,r in manifest['proof_files'].items():assert H(R/n)==r['sha256']
for n,d in manifest['working_inputs_sha256'].items():
 if n.startswith('SafeLearning/'):assert H(R/manifest['snapshot']/n)==d
 if n in ['book/coverage/core.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/foundations.json']:assert H(R/n)==d
counts={'old_entire_exercises':119,'owned_entire_inventory_material_records':1756,'old_proved_atoms':1080,'whole_new_units':14,'removed_pending_rows':15,'new_sources':3,'new_theorem_exports':39,'proof_rows':237,'physical_whole_proved':762,'physical_nonformal':524,'physical_pending':470}
report={'status':'independent_isolated_candidate_original_semantics_and_exact_inventory_mapping_confirmation_passed','reviewer':'/root/modules_resume','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_offer':ref(offerpath),'candidate_ledger':ref(candpath),'exact_interface_binding':ref(bindpath),'held_original22_ledger':ref(oldpath),'actual_original_candidate_builder':ref(expath),'checked_counts':counts,'entire119_exercises_1080_proved_atoms_1756_source_records_and_original_review_times_preserved':True,'exact_inverse_restores_entire_original22_ledger':True,'all_three_actual_pairs_and_original_semantic_canonical_peer_bodies_exact':True,'observed_current_inventory':ref(R/'book/coverage/inventory.json'),'historical_candidate_inventory':ref(inv50path),'all1113_selected22_sources_frozen31_assets_four_live22_ledgers_exact':True,'actual_checker':ref(Path(__file__)),'errors':[],'limits':['Isolated candidate and evidence mapping mechanics only; original complete semantic reviews and times remain immutable.','No live ledger installation, aggregate23, global23 validation or automatic parent-exercise theorem closure is inferred. Candidate remains bound to immutable source50; current Foundation entire literal records are additionally checked unchanged.']}
out=Path('/tmp/foundations23-source50-candidate-independent-modules-mechanical-confirmation-v1.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'report':str(out),'sha256':H(out),'status':report['status']}))

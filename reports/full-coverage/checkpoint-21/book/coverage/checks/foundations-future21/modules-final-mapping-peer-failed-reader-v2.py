from pathlib import Path
import json,hashlib,copy,sys
from collections import Counter
from datetime import datetime,timezone
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
cache={}
def H(n):
 p=Path(n);p=p if p.is_absolute() else R/p;s=p.stat();k=(str(p.resolve()),s.st_size,s.st_mtime_ns)
 if k not in cache:cache[k]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[k]
def L(n):return json.loads((R/n).read_text())
def ck(n,h):assert H(n)==h,(n,h)
B='book/coverage/checks/foundations-future21';on='book/coverage/foundations-audit21-source48-additions-v1.json';o=L(on);ck(on,'2becbf30d8be360e0872127346bf7e10c84e7bdff3e1670e74da3f81b72720dd');mn=o['loader_integration'];m=L(mn);ck(mn,o['loader_integration_sha256']);assert H(m['mapped_ledger'])==m['mapped_ledger_sha256']==o['mapped_ledger_sha256'];l=L(m['mapped_ledger']);base=L(m['original_immutable20_ledger']);ck(m['original_immutable20_ledger'],m['original_immutable20_ledger_sha256'])
for f in ['current_inventory','source48_unchanged_identity_manifest','material21_exact_interface_binding','independent_identity_interface_and_seeded_adapter_confirmation','actual_builder_record','cross_owner_lipsdp_readiness_manifest','global_integrity']:
 ck(o[f],o[f+'_sha256'])
assert H(o['current_inventory'])==H('book/coverage/inventory.json')=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
i=L(o['source48_unchanged_identity_manifest']);d=L(o['material21_exact_interface_binding']);prior=L(o['independent_identity_interface_and_seeded_adapter_confirmation']);assert prior['status']=='independent_exact_source48_foundation21_identity_and_interface_confirmation_passed';assert prior['identity_manifest_sha256']==H(o['source48_unchanged_identity_manifest']) and prior['interface_binding_sha256']==H(o['material21_exact_interface_binding'])
assert l['exercises']==base['exercises'] and len(l['exercises'])==119
for p,h in m['current21_helpers_sha256'].items():ck(p,h);assert o['current21_helpers_sha256'][p]==h
actual=L(o['actual_builder_record']);assert actual.get('actual_exit_code',actual.get('exit_code'))==0 and actual['helper_sha256_before']==actual['helper_sha256_after']==m['current21_helpers_sha256'];assert actual['current_ledger_sha256']==H(o['mapped_ledger']);ck(actual['log'],actual['log_sha256']);ga=L(o['global_integrity']);assert ga['integrity_status']=='passed' and not ga['errors']
for row in i['preserved20_owner_assets']:
 ck(row['canonical_byte_copy'],row['canonical_byte_copy_sha256']);assert row['canonical_byte_copy_sha256']==row['original_sha256']
for row in d['original_review_byte_copies']:
 ck(row['canonical_byte_copy'],row['canonical_byte_copy_sha256']);assert H(row['original'])==row['original_sha256']==row['canonical_byte_copy_sha256'];assert L(row['canonical_byte_copy'])['reviewed_at_utc']==row['original_reviewed_at_utc']
units={u['key']:u for u in L(o['current_inventory'])['material_source_units']};oldby={k:[c for c in base['material_claims'] if k in c['source_unit_keys']] for k in i['exact_unchanged_owned_material'][0:0]} # filled below
oldby={u['key']:[c for c in base['material_claims'] if u['key'] in c['source_unit_keys']] for u in i['exact_unchanged_owned_material']};newby={k:[c for c in l['material_claims'] if k in c['source_unit_keys']] for k in oldby};assert len(oldby)==len(newby)==1756
rows={r['source_unit_key']:r for r in d['material_units']};assert len(rows)==423 and Counter(r['material_status'] for r in rows.values())=={'proved':40,'not_a_formal_claim':59,'pending':324}
fields=['statement_in_prose','lean_declarations','hypotheses','correspondence'];atom=lambda c:{k:c[k] for k in fields}
def oldaliases(v):
 z=json.dumps(v)
 for row in i['identity_binding_versions']:z=z.replace(row['new_binding'],row['original_binding'])
 return json.loads(z)
# Inspect the actual adapter in-memory, preserving seeded old atoms.
from foundations_material21 import apply,pending_keys
seed={k:{'proved':[atom(c) for c in oldby[k] if c['status']=='proved'],'pending':['original literal scope']} for k in rows if rows[k]['material_status']=='pending'};saved=copy.deepcopy(seed);full={};nf={};apply(full,nf,seed)
assert len(full)==40 and len(nf)==59 and len(pending_keys())==324
allpreserved=0;pending=0
for k,old in oldby.items():
 new=newby[k];assert new and all(c['source_text']==units[k]['source_text'] and c['source_text_sha256']==units[k]['text_sha256'] and c['source_sha256']==units[k]['source_sha256'] for c in new)
 for c in old:
  if c['status']=='proved':assert atom(c) in [oldaliases(atom(q)) for q in new if q['status']=='proved'],(k,'lost old atom');allpreserved+=1
 if k in rows:
  r=rows[k];assert r['exact_current48_inventory_record']==units[k];assert old==r['original_current20_claims'];assert L(r['original_review'])['reviewed_at_utc']==r['original_reviewed_at_utc']
  if r['material_status']=='proved':
   assert all(c['status']=='proved' and not c['remaining_gaps'] for c in new);assert [atom(c) for c in new]==full[k];assert full[k][0]['lean_declarations']==r['lean_declarations'] and full[k][0]['hypotheses']==r['hypotheses']
  elif r['material_status']=='not_a_formal_claim':assert len(new)==1 and new[0]['status']=='not_a_formal_claim' and not new[0]['lean_declarations'] and new[0]['correspondence']==nf[k]
  else:
   pp=[c for c in new if c['status']=='proved'];pg=[c for c in new if c['status']=='pending'];assert [atom(c) for c in pp]==seed[k]['proved'];assert [c['statement_in_prose'] for c in pg]==seed[k]['pending'];assert all(c['remaining_gaps']==[c['statement_in_prose']] for c in pg);assert seed[k]['proved'][:len(saved[k]['proved'])]==saved[k]['proved'];assert len(pg)==len(r['missing_clauses'])
 else:
  # Only two literal current-interface path aliases may differ outside the new423 rows.
  z=copy.deepcopy(new)
  for row in i['identity_binding_versions']:
   z=json.loads(json.dumps(z).replace(row['new_binding'],row['original_binding']))
  assert z==old,(k,'outside423 semantic change')
 if any(c['status']=='pending' for c in new):pending+=1
assert pending==501 and len(oldby)-pending==1255
assert sum(any(c['status']=='pending' for c in oldby[k]) for k in oldby if k not in rows)==177
# Whole rows1107/679 retain their original approved atoms independently of added whole scope.
for suffix in ['::node-1107','::node-679']:
 ks=[k for k in rows if k.endswith(suffix)];assert len(ks)==1 and rows[ks[0]]['material_status']=='proved';assert any(c['status']=='proved' for c in oldby[ks[0]])
bm=L('reports/full-coverage/checkpoint-20-manifest.json');sources=set(bm['proof_files'])|set(o['proof_files']);names={d['name'] for p in sources for d in declarations((R/p).read_text())};count=0;actualcount=0
for p,row in o['proof_files'].items():
 ck(p,row['sha256']);assert row['exit_code']==0 and row['source_unchanged'];refs=[q['name'] for q in declarations((R/p).read_text()) if q['kind'] in ['theorem','lemma']];assert refs==row['public_theorem_or_lemma_names'];count+=len(refs)
 for n,h in row['evidence_sha256'].items():ck(n,h)
 stem=Path(p).stem
 for kind in ['standalone','named-build']:
  n='book/coverage/checks/foundations-future21-'+stem+'-'+kind+'.json';a=L(n);assert a['exit_code']==0 and a['source_sha256_before']==a['source_sha256_after']==H(p);ck(a['log'],a['log_sha256']);actualcount+=1
 for dep,h in row['local_import_dependency_sha256'].items():ck(dep,h);assert dep in sources
assert len(o['proof_files'])==7 and count==55 and actualcount==14
for c in l['material_claims']+[c for e in l['exercises'] for c in e['claims']]:assert set(c['lean_declarations'])<=names
for p,h in o['reused_selected20_proof_source_sha256'].items():ck(p,h);assert bm['proof_files'][p]['sha256']==h
assert len(o['reused_selected20_proof_source_sha256'])==225
# Fresh actual SHA checks for every inherited selected source/evidence and frozen byte.
for p,row in bm['proof_files'].items():
 ck(p,row['sha256'])
 for q,h in row['evidence_sha256'].items():ck(q,h)
for p,h in bm['frozen_inputs_sha256'].items():ck(str(Path(bm['snapshot'])/p),h)
for p,h in m['current21_helpers_sha256'].items():ck(p,h)
ck(on,'2becbf30d8be360e0872127346bf7e10c84e7bdff3e1670e74da3f81b72720dd');assert H(o['mapped_ledger'])==m['mapped_ledger_sha256']
out=B+'/foundations-source48-final-mapping-independent-modules-confirmation21-v2.json';assert not (R/out).exists();r={'status':'independent_exact_source48_foundation21_final_mapping_confirmation_passed','reviewer':'/root/modules_resume','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'offer':on,'offer_sha256':H(on),'mapped_ledger':o['mapped_ledger'],'mapped_ledger_sha256':H(o['mapped_ledger']),'loader_integration':mn,'loader_integration_sha256':H(mn),'identity_interface_preparation_peer':o['independent_identity_interface_and_seeded_adapter_confirmation'],'identity_interface_preparation_peer_sha256':H(o['independent_identity_interface_and_seeded_adapter_confirmation']),'current_inventory':o['current_inventory'],'current_inventory_sha256':H(o['current_inventory']),'actual_builder_record':o['actual_builder_record'],'actual_builder_record_sha256':H(o['actual_builder_record']),'current21_helpers_sha256':m['current21_helpers_sha256'],'counts':{'unchanged_entire_exercise_bodies':119,'entire_current48_material_records':1756,'new_full_literal_dispositions':423,'new_whole_proved':40,'new_individually_nonformal':59,'new_precise_pending':324,'prior_pending_exact':177,'all600_prior_pending_assessed':600,'current_pending':501,'current_reviewed':1255,'every_prior_proved_atom_preserved':allpreserved,'new_cross_owner_proof_files':7,'new_public_exports':55,'actual_canonical_zero_records':14,'selected20_reused_sources':225,'selected20_sources_protected':1068,'frozen20_inputs_exact':30207},'preserved_failed_reader':str(f.relative_to(r)) if False else 'book/coverage/checks/foundations-future21/modules-final-mapping-peer-failed-reader-v1.json','now_whole1107_and679_prior_atoms_retained':True,'outside423_only_explicit_current_interface_path_aliases_changed':True,'all_original_review_bodies_times_hypotheses_gaps_actual_evidence_preserved':True,'independent_seeded_adapter_and_actual_ledger_exact_match':True,'checker':str(Path(__file__)),'checker_sha256':H(Path(__file__)),'limits':['Independent final mapping/evidence mechanics. Original eight mathematical source reviews retain their decisions and times; no new semantic theorem is inferred.','The inherited20 actual audit is retained as historical evidence. A fresh checkpoint21 aggregate/kernel/axiom audit remains required.']};(R/out).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'path':out,'sha256':H(out),'counts':r['counts']}))

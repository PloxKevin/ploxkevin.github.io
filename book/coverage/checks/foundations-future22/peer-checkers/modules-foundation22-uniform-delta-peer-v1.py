from pathlib import Path
import collections,datetime,hashlib,json,sys
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/foundations-future22'
sys.path.insert(0,str(R/'book/coverage'))
from lean_names import declarations
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
expected={
 'book/coverage/build_foundations22_v2.py':'e17e28825b04082f1915a0a3aceba7812041b201f2087da6c7b4503b9ece1ea5',
 'foundations-source48-candidate-ledger22-v1.json':'cba5b6308dc33346cb3e86dc7fc3c5e2f43773ec95b55d0c4a0b42bdd0cb4cbb',
 'foundations-source48-material22-interface-binding-v1.json':'7a0729299f3545ced42662c820681c01fc95a11ef3a9343955f937767bdde31c',
 'foundations-source48-candidate-ledger22-v2.json':'305229a7e1df78c23bc1af728c7f3f4e0ac09d13c55e4e687fe721160b43bf88',
 'foundations-source48-material22-interface-binding-v2.json':'be87a01382c6f4be09486d4c546b759efb68c0f0ba3bfae6b52d97a961d833b2',
 'foundations-source48-integration-offer22-draft-v2.json':'defa9e655ae484813647f075d36a993ea387852b911dac700dde10dd106066e2'}
for n,h in expected.items():assert sha(R/n if '/' in n else B/n)==h,n
old=read(B/'foundations-source48-candidate-ledger22-v1.json');new=read(B/'foundations-source48-candidate-ledger22-v2.json')
i1=read(B/'foundations-source48-material22-interface-binding-v1.json');i2=read(B/'foundations-source48-material22-interface-binding-v2.json')
offer=read(B/'foundations-source48-integration-offer22-draft-v2.json')
assert sha(R/'book/coverage/foundations-audit22-source48-additions-v1.json')=='bf8432b89badbd44e5f3998470f26af3f3bb07ee88fe68853ceb6184e5eb1662'
prior=read(B/'foundations-source48-candidate22-independent-modules-confirmation-v2.json')
assert sha(B/'foundations-source48-candidate22-independent-modules-confirmation-v2.json')=='55a295eaad07c32ee0c49ee197fc96011d1e365b766ad80216a59db7acf7ab4b'
assert prior['errors']==[]
assert i2['material_units'][:-1]==i1['material_units'] and i2['proof_packets'][:-1]==i1['proof_packets']
assert len(i2['material_units'])==17
row=i2['material_units'][-1];key=row['source_unit_key'];assert key=='primer-basics.html::node-1167'
peer=read(R/row['original_review']);assert sha(R/row['original_review'])==row['original_review_sha256']=='f926443ed435f3d07a06d20b40724806b3251ef7bfdb7e306ceec83c24fc4331'
assert peer['errors']==[] and peer['status']=='independent_complete_uniform_continuity_literal_review_passed'
assert row['original_reviewed_at_utc']==peer['reviewed_at_utc'] and row['original_unit_row']==peer['material_units'][0]
assert row['original_unit_row']['whole_unit_approved'] and row['original_unit_row']['missing_clauses']==[]
invpath=R/'book/coverage/inventory-after-correction48.json';assert sha(invpath)==sha(R/'book/coverage/inventory.json')=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
unit=next(r for r in read(invpath)['material_source_units'] if r['key']==key)
assert row['exact_current48_inventory_record']==row['original_unit_row']['entire_inventory_record']==unit
before=[c for c in old['material_claims'] if key in c['source_unit_keys']]
assert row['original_current21_claims']==before
removed=[c for c in before if c['status']=='pending'];assert len(removed)==1 and removed==row['removed_pending_clauses']
retained=[c for c in before if c['status']!='pending'];assert retained==row['retained_original_proved_or_nonformal_claims']
claim=row['new_candidate_claim'];original=row['original_unit_row']
assert claim['source_unit_keys']==[key] and claim['status']=='proved' and claim['remaining_gaps']==[]
for field in ['source','locator','source_text','source_sha256']:assert claim[field]==unit[field]
assert claim['source_text_sha256']==unit['text_sha256'] and claim['lean_declarations']==original['lean_declarations']
assert claim['hypotheses']==original['hypotheses'] and claim['correspondence']==original['per_unit_reason']
assert claim['source_review']['reviewed_at_utc']==peer['reviewed_at_utc']
assert new['material_claims']==[c for c in old['material_claims'] if c not in removed]+[claim]
assert all(c in new['material_claims'] for c in old['material_claims'] if c['status']!='pending')
assert new['exercises']==old['exercises'] and len(new['exercises'])==119
allowed={'proof_files','proof_sha256','counts','material_claims','limits','current22_material_mapping','original_current22_four_source_mapping_v1'}
assert {k:v for k,v in new.items() if k not in allowed}=={k:v for k,v in old.items() if k not in allowed}
assert new['limits'][:-1]==old['limits'] and new['original_current22_four_source_mapping_v1']==old['current22_material_mapping']
assert {k:v for k,v in new['counts'].items() if k!='material_claim_statuses'}=={k:v for k,v in old['counts'].items() if k!='material_claim_statuses'}
assert new['counts']['material_claim_statuses']==dict(collections.Counter(c['status'] for c in new['material_claims']))
source='verification/lean/SafeLearning/CompleteFoundationsUniformContinuity22.lean';digest='ca8ba22fe9cb9287de6cb9fc8e6f2edf797908be0deb7acd00aacc5586bef31a'
assert set(new['proof_files'])==set(old['proof_files'])|{source}
assert new['proof_sha256']==dict(old['proof_sha256'],**{source:digest}) and sha(R/source)==digest
names=[d['name'] for d in declarations((R/source).read_text()) if d['kind'] in {'theorem','lemma'}]
assert len(names)==9 and names==original['lean_declarations']
assert len(peer['actual_canonical_execution_records'])==2
for ref in peer['actual_canonical_execution_records']:
 rec=read(R/ref['file']);assert sha(R/ref['file'])==ref['sha256'] and rec==ref['record']
 assert rec['exit_code']==0 and rec['source_sha256_before']==rec['source_sha256_after']==digest
 assert sha(R/rec['log'])==rec['log_sha256'] and sha(R/rec['preserved_source'])==digest
 assert rec['command'] in [['lake','env','lean','SafeLearning/CompleteFoundationsUniformContinuity22.lean'],['lake','build','SafeLearning.CompleteFoundationsUniformContinuity22']]
assert len(offer['proof_files'])==5 and offer['new_theorem_or_lemma_count']==45 and not offer['coverage_complete']
for source2,data in offer['proof_files'].items():
 assert sha(R/source2)==data['sha256']
 for n,h in data['evidence_sha256'].items():assert sha(R/n)==h
assert i2['physical_after']=={'total':1756,'whole_proved':748,'nonformal':524,'whole_pending':484}
assert sha(R/offer['held21_ledger'])==offer['held21_ledger_sha256']
sel=read(R/offer['base_selection']);assert len(sel['proof_files'])==1089
for n,data in sel['proof_files'].items():assert sha(R/n)==data['sha256']
out=B/'foundations-source48-uniform22-delta-independent-modules-confirmation-v1.json'
report={'status':'independent_exact_one_unit_uniform_extension_and_prior_candidate_preservation_passed','reviewed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checker':str(Path(__file__)),'checker_sha256':sha(__file__),'candidate_ledger':offer['mapped_ledger'],'candidate_ledger_sha256':sha(R/offer['mapped_ledger']),'interface_binding':offer['material22_exact_interface_binding'],'interface_binding_sha256':sha(R/offer['material22_exact_interface_binding']),'draft_offer':'book/coverage/checks/foundations-future22/foundations-source48-integration-offer22-draft-v2.json','draft_offer_sha256':sha(B/'foundations-source48-integration-offer22-draft-v2.json'),'prior_full_candidate_peer':'book/coverage/checks/foundations-future22/foundations-source48-candidate22-independent-modules-confirmation-v2.json','prior_full_candidate_peer_sha256':sha(B/'foundations-source48-candidate22-independent-modules-confirmation-v2.json'),'original_uniform_review':row['original_review'],'original_uniform_review_sha256':row['original_review_sha256'],'original_uniform_review_time_preserved':peer['reviewed_at_utc'],'checks':{'119_exercises_and_all16_prior_complete_literal_rows_unchanged':True,'original1167_heine_cantor_proved_atom_retained':True,'exactly_one_own_pending_removed':True,'fresh_original_reason_hypotheses_declarations_time_exact':True,'nine_actual_new_exports_paired_exit0':True,'old_v1_candidate_interface_offer_and_all1089_sources_exact':True},'counts':{'new_complete_literal_units':1,'combined_complete_literal_units':17,'new_public_theorems':9,'combined_new_public_theorems':45,'combined_new_sources':5,'whole_pending_before_v1':485,'whole_pending_after_v2':484},'scope':'Narrow mechanical delta confirmation. The prior complete v1 peer and fresh whole node1167 semantic peer retain their original bodies/times. No live mapping or aggregate22 claim.','errors':[]}
with out.open('x') as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':report['status'],'report':str(out.relative_to(R)),'sha256':sha(out)}))

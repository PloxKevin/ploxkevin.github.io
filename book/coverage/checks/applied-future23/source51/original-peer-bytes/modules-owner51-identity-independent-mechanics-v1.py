from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, sys
R=Path('/home/oxrexkevin/SafetyBased')
H=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
P=lambda n: Path(n) if Path(n).is_absolute() else R/n
J=lambda n: json.loads(P(n).read_text())
ref=lambda n: {'file':str(n),'sha256':H(P(n))}
def checkref(r):
 assert H(P(r['file']))==r['sha256'],r['file']
 return J(r['file']) if P(r['file']).suffix=='.json' else None
owner=sys.argv[1]; assert owner in ('applied','foundations')
base=f'book/coverage/checks/{owner}-future23/source51'
offername=base+f'/{owner}-audit23-candidate-source51-additions-v1.json'
offer=J(offername)
assert H(P(offername))=={'applied':'b0be18b27d8c6dd50c5247a920371052fe66b52bcd7cef609bf7e2c4e3c1bc34','foundations':'ff9e6e06f1774ae31234022a9e1c126b891e33c50cf8d453d1e2c8a2bb5ab020'}[owner]
live={n:H(P('book/coverage/'+n+'.json')) for n in ('core','applied','foundations','modules')}
assert live=={'core':'3e7c69fb9a0978c914df20835bed3b2aee2b742702bb07caa6d9d582a16251f7','applied':'0ee60f1f224d01f443a762e0427d4527d6bd9b1d3ae5ed1d893c67750e331d20','foundations':'305229a7e1df78c23bc1af728c7f3f4e0ac09d13c55e4e687fe721160b43bf88','modules':'0ebe910d6d8d9a84338727988c5d415746c3f1f624d6958997bea89645d4b06c'}
invname='book/coverage/inventory-after-correction51.json'; inv=J(invname)
assert H(P(invname))==H(P('book/coverage/inventory.json'))=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
rootactual=J('reports/full-coverage/source51-apply-execution-v1.json'); rootpost=J('book/coverage/checks/root-source-batch51/postwrite-source-integrity-v1.json')
assert rootactual['actual_exit_code']==rootpost['actual_exit_code']==0
assert H(P(rootactual['log']))==rootactual['log_sha256'] and rootpost['inventory_after_sha256']==H(P(invname))
manifest=J('reports/full-coverage/checkpoint-22-manifest.json');assert len(manifest['proof_files'])==1113
for n,v in manifest['proof_files'].items(): assert H(P(n))==v['sha256'],n
frozenassets={n:v for n,v in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(frozenassets)==31
for n,v in frozenassets.items():assert H(R/'reports/full-coverage/checkpoint-22'/n)==v,n
candidate=J(offer['mapped_ledger']);assert H(P(offer['mapped_ledger']))==offer['mapped_ledger_sha256']
scope=set(candidate['scope_pages'])
for n,v in offer['source_sha256'].items():assert H(P(n))==v,n
inventories={i:J(f'book/coverage/inventory-after-correction{i}.json') for i in (48,49,50,51)}
ownedcounts={}
for kind in ('exercises','material_source_units'):
 records={i:{r['key']:r for r in x[kind] if r['source'] in scope} for i,x in inventories.items()}
 assert all(x==records[51] for x in records.values()),kind
 ownedcounts[kind]=len(records[51])
if owner=='applied':
 side=checkref(offer['identity_sidecar']);guard=checkref(offer['identity_integrity']); assert guard['errors']==[]
 old=J('book/coverage/applied.json');oldp=J('book/coverage/applied-promotions.json');prom=J(offer['mapped_promotions']);assert H(P(offer['mapped_promotions']))==offer['mapped_promotions_sha256']
 reverse=copy.deepcopy(candidate);reversep=copy.deepcopy(prom);identity=reverse.pop('current51_owner_identity');identityp=reversep.pop('current51_owner_identity');assert identity==identityp
 assert reverse==old and reversep==oldp
 assert identity['inventory']==invname and identity['inventory_sha256']==H(P(invname))
 for k in ('historical_inventory','current_inventory','intermediate_inventory49','intermediate_inventory50'):checkref(side[k])
 for kind in ('exercises','material_source_units'):
  assert {r['key']:r for r in side['entire_owned_inventory_records'][kind]}=={r['key']:r for r in inv[kind] if r['source'] in scope}
 for row in offer['baseline22_unpruned_working_history']:
  checkref(row['original']);checkref(row['byte_exact_copy']);assert P(row['original']['file']).read_bytes()==P(row['byte_exact_copy']['file']).read_bytes()
 for n,v in offer['required_evidence_artifacts_sha256'].items():assert H(P(n))==v,n
 extras={n:v for n,v in old['proof_files'].items() if n not in manifest['proof_files']}
 assert extras==side['unreferenced_unselected_metadata_preserved_exactly'] and len(extras)==3
 for n,v in old['proof_files'].items():assert H(P(n))==v,n
 assert len(candidate['exercises'])==128 and sum(len(x['claims']) for x in candidate['exercises'])==468 and len(candidate['material_claims'])==1954 and len(candidate['proof_files'])==298
 assert ownedcounts=={'exercises':128,'material_source_units':2059}
 assert offer['proof_files']=={} and offer['new_actual_paired_records']==[] and offer['new_material_keys']==[]
 actualname=base+'/applied23-source51-identity-preparation-actual-execution-v1.json';actual=J(actualname)
 helper=offer['candidate_builder'];assert H(P(helper))==offer['candidate_builder_sha256']==actual['actual_checker_sha256_before']==actual['actual_checker_sha256_after']
 assert actual['actual_command']==['python',str(P(helper)),H(P(invname))] and actual['actual_workdir']==str(R) and actual['actual_exit_code']==0
 assert H(P(actual['log']))==actual['log_sha256']
 proofcount=298; newproofs=0; reversals='Entire unpruned working22 ledger and promotions recovered by removing only current51_owner_identity; all three unreferenced/unselected metadata entries preserved.'
else:
 oldname='book/coverage/checks/foundations-future23/source50/foundations23-candidate-source50-v1.json';old=J(oldname);assert H(P(oldname))=='ab48adca29ae6bc13fe87466700e07cb0b6112a2668ad494b98a6a4a34a93c79'
 oldoffername='book/coverage/checks/foundations-future23/source50/foundations-audit23-candidate-source50-additions-v2-reviewed.json';oldoffer=J(oldoffername)
 interface=J(offer['material23_exact_interface_binding']);assert H(P(offer['material23_exact_interface_binding']))==offer['material23_exact_interface_binding_sha256']
 oldinterface=checkref(interface['original_source50_interface']);oldpeer=checkref(interface['original_source50_independent_mapping_peer'])
 assert interface['entire_original_source50_interface_body_and_times']==oldinterface and interface['entire_original_independent_peer_body_and_time']==oldpeer
 reverse=copy.deepcopy(candidate)
 assert reverse['current23_owner_identity']['original_source50_owner_identity_exact']==old['current23_owner_identity']
 for k in ('current23_owner_identity','current23_material_mapping'):reverse[k]=copy.deepcopy(old[k])
 assert reverse==old
 assert candidate['current23_owner_identity']['inventory']==ref(invname)
 assert candidate['current23_material_mapping']==dict(old['current23_material_mapping'],interface_binding=offer['material23_exact_interface_binding'])
 assert ownedcounts=={'exercises':119,'material_source_units':1756}
 assert offer['proof_files']==oldoffer['proof_files'] and len(offer['proof_files'])==3 and offer['new_theorem_or_lemma_count']==39
 assert offer['exact_source_reviews_sha256']==oldoffer['exact_source_reviews_sha256'] and offer['canonical_source_binding_reviews_with_original_bodies_and_times']==oldoffer['canonical_source_binding_reviews_with_original_bodies_and_times']
 for rows in ('exact_source_reviews_sha256','actual_canonical_execution_records_sha256','canonical_source_peer_bindings_sha256'):
  for n,v in offer[rows].items():assert H(P(n))==v,n
 for n,v in offer['proof_files'].items():
  assert H(P(n))==v['sha256']
  for e,d in v['evidence_sha256'].items():assert H(P(e))==d,e
 history=checkref(offer['source50_to51_original_candidate_peer_history'])
 for row in history['archives']:
  checkref(row['original']);checkref(row['canonical_alias']);assert P(row['original']['file']).read_bytes()==P(row['canonical_alias']['file']).read_bytes()
 actualname=offer['actual_builder_record'];actual=J(actualname);assert H(P(actualname))==offer['actual_builder_record_sha256']
 helper=offer['current_owner_builder'];assert H(P(helper))==offer['current_owner_builder_sha256']==actual['helper_sha256_before']==actual['helper_sha256_after']
 assert actual['command']==['python3',str(P(helper))] and actual['cwd']==str(R) and actual['actual_exit_code']==0
 assert H(P(actual['raw_log']))==actual['raw_log_sha256']==offer['actual_builder_raw_log']['sha256']
 proofcount=len(candidate['proof_files']);newproofs=3;reversals='Entire independently reviewed source50 candidate recovered by restoring only two identity/interface metadata fields; all14 decisions/39 exports and whole original interfaces/review times preserved.'
for n,v in live.items():assert H(P('book/coverage/'+n+'.json'))==v
out={'status':'independent_exact_inventory_identity_rebase_confirmation_passed','reviewer':'/root/modules_resume','checked_at_utc':datetime.now(timezone.utc).isoformat(),'errors':[], 'candidate_offer':ref(offername),'candidate_ledger':ref(offer['mapped_ledger']),'actual_isolated_identity_builder':ref(actualname),'actual_identity_helper':ref(helper),'current_inventory':ref(invname),'exact_owned_full_inventory_record_counts':ownedcounts,'entire_inverse_and_original_semantics_preserved':True,'inverse_scope':reversals,'preserved_proof_rows':proofcount,'new_selected_proof_sources':newproofs,'all1113_selected22_source_hashes_exact':True,'all31_original_frozen22_assets_exact':True,'held22_live_owner_ledgers_sha256':live,'checker':ref(Path(__file__)),'scope':'Fresh read-only isolated candidate mechanics only. Original semantic decisions, hypotheses, declarations, reasons, times and compiler evidence remain exact. No live ledger installation, new mathematical review, Lean compile, global23 or aggregate23 claim.'}
target=Path(f'/tmp/{owner}23-source51-identity-independent-modules-confirmation-v1.json');assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':ref(target),'status':out['status']}))

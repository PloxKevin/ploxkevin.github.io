from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy
ROOT=Path('/home/oxrexkevin/SafetyBased');D='book/coverage/checks/future26-core/box-labels/';OUT=Path('/tmp/core26-labels-isolated-candidate-independent-applied-confirmation-v1.json');assert not OUT.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();R=lambda n:json.loads((ROOT/n).read_text())
cn=D+'core26-source52-labels-candidate-v1.json';bn='book/coverage/checks/future25-core/core25-source52-material-candidate-v1.json';pn=D+'original-tmp/root-core26-box-label-118-independent-applied-full-context-review-v1.json';catalogname=D+'closed-original-byte-aliases-v1.json'
c=R(cn);b=R(bn);peer=R(pn);catalog=R(catalogname);assert H(ROOT/pn)=='c1d15307054f027da5f5ff25b7bec6d9703360e629947c452888d1cc20ded167' and H(ROOT/bn)=='4e96c717055187cfc24e9e60a19a7d183499336570d99fbf9954ff199ff49572'
assert peer['errors']==[] and peer['whole_nonformal_labels_approved']==48 and peer['substantive_titles_retained_pending']==70
for row in catalog['original_absolute_path_byte_aliases']:
 assert H(ROOT/row['canonical_file'])==row['sha256']
 if Path(row['original_absolute_path']).exists():assert H(row['original_absolute_path'])==row['sha256']
inv=R('book/coverage/inventory.json');assert H(ROOT/'book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3';units={r['key']:r for r in inv['material_source_units']};appr={r['source_unit_key']:r for r in peer['material_units'] if r['whole_unit_approved']};pending={r['source_unit_key']:r for r in peer['material_units'] if not r['whole_unit_approved']}
assert len(appr)==48 and len(pending)==70
changes=[];restored=copy.deepcopy(c)
for n,(old,row) in enumerate(zip(b['material_claims'],c['material_claims'])):
 key=row['source_unit_keys'][0] if len(row['source_unit_keys'])==1 else None
 if key in appr:
  u=appr[key];assert u['entire_inventory_record']==units[key] and u['entire_original_pending_claim_body_and_time']==old
  assert row['kind']=='independently_reviewed_literal_material_unit' and row['status']=='not_a_formal_claim'
  assert row['lean_declarations']==u['lean_declarations']==[] and row['hypotheses']==u['hypotheses']==[] and row['remaining_gaps']==u['missing_clauses']==[]
  assert row['correspondence']==u['per_unit_reason'] and row['original_complete_literal_review_record']==u and row['original_source52_entire_pending_material_row']==old
  assert row['independent_review']=={'source':pn,'sha256':H(ROOT/pn),'original_review_time':peer['reviewed_at_utc']}
  changes.append(key);restored['material_claims'][n]=copy.deepcopy(old)
 else:assert row==old
assert set(changes)==set(appr)
for key,u in pending.items():assert u['entire_inventory_record']==units[key] and u['material_status']=='pending' and u['missing_clauses']
restored['generated_at_utc']=b['generated_at_utc'];binding=restored.pop('future26_label_material_candidate_binding');assert restored==b
assert len(c['exercises'])==92 and len(c['proof_files'])==177 and c['proof_files']==b['proof_files']
for name,key in [('prior_isolated_owner25_candidate','prior_isolated_owner25_candidate'),('original_full118_label_peer','original_full118_label_peer'),('closed_original_byte_aliases','closed_original_byte_aliases'),('current_inventory','current_inventory')]:
 ref=binding[key];assert H(ROOT/ref['file'])==ref['sha256']
integrity=R(D+'core26-source52-labels-candidate-integrity-v1.json');assert integrity['errors']==[] and integrity['candidate']=={'file':cn,'sha256':H(ROOT/cn)} and set(integrity['whole_nonformal_units'])==set(changes)
actualname='reports/full-coverage/root-core26-labels-isolated-candidate-execution-v1.json';actual=R(actualname);assert actual.get('actual_exit_code',actual.get('exit_code'))==0
assert actual.get('command',actual.get('actual_command'))
# Genuine Root candidate construction is provenance, not another compiler execution.
manifest=R('reports/full-coverage/checkpoint-24-manifest.json');assert len(manifest['proof_files'])==1144 and len(manifest['frozen_inputs_sha256'])==40485
for name,row in manifest['proof_files'].items():assert H(ROOT/name)==row['sha256']
for name,h in manifest['frozen_inputs_sha256'].items():assert H(ROOT/manifest['snapshot']/name)==h
held={name:H(ROOT/name) for name in ['book/coverage/'+x+'.json' for x in ['core','foundations','applied','modules','applied-promotions']]+list(inv['source_sha256'])}
for name,h in held.items():assert H(ROOT/name)==h
report={'status':'passed_independent_isolated_core26_label_candidate_mechanics','errors':[],'reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':{'file':cn,'sha256':H(ROOT/cn)},'base_isolated_core25_candidate':{'file':bn,'sha256':H(ROOT/bn)},'original_semantic_peer':{'file':pn,'sha256':H(ROOT/pn),'entire_original_body':peer,'original_review_time':peer['reviewed_at_utc']},'exact_changes':{'whole_nonformal_labels':48,'keys':sorted(changes),'substantive_label_assertions_retained_pending':70,'new_proof_sources':0,'new_theorems':0},'entire_inverse_to_held_isolated25_candidate':True,'all92_exercises_and177_old_proof_rows_exact':True,'all_other_material_rows_exact':True,'actual_isolated_candidate_preparation':{'file':actualname,'sha256':H(ROOT/actualname),'entire_native_record':actual},'original_closed_byte_alias_catalog':{'file':catalogname,'sha256':H(ROOT/catalogname)},'checked_protection':{'1144_selected_sources_exact':True,'40485_frozen24_inputs_exact':True,'live_owners_and_current31_asset_hashes':held},'scope':'Mechanical candidate/alias/current-literal check only. Original118 semantic decisions/times unchanged. No live installation, compiler, aggregate or parent/exercise promotion.'}
OUT.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':'passed','report':str(OUT),'sha256':H(OUT),'changed_NF':48,'new_theorems':0}))

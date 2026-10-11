"""Unique isolated future24 candidate: exact six whole literals and original times."""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import hashlib,json,re,copy
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'book/coverage/checks/foundations-future24/source51'
PACK=ROOT/'book/coverage/checks/foundations-future24/material-batch1/five-source37-export-actual-canonical-readiness24-v1.json'
PACK_SHA='758e81e120ab257f9b87fe0c6602ce92bfab26d3f90ca6d4a726937ca293164d'
OLD=ROOT/'book/coverage/foundations.json';OLD_SHA='6008c0225111ce8a8db195475036d85af95567f620e57929ea485d39e9d42279'
INV=ROOT/'book/coverage/inventory-after-correction51.json';INV_SHA='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
SELECTION=ROOT/'reports/full-coverage/checkpoint-23-selection.json'
AUDIT=ROOT/'reports/full-coverage/lean-checkpoint-23/verification-original.json'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def R(p):return json.loads(p.read_text())
def rel(p):return p.relative_to(ROOT).as_posix()
def ref(p):return {'file':rel(p),'sha256':H(p)}
def bind(r):
 p=ROOT/r['file'];assert H(p)==r['sha256'],r['file'];return p
def write(p,d):
 with p.open('x')as f:f.write(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def physical(d):
 by={}
 for r in d['material_claims']:
  for k in r['source_unit_keys']:by.setdefault(k,set()).add(r['status'])
 c=Counter('pending'if'pending'in v else'not_a_formal_claim'if v=={'not_a_formal_claim'}else'proved'for v in by.values())
 return {'total':len(by),'whole_proved':c['proved'],'nonformal':c['not_a_formal_claim'],'whole_pending':c['pending']}
assert H(OLD)==OLD_SHA and H(INV)==INV_SHA==H(ROOT/'book/coverage/inventory.json') and H(PACK)==PACK_SHA
old=R(OLD);inv=R(INV);inv48=R(ROOT/'book/coverage/inventory-after-correction48.json')
selection=R(SELECTION);manifest=R(ROOT/'reports/full-coverage/checkpoint-23-manifest.json');audit=R(AUDIT)
assert len(selection['proof_files'])==1131 and audit['status']=='passed'and audit['proof_file_count']==1131 and audit['theorem_count']==9193
assert manifest['selection_sha256']==H(SELECTION)and manifest['status']=='formal_verification_passed_partial_coverage'
protected={n:r['sha256']for n,r in selection['proof_files'].items()}
assets={n:h for n,h in manifest['working_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31
protected.update(assets);protected.update(old['source_sha256'])
owners={f'book/coverage/{n}.json':H(ROOT/f'book/coverage/{n}.json')for n in ['core','foundations','applied','modules','applied-promotions']}
protected.update(owners);protected.update({rel(INV):INV_SHA,'book/coverage/inventory.json':INV_SHA,rel(SELECTION):H(SELECTION)})
def guard():
 for n,h in protected.items():assert H(ROOT/n)==h,n
 for n,r in selection['proof_files'].items():assert H(ROOT/'reports/full-coverage/checkpoint-23'/n)==r['sha256'],n
 for n,h in assets.items():assert H(ROOT/'reports/full-coverage/checkpoint-23'/n)==h,n
guard();BASE.mkdir(parents=True,exist_ok=True)
CAND=BASE/'foundations24-candidate-source51-v1.json';INTERFACE=BASE/'foundations24-six-complete-literal-interface-source51-v1.json';DRAFT=BASE/'foundations-audit24-candidate-source51-additions-draft-v1.json';INTEGRITY=BASE/'candidate-original23-preservation-source51-v1.json';HELD=BASE/'held-foundations23-original-source51-v1.json'
assert not any(p.exists()for p in [CAND,INTERFACE,DRAFT,INTEGRITY,HELD])
with HELD.open('xb')as f:f.write(OLD.read_bytes())
foundation_units=[u for u in inv['material_source_units']if u['source']in old['scope_pages']]
foundation_ex=[e for e in inv['exercises']if e['source']in old['scope_pages']]
units48={u['key']:u for u in inv48['material_source_units']};ex48={e['key']:e for e in inv48['exercises']}
assert len(foundation_units)==1756 and len(foundation_ex)==119
assert all(u==units48[u['key']]for u in foundation_units)and all(e==ex48[e['key']]for e in foundation_ex)
units={u['key']:u for u in foundation_units};candidate=copy.deepcopy(old)
decl_files={r['name']:r['file']for r in audit['declarations']};assert len(decl_files)==9193
pack=R(PACK);assert pack['source_count']==5 and pack['public_theorem_count']==37 and pack['whole_mathematical_unit_count']==6
newproofs={};newnames=set();readyrefs={};semanticrefs={};actualrefs={};packets=[];mappings=[];removedids=set();mappedkeys=set();covered=set();referenced_selected_sources={}
for gr in pack['groups']:
 gp=bind(gr);g=R(gp);readyrefs[rel(gp)]=H(gp);src=bind(g['canonical_source']);text=src.read_text()
 assert rel(src)not in selection['proof_files']and rel(src)not in old['proof_files']
 module=src.stem;names=['SafeLearning.'+module+'.'+n for n in re.findall(r'^theorem\s+(\w+)',text,re.M)]
 assert names==g['public_theorem_names']and len(names)==g['public_theorem_count']
 assert not re.search(r'\b(sorry|admit|axiom)\b',text)
 assert not newnames.intersection(names);newnames.update(names)
 for n in names:decl_files[n]=rel(src)
 peerp=bind(g['original_full_semantic_peer']);peer=R(peerp);assert peer==g['entire_original_full_semantic_peer_body_and_time']
 assert 'passed'in peer['status']and peer.get('errors',[])==[]
 semanticrefs[rel(peerp)]=H(peerp)
 for original,c in g['all_original_TMP_byte_copies'].items():
  cp=bind(c);assert Path(original).read_bytes()==cp.read_bytes(),original
 evidence={};pairs=[]
 for pr in g['actual_canonical_pair']:
  rp=bind(pr['actual_record']);r=R(rp);log=bind(pr['raw_log']);snapshot=bind(pr['source_snapshot'])
  exits=[r[k]for k in ['actual_exit_code','exit_code']if k in r];assert exits and all(x==0 for x in exits)
  assert r['actual_workdir']==str(ROOT/'verification/lean')and r['source']==rel(src)
  assert r['actual_command']in [['lake','build','SafeLearning.'+module],['lake','env','lean','SafeLearning/'+module+'.lean']]
  assert r['source_sha256_before']==r['source_sha256_after']==H(src)==H(snapshot)
  assert r['log_sha256']==H(log)and r['log']==rel(log)and r['source_snapshot']==rel(snapshot)
  assert r['started_at_utc']<r['finished_at_utc']and r['elapsed_seconds']>0
  helper=ROOT/r['actual_pair_helper'];assert H(helper)==r['actual_pair_helper_sha256']and ref(helper)==g['actual_helper']
  evidence.update({rel(rp):H(rp),rel(log):H(log),rel(snapshot):H(snapshot)})
  actualrefs[rel(rp)]=H(rp);pairs.append({'reference':ref(rp),'entire_original_actual_record_and_time':r,'raw_log':ref(log),'source_snapshot':ref(snapshot)})
 assert len(pairs)==2 and {r['entire_original_actual_record_and_time']['actual_command'][1]for r in pairs}=={'build','env'}
 newproofs[rel(src)]={'sha256':H(src),'evidence_sha256':evidence,'evidence_scope':'Genuine exact-source canonical standalone and named target EXIT0 with actual raw logs/source snapshot. Original whole semantic decisions/time unchanged; future24 aggregate/selection separate.'}
 packets.append({'group':g['group'],'canonical_source':ref(src),'public_theorem_names':names,'original_semantic_review':ref(peerp),'entire_original_semantic_body_and_time':peer,'canonical_readiness':ref(gp),'actual_pair':pairs,'all_original_TMP_byte_copies':g['all_original_TMP_byte_copies']})
 candidate['proof_files'].append(rel(src));candidate['proof_sha256'][rel(src)]=H(src)
 for row in peer['material_units']:
  key=row.get('source_unit_key',row.get('key'));unit=units[key]
  originalunit=row.get('entire_inventory_record',row.get('entire_original_inventory_record'))
  assert originalunit==unit==units48[key]and key not in mappedkeys;mappedkeys.add(key)
  if g['group']=='audit1163':assert row['review_status']=='approved_complete_source_unit'and row['missing']==[]
  else:assert row['whole_unit_approved']is True and row['missing_clauses']==[]
  reason=row.get('per_unit_reason',row.get('reason'));assert isinstance(reason,str)and reason
  hypotheses=row['hypotheses'];declarations=row['lean_declarations'];assert declarations
  for n in declarations:
   assert n in decl_files,n
   p=ROOT/decl_files[n];assert H(p)==newproofs[rel(p)]['sha256']if rel(p)in newproofs else H(p)==selection['proof_files'][rel(p)]['sha256']
   if rel(p)in selection['proof_files']:
    referenced_selected_sources[rel(p)]=selection['proof_files'][rel(p)]['sha256']
    if rel(p)not in candidate['proof_files']:candidate['proof_files'].append(rel(p));candidate['proof_sha256'][rel(p)]=H(p)
  covered.update(set(declarations)&newnames)
  original=[r for r in old['material_claims']if key in r['source_unit_keys']];pending=[r for r in original if r['status']=='pending']
  assert len(pending)==1 and pending[0]['source_unit_keys']==[key]
  removedids.add(pending[0]['id'])
  new={'id':key+'::independently-reviewed24-whole-literal','source_unit_keys':[key],'source':unit['source'],'locator':unit['locator'],'source_text':unit['source_text'],'source_text_sha256':unit['text_sha256'],'source_sha256':unit['source_sha256'],'statement_in_prose':unit['source_text'],'kind':'independently_reviewed_complete_mathematical_literal','status':'proved','lean_declarations':declarations,'hypotheses':hypotheses,'correspondence':reason,'remaining_gaps':[],'source_review':{'file':rel(peerp),'sha256':H(peerp),'reviewed_at_utc':peer['reviewed_at_utc'],'reviewer':peer.get('reviewer'),'reviewer_scope':'Exact author-independent original peer, entire original body/time preserved in interface.'}}
  candidate['material_claims']=[r for r in candidate['material_claims']if r['id']!=pending[0]['id']];candidate['material_claims'].append(new)
  mappings.append({'source_unit_key':key,'entire_current51_inventory_record':unit,'entire_original_whole_literal_peer_row':row,'original_semantic_review':ref(peerp),'original_reviewed_at_utc':peer['reviewed_at_utc'],'entire_original_pending_clauses':pending,'retained_original_nonpending_clauses':[r for r in original if r['status']!='pending'],'new_candidate_claim':new})
assert len(mappedkeys)==6 and len(removedids)==6 and len(newnames)==37 and len(newproofs)==5 and covered==newnames
candidate['proof_files']=sorted(set(candidate['proof_files']));candidate['counts']['material_claim_statuses']=dict(Counter(r['status']for r in candidate['material_claims']))
assert candidate['exercises']==old['exercises']and candidate['surrounding_prose_reviews']==old['surrounding_prose_reviews']and candidate['source_sha256']==old['source_sha256']
newids={r['new_candidate_claim']['id']for r in mappings}
assert [r for r in old['material_claims']if r['id']not in removedids]==[r for r in candidate['material_claims']if r['id']not in newids]
assert sum(r['status']=='proved'for r in old['material_claims'])==1094
assert physical(old)=={'total':1756,'whole_proved':762,'nonformal':524,'whole_pending':470}
assert physical(candidate)=={'total':1756,'whole_proved':768,'nonformal':524,'whole_pending':464}
candidate['current24_owner_identity']={'inventory':ref(INV),'original23_ledger':ref(HELD),'original23_selection':ref(SELECTION),'actual_passed23_aggregate':ref(AUDIT),'unchanged_entire_foundation_source_records':1756,'unchanged_entire_foundation_exercise_records':119,'scope':'Isolated future24 identity51 only. Actual frozen23/live-owner ledgers, source HTML and all earlier full semantic bodies/times stay exact.'}
candidate['current24_material_mapping']={'interface_binding':rel(INTERFACE),'whole_material_units':6,'removed_prior_pending_claims':6,'new_public_exports':37,'new_proof_sources':5,'already_selected_referenced_declaration_sources':referenced_selected_sources,'physical_before':physical(old),'physical_after':physical(candidate),'scope':'Exact original whole-unit decisions normalized from their recorded schemas, with full original rows retained; no semantic replacement or current23 amendment.'}
candidate['limits'].append('Future24 isolated source51 candidate adds6 independently approved complete Foundation material units using5 genuine canonical paired sources/37 exports. All119 complete exercises and1094 earlier proved atoms/semantic bodies/times stay exact. Remaining464 physical units still require mathematical work; no blanket guarantee classification or aggregate24 claim.')
write(CAND,candidate);guard()
interface={'status':'exact_original_six_complete_semantic_decisions_and_times_bound_to_isolated_candidate24','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_ledger':ref(CAND),'held_original23_ledger':ref(HELD),'current_inventory':ref(INV),'material_units':mappings,'proof_packets':packets,'referenced_existing_selected23_proof_sources':referenced_selected_sources,'all1756_units_and119_exercises_equal_source48_to51':True,'all_original1094_proved_atoms_and_prior_semantic_bodies_times_exact':True,'physical_before':physical(old),'physical_after':physical(candidate),'coverage_complete':False}
write(INTERFACE,interface)
draft={'schema_version':1,'status':'isolated_actual_paired_five_source37_export_six_whole_literal_candidate24_pending_independent_mapping_and_canonical_binding_peers','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'base_selection':rel(SELECTION),'base_selection_sha256':H(SELECTION),'actual_passing_baseline_audit':rel(AUDIT),'actual_passing_baseline_audit_sha256':H(AUDIT),'proof_files':newproofs,'new_proof_sources_for_checkpoint24':sorted(newproofs),'new_proof_file_count':5,'new_theorem_or_lemma_count':37,'mapped_ledger':rel(CAND),'mapped_ledger_sha256':H(CAND),'held23_ledger':rel(HELD),'held23_ledger_sha256':H(HELD),'working23_ledger':'book/coverage/foundations.json','working23_ledger_sha256':OLD_SHA,'source_sha256':candidate['source_sha256'],'current_inventory':rel(INV),'current_inventory_sha256':INV_SHA,'current_owner_builder':rel(Path(__file__)),'current_owner_builder_sha256':H(Path(__file__)),'exact_source_reviews_sha256':semanticrefs,'actual_canonical_execution_records_sha256':actualrefs,'canonical_readiness_sha256':readyrefs,'material24_exact_interface_binding':rel(INTERFACE),'material24_exact_interface_binding_sha256':H(INTERFACE),'new_material_dispositions':{'exact_current_rows':6,'whole_proved':6,'nonformal':0,'whole_pending':0,'previous_pending_claims_removed':6},'exercise_counts':candidate['counts']['exercise_statuses'],'material_counts':physical(candidate),'original_semantic_reviews_body_and_time_retained':True,'independent_final_candidate_mapping_peer_pending':True,'independent_canonical_binding_peer_pending':True,'actual_builder_record_pending':True,'coverage_complete':False,'scope':'Isolated Foundation24 candidate only; exact6 whole literals/5 actual paired source files/37 exports. All119 exercises/1094 prior proved atoms preserved, with genuine selected declaration dependencies. No live23 owner change, aggregate24/selection/publication claimed.'}
write(DRAFT,draft);guard()
integrity={'status':'passed_isolated_candidate_preserves_all_prior23_rows_and_frozen_sources','checked_at_utc':datetime.now(timezone.utc).isoformat(),'held23_ledger':ref(HELD),'candidate':ref(CAND),'interface':ref(INTERFACE),'draft_offer':ref(DRAFT),'all1131_selected23_sources_and_frozen_snapshots_exact':True,'all31_current51_assets_and_frozen_snapshots_exact':True,'five_live23_owner_files_and_inventory_exact':owners,'all119_exercise_bodies_and1094_prior_proved_atoms_exact':True,'all1756_entire_foundation_source_records_equal48_to51':True,'removed_pending_claim_ids':sorted(removedids),'referenced_existing_selected_proof_sources':referenced_selected_sources,'coverage_complete':False}
write(INTEGRITY,integrity);guard()
print(json.dumps({'candidate':ref(CAND),'interface':ref(INTERFACE),'draft_offer':ref(DRAFT),'integrity':ref(INTEGRITY),'new_sources':5,'new_exports':37,'whole_units':6,'physical_after':physical(candidate)}))

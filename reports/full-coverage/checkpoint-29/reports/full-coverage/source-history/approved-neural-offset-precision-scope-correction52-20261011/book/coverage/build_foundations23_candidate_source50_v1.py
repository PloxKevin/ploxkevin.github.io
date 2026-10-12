"""Isolated candidate only: exact reviewed Foundation literals, original times preserved."""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import copy,hashlib,json,re
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'book/coverage/checks/foundations-future23/source50'
INV=ROOT/'book/coverage/inventory-after-correction50.json';INV_SHA='dec8a34d0313fbc19846489f4d8c2f6e51734a135df6145829993fae0f80d91c'
OLD=ROOT/'book/coverage/foundations.json';OLD_SHA='305229a7e1df78c23bc1af728c7f3f4e0ac09d13c55e4e687fe721160b43bf88'
PLAN=[
 ('finite-prefix','foundations-finite-prefix1075-independent-modules-source-review23-v1.json','8aea2c9e73b21db45df6666cf303ad3e3b598e7400249e75d9d06615b2f68f01','CompleteFoundationsFinitePrefix23','f10296c36c25f094374c32423ba6d837f6bd364e397a89c7a586192d1d0bf7ef',6,'basics1075-full-literal-source-review-request-v1.json','382243b1174349103176dcee865221eac1941c6f259ace27a5650c50fa066d67','original-module-peer'),
 ('semicontinuity','foundations-semicontinuity-two-literals-independent-modules-source-review23-v1.json','1d79324bc7375ff026b06e64c67931945aecff3a39b4c29d79dd21e4a74a0ac5','CompleteFoundationsSemicontinuity23','280be25369c9cc9b3336d87ada8e5cf4d899cd454da1a4cabcf33725cb612b14',10,'basics1202-1237-canonical-paired-source-readiness-v1.json','e6285f7e4651589345bec4829bdadd7c06bd14c26d74a14669b7945470464fad','original-module-peer'),
 ('linalg-refresher','foundations-linalg-refresher-eleven-literals-independent-modules-source-review23-v1.json','be9f21c01be811f7b8137e0ea6d6638f9f11ad5a6c5e3f489dd6189393939f5f','CompleteFoundationsLinalgRefresher23','1918ab182f7fe20385966020197f3195abca4d61068ebeb1f21bfc9bd2061f0e',23,'eleven-literals-canonical-paired-source50-readiness-v1.json','d6d542b7c03a780a65c8882b588fabd68c5bab7842ecf289d4548f783e7ed25f','original-tmp')]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def rel(p):return p.relative_to(ROOT).as_posix()
def ref(p):return {'file':rel(p),'sha256':sha(p)}
def write_new(p,d):
 with p.open('x') as f:f.write(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def physical(d):
 bykey={}
 for row in d['material_claims']:
  for key in row['source_unit_keys']:bykey.setdefault(key,set()).add(row['status'])
 counts=Counter('pending' if 'pending' in v else 'not_a_formal_claim' if v=={'not_a_formal_claim'} else 'proved' for v in bykey.values())
 return {'total':len(bykey),'whole_proved':counts['proved'],'nonformal':counts['not_a_formal_claim'],'whole_pending':counts['pending']}
assert sha(INV)==INV_SHA==sha(ROOT/'book/coverage/inventory.json') and sha(OLD)==OLD_SHA
old=read(OLD);inv=read(INV);oldinv=read(ROOT/'book/coverage/inventory-after-correction48.json')
manifestpath=ROOT/'reports/full-coverage/checkpoint-22-manifest.json';manifest=read(manifestpath)
protected={n:r['sha256'] for n,r in manifest['proof_files'].items()};assert len(protected)==1113
assets={n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
protected.update(assets);protected.update({n:h for n,h in manifest['working_inputs_sha256'].items() if n in {'book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/core.json'}})
protected.update({'SafeLearning/cmdp.html':'5a503475452eacbeb8d5b8f4b3dd846bc3d88ff6817bd900a3cf3b2e2b23f6e9','SafeLearning/lyapunov-mpc.html':'228e4e22eaa32ad287069001abe9507706ec0112ec2ed9e1d3cfb2d569c4be7c','book/coverage/inventory.json':INV_SHA,'book/coverage/inventory-after-correction50.json':INV_SHA})
protected.update(old['source_sha256'])
def guard():
 for n,h in protected.items():assert sha(ROOT/n)==h,n
 for n,h in assets.items():assert sha(ROOT/'reports/full-coverage/checkpoint-22'/n)==h,n
guard();BASE.mkdir(parents=True,exist_ok=True)
CANDIDATE=BASE/'foundations23-candidate-source50-v1.json';BINDING=BASE/'foundations23-complete-literal-interface-source50-v1.json';DRAFT=BASE/'foundations-audit23-candidate-source50-additions-draft-v1.json';INTEGRITY=BASE/'candidate-original22-preservation-source50-v1.json'
assert not any(p.exists() for p in [CANDIDATE,BINDING,DRAFT,INTEGRITY])
snapshot=BASE/'held-foundations22-original-source48-v1.json'
if snapshot.exists():assert snapshot.read_bytes()==OLD.read_bytes()
else:
 with snapshot.open('xb') as f:f.write(OLD.read_bytes())
units={r['key']:r for r in inv['material_source_units']};oldunits={r['key']:r for r in oldinv['material_source_units']}
foundation_units=[r for r in inv['material_source_units'] if r['source'] in old['scope_pages']]
assert len(foundation_units)==1756 and all(r==oldunits[r['key']] for r in foundation_units)
oldex={r['key']:r for r in oldinv['exercises']};foundation_ex=[r for r in inv['exercises'] if r['source'] in old['scope_pages']]
assert len(foundation_ex)==119 and all(r==oldex[r['key']] for r in foundation_ex)
candidate=copy.deepcopy(old);mapping=[];packets=[];newproofs={};removedids=[];mappedkeys=set();covered=set();allpublic=set();semanticrefs={};actualrefs={};readinessrefs={}
for folder,peername,peersha,module,digest,count,readinessname,readinesssha,peersubdir in PLAN:
 base=ROOT/'book/coverage/checks/foundations-future23'/folder;peerpath=base/peersubdir/peername;assert sha(peerpath)==peersha;peer=read(peerpath)
 assert 'passed' in peer['status'] and peer['errors']==[];semanticrefs[rel(peerpath)]=peersha
 source=ROOT/'verification/lean/SafeLearning'/f'{module}.lean';assert sha(source)==digest and rel(source) not in old['proof_files'] and rel(source) not in manifest['proof_files']
 text=source.read_text();names=[f'SafeLearning.{module}.'+n for n in re.findall(r'^theorem\s+(\w+)',text,re.M)];assert len(names)==count;allpublic.update(names)
 ready=base/readinessname;assert sha(ready)==readinesssha;q=read(ready);readinessrefs[rel(ready)]=readinesssha
 evidence={};actualpair=[]
 if folder=='finite-prefix':
  pairpaths=[base/f'{module}-standalone-v1.json',base/f'{module}-named-build-v1.json']
 else:pairpaths=[ROOT/r['file'] for r in q['actual_canonical_pair']]
 for index,p in enumerate(pairpaths):
  r=read(p);exits=[r[k] for k in ['exit_code','actual_exit_code'] if k in r];assert exits and all(c==0 for c in exits)
  cmd=['lake','env','lean',f'SafeLearning/{module}.lean'] if index==0 else ['lake','build',f'SafeLearning.{module}'];assert r['command']==cmd
  assert r['actual_workdir']==str(ROOT/'verification/lean') and r['source_sha256_before']==r['source_sha256_after']==digest
  log=ROOT/r['log'];preserved=ROOT/r['preserved_source'];assert sha(log)==r['log_sha256'] and sha(preserved)==digest and source.read_bytes()==preserved.read_bytes()
  evidence.update({rel(p):sha(p),rel(log):sha(log),rel(preserved):sha(preserved)});actualrefs[rel(p)]=sha(p);actualpair.append({'reference':ref(p),'entire_original_actual_record':r})
 newproofs[rel(source)]={'sha256':digest,'evidence_sha256':evidence,'evidence_scope':'Actual canonical standalone and named target exit0 with exact raw logs/source snapshot; original complete-literal peer independently approved true mathematical clauses. Aggregate23 remains required.'}
 for row in peer['material_units']:
  key=row['source_unit_key'];unit=units[key];assert key not in mappedkeys;mappedkeys.add(key)
  assert row['entire_inventory_record']==unit==oldunits[key] and row['whole_unit_approved'] is True and row['material_status']=='proved' and row['missing_clauses']==[]
  assert set(row['lean_declarations'])<=set(names);covered.update(row['lean_declarations'])
  original=[r for r in old['material_claims'] if key in r['source_unit_keys']];pending=[r for r in original if r['status']=='pending'];assert pending and all(r['source_unit_keys']==[key] for r in pending)
  removedids.extend(r['id'] for r in pending)
  new={'id':key+'::independently-reviewed23-whole-literal','source_unit_keys':[key],'source':unit['source'],'locator':unit['locator'],'source_text':unit['source_text'],'source_text_sha256':unit['text_sha256'],'source_sha256':unit['source_sha256'],'statement_in_prose':unit['source_text'],'kind':'independently_reviewed_complete_mathematical_literal','status':'proved','lean_declarations':row['lean_declarations'],'hypotheses':row['hypotheses'],'correspondence':row['per_unit_reason'],'remaining_gaps':[],'source_review':{'file':rel(peerpath),'sha256':peersha,'reviewed_at_utc':peer['reviewed_at_utc'],'reviewer':peer['reviewer']}}
  candidate['material_claims']=[r for r in candidate['material_claims'] if r['id'] not in {r['id'] for r in pending}];candidate['material_claims'].append(new)
  mapping.append({'source_unit_key':key,'entire_current50_inventory_record':unit,'original_unchanged48_or49_entire_unit_peer_row':row,'original_semantic_review':ref(peerpath),'original_reviewed_at_utc':peer['reviewed_at_utc'],'entire_original_pending_clauses':pending,'retained_original_proved_or_nonformal_clauses':[r for r in original if r['status']!='pending'],'new_candidate_claim':new})
 candidate['proof_files'].append(rel(source));candidate['proof_sha256'][rel(source)]=digest
 packets.append({'module':module,'source':ref(source),'new_public_theorem_count':count,'public_theorem_names':names,'original_semantic_review':ref(peerpath),'canonical_readiness':ref(ready),'actual_pair':actualpair})
assert len(mappedkeys)==14 and len(removedids)==15 and len(allpublic)==39 and covered==allpublic
candidate['proof_files']=sorted(candidate['proof_files']);candidate['counts']['material_claim_statuses']=dict(Counter(r['status'] for r in candidate['material_claims']))
assert candidate['exercises']==old['exercises'] and candidate['surrounding_prose_reviews']==old['surrounding_prose_reviews'] and candidate['source_sha256']==old['source_sha256']
assert [r for r in old['material_claims'] if r['status']!='pending']==[r for r in candidate['material_claims'] if r['id'] not in {r['new_candidate_claim']['id'] for r in mapping} and r['status']!='pending']
assert [r for r in old['material_claims'] if r['id'] not in set(removedids)]==[r for r in candidate['material_claims'] if r['id'] not in {r['new_candidate_claim']['id'] for r in mapping}]
assert len(candidate['proof_files'])==len(old['proof_files'])+3 and physical(old)=={'total':1756,'whole_proved':748,'nonformal':524,'whole_pending':484} and physical(candidate)=={'total':1756,'whole_proved':762,'nonformal':524,'whole_pending':470}
candidate['current23_owner_identity']={'inventory':ref(INV),'unchanged_entire_foundation_inventory_units':1756,'unchanged_entire_foundation_exercise_records':119,'original22_ledger':ref(snapshot),'original_source48_inventory':ref(ROOT/'book/coverage/inventory-after-correction48.json'),'original_source49_inventory':ref(ROOT/'book/coverage/inventory-after-correction49.json'),'scope':'Global identity50 is new; all Foundation physical source pages, entire119/1756 inventory records and old semantic decision bodies/times remain unchanged.'}
candidate['current23_material_mapping']={'interface_binding':rel(BINDING),'whole_material_units':14,'removed_prior_pending_claims':15,'new_public_exports':39,'new_proof_sources':3,'physical_before':physical(old),'physical_after':physical(candidate),'scope':'Isolated future23 candidate only. Current22 ledgers/proofs/source48 snapshots are immutable; source49/50 edits concern Monitoring/Scenario only.'}
candidate['limits'].append('Future23 isolated source50 identity candidate adds14 independently complete Foundation literal units using3 actual paired sources/39 exports. All119 complete exercises and1080 earlier proved material atoms remain byte-exact;484 old physical pending units decrease by14. Remaining470 units still require substantive mathematical work.')
write_new(CANDIDATE,candidate)
binding={'status':'exact_original_full_semantic_decisions_and_times_bound_to_isolated_source50_candidate23','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_ledger':ref(CANDIDATE),'held_original22_ledger':ref(snapshot),'current_inventory':ref(INV),'all1756_foundation_literals_and119_full_exercise_records_equal_source48':True,'material_units':mapping,'proof_packets':packets,'physical_before':physical(old),'physical_after':physical(candidate),'all_previous_proved_atoms_and_review_bodies_times_exact':True,'coverage_complete':False}
write_new(BINDING,binding)
draft={'schema_version':1,'status':'isolated_actual_paired_proofs_and_complete_literal_candidate23_pending_independent_mapping_peer','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'base_selection':'reports/full-coverage/checkpoint-22-selection.json','base_selection_sha256':sha(ROOT/'reports/full-coverage/checkpoint-22-selection.json'),'actual_passing_baseline_audit':'reports/full-coverage/lean-checkpoint-22/verification-original.json','actual_passing_baseline_audit_sha256':sha(ROOT/'reports/full-coverage/lean-checkpoint-22/verification-original.json'),'proof_files':newproofs,'new_proof_sources_for_checkpoint23':sorted(newproofs),'new_proof_file_count':3,'new_theorem_or_lemma_count':39,'mapped_ledger':rel(CANDIDATE),'mapped_ledger_sha256':sha(CANDIDATE),'held22_ledger':rel(snapshot),'held22_ledger_sha256':sha(snapshot),'working22_ledger':'book/coverage/foundations.json','working22_ledger_sha256':OLD_SHA,'source_sha256':candidate['source_sha256'],'current_inventory':rel(INV),'current_inventory_sha256':INV_SHA,'current_owner_builder':rel(Path(__file__)),'current_owner_builder_sha256':sha(Path(__file__)),'exact_source_reviews_sha256':semanticrefs,'actual_canonical_execution_records_sha256':actualrefs,'canonical_readiness_sha256':readinessrefs,'material23_exact_interface_binding':rel(BINDING),'material23_exact_interface_binding_sha256':sha(BINDING),'new_material_dispositions':{'exact_current_rows':14,'whole_proved':14,'nonformal':0,'whole_pending':0,'previous_pending_claims_removed':15},'exercise_counts':candidate['counts']['exercise_statuses'],'material_counts':physical(candidate),'original_semantic_reviews_body_and_time_retained':True,'independent_final_candidate_mapping_peer_pending':True,'actual_builder_record_pending':True,'coverage_complete':False,'scope':'Three actual paired immutable new Foundation sources,39 public theorems,14 independently complete whole source units. The candidate preserves exact119 exercise bodies/all1080 old proved material atoms and unchanged Foundation literals under new global50 identity. No current ledger installation, aggregate23/selection or publication claimed.'}
write_new(DRAFT,draft);guard()
integrity={'status':'passed_isolated_candidate_preserves_every_prior22_foundation_row_and_selected_source','checked_at_utc':datetime.now(timezone.utc).isoformat(),'protected_current50_sources_inventory_and_four_working22_ledgers_sha256':protected,'frozen22_all31_source48_asset_sha256':assets,'all1113_selected22_sources_exact':True,'all119_exercise_bodies_and1080_proved_atoms_exact':True,'all1756_entire_foundation_source_records_unchanged48_to50':True,'removed_pending_claim_ids':removedids,'candidate':ref(CANDIDATE),'interface':ref(BINDING),'draft_offer':ref(DRAFT),'coverage_complete':False}
write_new(INTEGRITY,integrity);guard()
print(json.dumps({'status':draft['status'],'candidate':ref(CANDIDATE),'binding':ref(BINDING),'draft':ref(DRAFT),'integrity':ref(INTEGRITY),'new_exports':39,'whole_units':14,'physical_after':physical(candidate)}))

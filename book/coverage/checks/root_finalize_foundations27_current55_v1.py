"""Bind the reviewed Foundation43 TMP draft to six real canonical commands.

Isolated only. Root must review this new helper before explicit --apply. Original
semantic bodies, times, all failed readers/trials and old ledger rows stay exact.
The new offer still requires a final independent canonical/mapping confirmation.
"""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,copy,re
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/foundations-future27/source55'
DRAFT=Path('/tmp/foundations27-source55-three-source43-five-whole-unit-draft-v2')
READY=DRAFT/'foundations27-current55-three-source43-five-whole-unit-readiness-draft-v1.json'
READY_SHA='1796b230351781e57b26921ccf47b92fff5a561500d292af1b4c6a413c6f7c7e'
PEER=Path('/tmp/foundations27-current55-draft-independent-applied-confirmation-v1.json')
PEER_SHA='733a98acc304123c805e12e9b08ee89fb8bfa7b1251c5b662b4f41fdaf045119'
PAIRS='book/coverage/checks/future27-core/eight-source141-canonical-v1/eight-source141-actual-canonical-paired-readiness27-v1.json'
PAIRS_SHA='74f6e5413cb390698e6090b798d6f0eed0b667082bd24681f7b2e82c49deef1f'
ACTUAL='reports/full-coverage/eight-source141-canonical-pairs27-execution-v1.json'
ACTUAL_SHA='9ee7428bc5d16d6b65ec0fd88877d85e3ba38cb879f11951eca72ddd0b6df384'
PAIR_HELPER='book/coverage/checks/run_root27_eight_source141_canonical_pairs_v2.py'
PAIR_HELPER_SHA='30dda287631fe698f4d39ef16a5c92b42cee332dfcf7bc45a178630d1f4de8c0'
INV='book/coverage/inventory-after-correction55.json';INV_SHA='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
OLD='book/coverage/foundations.json';OLD_SHA='60b1ebaa5d44b3e371466d89cc9af68572ccdc069127504940a5c6c7ecd48b3a'
BUILDER=Path('/tmp/prepare-foundations27-source55-five-whole-unit-draft-v2.py')
BUILDER_SHA='0708b2bce819c301cb7c62fcbbe74d34f332af335ce77a90849ec8ca6b20a98d'
BUILDER_ACTUAL=Path('/tmp/foundations27-source55-five-whole-unit-draft-preparation-actual-v2.json')
BUILDER_RUNNER=Path('/tmp/run-foundations27-source55-five-whole-unit-draft-preparation-v2.py')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def locate(n):
 p=Path(n)
 if p.is_absolute():assert p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to(Path('/tmp'))
 else:
  assert p.as_posix()==n and '..' not in p.parts and '.' not in p.parts;p=ROOT/p;assert p.resolve().is_relative_to(ROOT)
 assert p.is_file() and not p.is_symlink(),str(p)
 return p

def checked(r):
 assert set(r)=={'file','sha256'} and re.fullmatch('[0-9a-f]{64}',r['sha256'])
 p=locate(r['file']);assert sha(p)==r['sha256'],str(p);return p

def ref(p):return {'file':p.relative_to(ROOT).as_posix() if p.is_relative_to(ROOT) else str(p),'sha256':sha(p)}
def read(p):return json.loads(p.read_bytes())
def zero(d):
 codes=[d[k] for k in ('actual_exit_code','exit_code','actual_runner_exit_code') if k in d]
 assert codes and all(type(c)is int and c==0 for c in codes)
def write(p,d):
 with p.open('x') as f:f.write(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def raw_alias_plan(original,digest,source):
 checked({'file':str(source),'sha256':digest})
 key=original+'::'+digest
 target=BASE/'original-closed-bytes'/digest/Path(original).name
 return key,{'original_path':original,'original_sha256':digest,'byte_copy_source':str(source),'immutable_byte_copy':{'file':target.relative_to(ROOT).as_posix(),'sha256':digest}}
def prepare():
 assert sha(READY)==READY_SHA and sha(PEER)==PEER_SHA and sha(BUILDER)==BUILDER_SHA
 assert sha(ROOT/OLD)==OLD_SHA and sha(ROOT/INV)==sha(ROOT/'book/coverage/inventory.json')==INV_SHA
 assert sha(ROOT/PAIRS)==PAIRS_SHA and sha(ROOT/ACTUAL)==ACTUAL_SHA and not BASE.exists()
 ready=read(READY);draft_path=checked(ready['candidate_ledger']);draft=read(draft_path);interface=read(checked(ready['interface']));plan=read(checked(ready['canonical_pair_plan']));peer=read(PEER)
 assert peer['status']=='passed_independent_tmp_only_foundations27_current55_draft_mechanics_pair_plan_pending' and peer['errors']==[]
 assert peer['readiness']==ref(READY) and peer['candidate']==ready['candidate_ledger'] and peer['interface']==ready['interface'] and peer['canonical_pair_plan']==ready['canonical_pair_plan']
 assert peer['exact_entire_ledger_inverse'] is True and peer['all_five_original_decisions_hypotheses_names_reasons_times_match'] is True
 assert ready['source_count']==3 and ready['new_public_exports']==43 and ready['whole_material_unit_count']==5 and ready['canonical_pair_execution_count']==0
 assert draft['exercises']==read(ROOT/OLD)['exercises'] and len(draft['exercises'])==119
 actual=read(ROOT/ACTUAL);zero(actual);assert actual['actual_command']==['python3',PAIR_HELPER,'--apply'] and actual['actual_workdir']==str(ROOT)
 expected_helpers={PAIR_HELPER:PAIR_HELPER_SHA,'book/coverage/check_core_standalone.py':'124bab45d3f48204b7436d721bf0b414c216a42e57b91a937dbd9e2ac6c8300a','book/coverage/check_core_named_build.py':'605ac2593a1b49044d011abc2d59cf3c4a422617929455754594199a5af73069'}
 assert actual['helper_sha256_before']==actual['helper_sha256_after']==expected_helpers
 for n,h in expected_helpers.items():checked({'file':n,'sha256':h})
 checked({'file':actual['log'],'sha256':actual['log_sha256']})
 pairs=read(ROOT/PAIRS);assert pairs['status']=='passed_actual_eight_source141_canonical_standalone_and_named_pairs_unselected_future27' and pairs['errors']==[]
 assert pairs['source_count']==8 and pairs['public_theorem_count']==141 and pairs['actual_compiler_command_count']==len(pairs['actual_paired_records'])==16
 assert pairs['coverage_complete'] is False and pairs['owner_installation_claimed'] is False and pairs['selection_or_aggregate_or_publication_claimed'] is False
 builder_actual=read(BUILDER_ACTUAL);zero(builder_actual);assert builder_actual['actual_command']==['python3',str(BUILDER)] and builder_actual['actual_workdir']==str(ROOT)
 assert builder_actual['helper_sha256_before']==builder_actual['helper_sha256_after']==BUILDER_SHA;checked({'file':builder_actual['log'],'sha256':builder_actual['log_sha256']})
 aliases={}
 def add(original,h,source):
  key,row=raw_alias_plan(original,h,source)
  if key in aliases:assert aliases[key]['original_sha256']==row['original_sha256']
  else:aliases[key]=row
 for original,row in interface['exact_original_byte_aliases'].items():
  assert original==row['original_path']+'::'+row['original_sha256'] and row['immutable_byte_copy']['sha256']==row['original_sha256']
  add(row['original_path'],row['original_sha256'],checked(row['immutable_byte_copy']))
 assert len(aliases)==110
 for r in [ref(READY),ready['candidate_ledger'],ready['interface'],ready['canonical_pair_plan'],ref(BUILDER),ref(BUILDER_ACTUAL),ref(BUILDER_RUNNER),{'file':builder_actual['log'],'sha256':builder_actual['log_sha256']},ref(PEER)]:add(r['file'],r['sha256'],checked(r))
 for n,h in peer['closed_evidence_sha256'].items():add(n,h,checked({'file':n,'sha256':h}))
 # All original semantic references are closed without rewriting their raw bodies.
 for r in ready['original_whole_source_reviews']:
  body=read(checked(r));assert body['errors']==[] and body['reviewed_at_utc'];add(r['file'],r['sha256'],checked(r))
 protected=dict(pairs['protected_input_sha256'])
 for r in pairs['sources']:protected[r['canonical_source']]=r['source']['sha256']
 for n,h in protected.items():checked({'file':n,'sha256':h})
 packets=interface['proof_packets'];assert len(packets)==3 and sum(r['public_theorem_count'] for r in packets)==43
 proof_rows={};all_names=[]
 for packet in packets:
  n=packet['planned_canonical_source'];h=packet['original_tmp_source']['sha256'];source=checked(packet['original_tmp_source']);assert sha(ROOT/n)==h
  assert source.read_text()==packet['entire_source_bytes'] if 'entire_source_bytes' in packet else True
  source_row=next(r for r in pairs['sources'] if r['canonical_source']==n);assert source_row['source']==packet['original_tmp_source'] and source_row['public_theorem_count']==packet['public_theorem_count']
  names=source_row['all_public_declarations'];assert len(names)==packet['public_theorem_count'] and [x.rsplit('.',1)[-1] for x in names]==re.findall(r'^theorem\s+(\w+)',source.read_text(),re.M);all_names+=names
  rows=[r for r in pairs['actual_paired_records'] if r['source']['file']==n];assert len(rows)==2 and {r['kind'] for r in rows}=={'standalone','named'}
  evidence={n:h,PAIRS:PAIRS_SHA,ACTUAL:ACTUAL_SHA,actual['log']:actual['log_sha256']}
  for r in rows:
   assert r['source']=={'file':n,'sha256':h} and type(r['actual_exit_code'])is int and r['actual_exit_code']==0
   native=read(checked(r['actual_record']));zero(native);assert native['source']==n and native['source_sha256_before']==native['source_sha256_after']==h and native['source_unchanged'] is True
   expected=['lake','env','lean','SafeLearning/'+Path(n).name] if r['kind']=='standalone' else ['lake','build','SafeLearning.'+Path(n).stem]
   assert native['command']==expected and native['actual_workdir']==str(ROOT/'verification/lean')
   assert r['raw_log']=={'file':native['log'],'sha256':native['log_sha256']} and r['source_snapshot']['sha256']==h
   for field in ('actual_record','raw_log','source_snapshot'):checked(r[field]);evidence[r[field]['file']]=r[field]['sha256']
  proof_rows[n]={'sha256':h,'theorem_count':len(names),'public_theorem_names':names,'mapped_named_declarations':names,'evidence_sha256':evidence,'actual_pair':rows,'evidence_scope':'Exact original full literal decisions and six real canonical commands; no source model assumptions are broadened.'}
 assert len(all_names)==len(set(all_names))==43
 new=copy.deepcopy(draft);old_proof_files=copy.deepcopy(new['proof_files']);old_proof_sha256=copy.deepcopy(new['proof_sha256']);assert len(old_proof_files)==247
 new['proof_files']=sorted(old_proof_files+list(proof_rows));assert len(new['proof_files'])==250
 new['proof_sha256']=old_proof_sha256|{n:r['sha256'] for n,r in proof_rows.items()}
 for n,h in old_proof_sha256.items():assert new['proof_sha256'][n]==h
 changes=[]
 def alias(original,h):return aliases[original+'::'+h]['immutable_byte_copy']
 for unit in interface['material_units']:
  cid=unit['new_candidate_claim']['id'];claim=next(c for c in new['material_claims'] if c['id']==cid);assert claim==unit['new_candidate_claim']
  original=copy.deepcopy(claim['source_review']);claim['source_review']={**original,'file':alias(original['file'],original['sha256'])['file']};changes.append({'claim_id':cid,'original_source_review':original,'canonical_source_review':copy.deepcopy(claim['source_review'])})
 assert len(changes)==5 and new['exercises']==draft['exercises']
 new['current27_material_mapping']={'original_exact_tmp_mapping':alias(str(draft_path),sha(draft_path)),'original_draft_readiness':alias(str(READY),READY_SHA),'original_independent_draft_mechanics_peer':alias(str(PEER),PEER_SHA),'actual_canonical_paired_readiness':{'file':PAIRS,'sha256':PAIRS_SHA},'actual_canonical_pair_execution':{'file':ACTUAL,'sha256':ACTUAL_SHA},'new_proof_files':list(proof_rows),'new_public_exports':43,'whole_material_units':5,'actual_canonical_commands':6,'active_review_path_changes':changes,'original_proof_files':old_proof_files,'original_proof_sha256':old_proof_sha256,'full_original_semantic_body_time_scope_preserved':True,'final_independent_mapping_review_pending':True}
 inverse=copy.deepcopy(new);inverse.pop('current27_material_mapping');inverse['proof_files']=old_proof_files;inverse['proof_sha256']=old_proof_sha256
 for c in changes:next(r for r in inverse['material_claims'] if r['id']==c['claim_id'])['source_review']=c['original_source_review']
 assert inverse==draft
 # This full preflight closes every source/copy before the first new directory.
 for row in aliases.values():checked({'file':row['byte_copy_source'],'sha256':row['original_sha256']})
 for n,h in protected.items():checked({'file':n,'sha256':h})
 return ready,new,interface,proof_rows,aliases,protected,actual

def execute():
 helper_sha=sha(Path(__file__));ready,new,interface,proof_rows,aliases,protected,actual=prepare();BASE.mkdir(parents=True)
 copied={}
 for row in aliases.values():
  source=checked({'file':row['byte_copy_source'],'sha256':row['original_sha256']});target=ROOT/row['immutable_byte_copy']['file']
  if target in copied:assert copied[target]==row['original_sha256']
  else:
   assert not target.exists();target.parent.mkdir(parents=True,exist_ok=True)
   with target.open('xb') as f:f.write(source.read_bytes())
   assert sha(target)==row['original_sha256'];copied[target]=row['original_sha256']
 closure={row['immutable_byte_copy']['file']:row['immutable_byte_copy']['sha256'] for row in aliases.values()}
 closure[Path(__file__).relative_to(ROOT).as_posix()]=helper_sha
 for row in proof_rows.values():row['evidence_sha256'].update(closure)
 candidate=BASE/'foundations27-current55-five-whole-unit-candidate-v1.json';write(candidate,new)
 binding=BASE/'foundations27-current55-five-whole-unit-canonical-binding-v1.json'
 write(binding,{'status':'passed_exact_isolated_canonical_byte_and_original_review_binding','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':ref(candidate),'original_tmp_interface':aliases[str(checked(ready['interface']))+'::'+ready['interface']['sha256']]['immutable_byte_copy'],'material_units':interface['material_units'],'original_closed_byte_aliases':aliases,'new_proof_files':proof_rows,'full_original_semantic_body_time_scope_preserved':True,'final_independent_mapping_review_pending':True,'coverage_complete':False})
 offer=BASE/'foundations-audit27-candidate-source55-additions-v1.json'
 reviews={aliases[r['file']+'::'+r['sha256']]['immutable_byte_copy']['file']:r['sha256'] for r in ready['original_whole_source_reviews']}
 write(offer,{'schema_version':1,'status':'paired_isolated_current55_foundations_candidate_awaiting_final_independent_mapping_review','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'proof_files':proof_rows,'new_proof_file_count':3,'new_theorem_or_lemma_count':43,'mapped_ledger':candidate.relative_to(ROOT).as_posix(),'mapped_ledger_sha256':sha(candidate),'candidate':ref(candidate),'held26_ledger':OLD,'held26_ledger_sha256':OLD_SHA,'source_sha256':new['source_sha256'],'current_inventory':INV,'current_inventory_sha256':INV_SHA,'current_owner_builder':Path(__file__).relative_to(ROOT).as_posix(),'current_owner_builder_sha256':helper_sha,'original_tmp_builder':aliases[str(BUILDER)+'::'+BUILDER_SHA]['immutable_byte_copy'],'original_tmp_builder_actual':aliases[str(BUILDER_ACTUAL)+'::'+sha(BUILDER_ACTUAL)]['immutable_byte_copy'],'original_independent_draft_mechanics_peer':aliases[str(PEER)+'::'+PEER_SHA]['immutable_byte_copy'],'original_full_source_reviews_sha256':reviews,'original_closed_byte_aliases':aliases,'actual_canonical_paired_readiness':{'file':PAIRS,'sha256':PAIRS_SHA},'actual_canonical_pair_execution':{'file':ACTUAL,'sha256':ACTUAL_SHA},'material27_exact_interface_binding':ref(binding),'new_whole_material_units':5,'all119_original_exercise_bodies_unchanged':True,'old247_proof_metadata_exact':True,'original_semantic_reviews_body_and_time_retained':True,'actual_canonical_commands':6,'additional_frozen_inputs':closure,'final_independent_candidate_mapping_peer_pending':True,'actual_finalizer_record_pending':True,'coverage_complete':False,'scope':'Isolated Foundation3/43 canonical binding and five already reviewed whole literal mappings only. Every original mathematical body, hypothesis, time and earlier failure is retained. A final independent canonical/mapping peer and closed actual finalizer record are still required; no installed owner, whole parent exercise, selection, aggregate or publication claim.'})
 for n,h in protected.items():checked({'file':n,'sha256':h})
 assert sha(Path(__file__))==helper_sha and sha(ROOT/OLD)==OLD_SHA and sha(ROOT/'book/coverage/inventory.json')==INV_SHA
 print(json.dumps({'status':'passed_isolated_foundations27_canonical_binding','candidate':ref(candidate),'offer':ref(offer),'binding':ref(binding),'source_count':3,'exports':43,'actual_canonical_commands':6,'installed_owner_write':False}))

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--apply',action='store_true');args=p.parse_args();assert args.apply,'Root must review before explicit --apply';execute()

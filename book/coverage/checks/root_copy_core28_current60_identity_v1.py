"""Create exact durable Core60 metadata aliases without changing reviewed bytes."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,copy,hashlib,json
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/future28-core/current60-identity-v1'
CAT=Path('/tmp/core28-current60-identity-v1/core28-current60-complete-original-byte-closure-catalog-v1.json')
CAT_SHA='34f0b347d4031bd0fc3b64c4426efc37da68140436d4a080cd60d64a7bae6c3b';INV_SHA='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();J=lambda p:json.loads(p.read_bytes())
def path(n):
 p=Path(n);return p if p.is_absolute()else ROOT/p
def checked(r):
 assert set(r)=={'file','sha256'};p=path(r['file']);assert p.is_file()and not p.is_symlink()and H(p)==r['sha256'];assert p.resolve().is_relative_to(ROOT)or p.resolve().is_relative_to('/tmp');return p
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':H(p)}
def prepare():
 assert H(CAT)==CAT_SHA and not BASE.exists()and H(ROOT/'book/coverage/inventory.json')==INV_SHA
 c=J(CAT);assert c['status']=='passed_exact_tmp_core28_current60_complete_closed_byte_refs'and c['errors']==[]
 source=checked(c['final_offer']);assert H(source)=='0a064eeccac940fb620f6b299831d878bce8ba8fe16bbca59f33e2debe1dd904'
 old=J(source);assert old['status']=='independently_reviewed_isolated_core28_current60_identity_offer'and old['errors']==[]and old['proof_files']=={}and old['new_actual_paired_records']==[]and old['new_material_keys']==[]and old['inventory_sha256']==INV_SHA
 peer_ref=old['final_independent_candidate_mapping_peer'];assert peer_ref['sha256']=='95fc995e2ce0ca0482ea3eb7bcec848ab95c667e72231e4f24acad188bdb0f7b';peer=J(checked(peer_ref));assert peer['status']=='passed_independent_exact_forward_inverse_core28_current60_identity_mechanics'and peer['errors']==[]and peer['candidate']==old['candidate']and peer['actual_author_preparation']==old['actual_isolated_candidate_preparation']
 entries={}
 for row in c['entries']:
  n=row['original_path'];assert n not in entries;p=checked({'file':row['file'],'sha256':row['sha256']});assert p.stat().st_size==row['bytes'];entries[n]={'file':str(p),'sha256':row['sha256']}
 entries[str(CAT)]={'file':str(CAT),'sha256':CAT_SHA}
 for n,h in old['required_evidence_artifacts_sha256'].items():assert n in entries and entries[n]['sha256']==h
 actual=J(checked(old['actual_isolated_candidate_preparation']));assert type(actual['actual_exit_code'])is int and actual['actual_exit_code']==0 and actual['helper_sha256_before']==actual['helper_sha256_after']
 for n,h in actual['helper_sha256_before'].items():assert n in entries and entries[n]['sha256']==h
 assert entries[actual['log']]['sha256']==actual['log_sha256']
 held={r['destination']:r['candidate']['sha256']for r in J(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']}
 for n,h in held.items():assert H(ROOT/n)==h
 return old,source,entries,held,actual
def main():
 p=argparse.ArgumentParser();p.add_argument('--apply',action='store_true');a=p.parse_args();old,source,entries,held,actual=prepare()
 if not a.apply:print(json.dumps({'status':'passed_read_only_core28_current60_exact_copy_preflight','candidate':old['candidate'],'original_refs':len(entries),'writes':False}));return
 BASE.mkdir(parents=True);aliases={}
 for original,r in sorted(entries.items()):
  source_file=checked(r)
  if source_file.is_relative_to(ROOT):target=source_file
  else:
   target=BASE/'original-closed-bytes'/r['sha256']/source_file.name;target.parent.mkdir(parents=True,exist_ok=True)
   if not target.exists():
    with target.open('xb')as f:f.write(source_file.read_bytes())
   assert H(target)==r['sha256']
  aliases[original]=ref(target)
 def canon(r):
  if r['file']in aliases:
   a=aliases[r['file']];assert a['sha256']==r['sha256'];return a
  f=checked(r);assert f.is_relative_to(ROOT);return ref(f)
 new=copy.deepcopy(old)
 for k in ['candidate','identity_sidecar','identity_integrity','candidate_builder','actual_isolated_candidate_preparation','actual_candidate_preparation_raw_log','actual_candidate_preparation_runner','original_unexecuted_offer_draft','base_selection','final_independent_candidate_mapping_peer','actual_finalizer','original_pre_mechanics_offer','original_independent_review_body_and_time_preserved_by_exact_ref','offer_finalizer_helper','actual_offer_finalization','actual_offer_finalization_raw_log','actual_offer_finalization_runner','original_reviewed_offer_before_native_closure']:new[k]=canon(old[k])
 new['mapped_ledger']=new['candidate']['file'];native_names=set(actual['helper_sha256_before'])|{actual['log']};native_aliases={n:aliases[n]for n in sorted(native_names)}
 peer_ref=new['final_independent_candidate_mapping_peer'];interface={'status':'exact_original_independent_peer_pointer_alias_interface','errors':[],'candidate':new['candidate'],'actual_finalizer':new['actual_finalizer'],'original_peer':peer_ref,'original_peer_status':'passed_independent_exact_forward_inverse_core28_current60_identity_mechanics','original_peer_body_and_time_byte_identity':True,'native_actual_preparation_byte_identity':True,'native_absolute_helper_and_log_byte_aliases':native_aliases,'new_semantic_review_or_native_execution_claimed':False,'scope':'Only durable pointer aliases for the unchanged independently reviewed Core60 candidate and genuine author preparation; no new review time or semantic decision.'}
 interface_path=BASE/'core28-current60-original-independent-peer-pointer-alias-interface-v1.json'
 with interface_path.open('x')as f:f.write(json.dumps(interface,indent=2)+'\n')
 new['final_independent_candidate_mapping_peer']=ref(interface_path);new['independent_peer_expected_status']=interface['status'];new['actual_finalizer_original_byte_aliases']=native_aliases;new['original_complete_independent_peer']=peer_ref;new['original_closed_byte_aliases']=aliases
 closure={}
 for n,h in old['required_evidence_artifacts_sha256'].items():r=canon({'file':n,'sha256':h});assert r['file']not in closure or closure[r['file']]==h;closure[r['file']]=h
 for r in aliases.values():closure[r['file']]=r['sha256']
 closure[ref(interface_path)['file']]=H(interface_path);closure[ref(Path(__file__))['file']]=H(Path(__file__));new['required_evidence_artifacts_sha256']=closure
 new['root_exact_current60_identity_byte_copy']={'copied_at_utc':datetime.now(timezone.utc).isoformat(),'original_final_offer':aliases[str(source)],'original_catalog':aliases[str(CAT)],'helper':ref(Path(__file__)),'candidate_bytes_unchanged':True,'new_proofs':0,'installed_owner_write':False}
 F=BASE/'core28-current60-identity-offer-canonical-v1.json'
 with F.open('x')as f:f.write(json.dumps(new,indent=2,ensure_ascii=False)+'\n')
 for n,h in held.items():assert H(ROOT/n)==h
 assert H(ROOT/'book/coverage/inventory.json')==INV_SHA
 for r in entries.values():checked(r)
 print(json.dumps({'status':'passed_exact_core28_current60_root_identity_copy','offer':ref(F),'interface':ref(interface_path),'candidate':new['candidate'],'actual_finalizer':new['actual_finalizer'],'aliases':len(aliases),'new_proofs':0,'installed_owner_written':False}))
if __name__=='__main__':main()

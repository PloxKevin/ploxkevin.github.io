"""Copy the closed TMP Applied60 zero-proof identity offer to exact Root aliases.

No installed owner, canonical Lean source, selection, HTML or PUB write.
Original candidates and native/peer bodies retain byte identity and timestamps.
"""
from pathlib import Path
from datetime import datetime,timezone
import argparse,copy,hashlib,json
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/applied-future28/current60-identity-v1'
CATALOG=Path('/tmp/applied28-source60-identity-v1/applied28-current60-complete-original-byte-closure-catalog-v1.json')
CATALOG_SHA='07d40280964470b92e47f1f8361961269ca35448c2364de50b75f88eec9b0c43'
INV_SHA='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
PEER_SHA='d267fdb10f27fc6cfda1fd5ab7512c15b427831483147539989f6dda9116bd81'
PEER_STATUS='passed_independent_applied28_current60_zero_proof_candidate_mechanics'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_bytes())
def checked(r):
 assert isinstance(r,dict)and isinstance(r.get('file'),str)and isinstance(r.get('sha256'),str)
 p=Path(r['file']);p=p if p.is_absolute()else ROOT/p
 assert p.is_file()and not p.is_symlink()and sha(p)==r['sha256']
 assert p.resolve().is_relative_to(ROOT)or p.resolve().is_relative_to(Path('/tmp'))
 return p
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
def prepare():
 assert sha(CATALOG)==CATALOG_SHA and not BASE.exists()
 assert sha(ROOT/'book/coverage/inventory.json')==INV_SHA
 catalog=load(CATALOG);assert catalog['status']=='passed_exact_tmp_applied28_current60_complete_closed_byte_refs'and catalog['errors']==[]
 source=checked(catalog['final_offer']);assert sha(source)=='8aa54986e8941d9fca3239d1c1f87c2b4467d8d647d85ff8ff48a214254036a9'
 old=load(source);assert old['status']=='independently_reviewed_isolated_applied28_current60_identity_offer'and old['errors']==[]
 assert old['inventory_sha256']==INV_SHA and old['proof_files']=={}and old['new_actual_paired_records']==[]and old['new_material_keys']==[]
 assert old['candidate']=={'file':old['mapped_ledger'],'sha256':old['mapped_ledger_sha256']}
 assert old['candidate_promotions']=={'file':old['mapped_promotions'],'sha256':old['mapped_promotions_sha256']}
 assert old['final_independent_candidate_mapping_peer']['sha256']==PEER_SHA
 peer=load(checked(old['final_independent_candidate_mapping_peer']));assert peer['status']==PEER_STATUS and peer['errors']==[]and peer['protection_errors']==[]
 assert peer['reader_decision']['candidate']==old['candidate']and peer['reader_decision']['candidate_promotions']==old['candidate_promotions']
 actual=load(checked(old['actual_offer_finalization']));assert type(actual['actual_exit_code'])is int and actual['actual_exit_code']==0
 assert actual['helper_sha256_before']==actual['helper_sha256_after']and sha(Path(actual['log']))==actual['log_sha256']
 held=dict(old['baseline27_owner_sha256'])
 for n,h in held.items():assert sha(ROOT/n)==h
 entries={}
 for row in catalog['entries']:
  original=row['original_path'];assert isinstance(original,str)and original not in entries
  p=checked(row);assert p.stat().st_size==row['bytes'];entries[original]={'file':str(p),'sha256':row['sha256']}
 for n,h in old['required_evidence_artifacts_sha256'].items():assert n in entries and entries[n]['sha256']==h
 entries[str(CATALOG)]={'file':str(CATALOG),'sha256':CATALOG_SHA}
 for r in entries.values():checked(r)
 return old,source,entries,held
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--apply',action='store_true');args=parser.parse_args()
 old,source,entries,held=prepare()
 if not args.apply:
  print(json.dumps({'status':'passed_read_only_applied28_current60_exact_copy_preflight','original_offer':{'file':str(source),'sha256':sha(source)},'original_refs':len(entries),'new_proofs':0,'writes':False}));return
 BASE.mkdir(parents=True)
 aliases={}
 for original,r in sorted(entries.items()):
  p=checked(r)
  if p.is_relative_to(ROOT):target=p
  else:
   target=BASE/'original-closed-bytes'/r['sha256']/p.name;target.parent.mkdir(parents=True,exist_ok=True)
   if not target.exists():
    with target.open('xb')as f:f.write(p.read_bytes())
   assert not target.is_symlink()and sha(target)==r['sha256']
  aliases[original]=ref(target)
 def canon(r):
  if r['file']in aliases:
   a=aliases[r['file']];assert a['sha256']==r['sha256'];return a
  p=checked(r);assert p.is_relative_to(ROOT);return ref(p)
 new=copy.deepcopy(old)
 keys=['candidate','candidate_promotions','candidate_builder','identity_sidecar','identity_integrity','original_reviewed_source55_offer','final_independent_candidate_mapping_peer','actual_isolated_candidate_preparation','original_preparation_offer','original_independent_review_body_and_time_preserved_by_exact_ref','original_pre_mechanics_offer','actual_offer_finalizer','actual_offer_finalization','actual_offer_finalization_raw_log','actual_offer_finalization_runner','original_reviewed_offer_before_native_closure']
 for k in keys:new[k]=canon(old[k])
 new['preserved_finalizer_schema_failure']['actual']=canon(old['preserved_finalizer_schema_failure']['actual'])
 new['mapped_ledger']=new['candidate']['file'];new['mapped_promotions']=new['candidate_promotions']['file']
 new['actual_finalizer']=new['actual_isolated_candidate_preparation']
 original_peer=canon(old['final_independent_candidate_mapping_peer'])
 interface={'status':PEER_STATUS,'errors':[],'candidate':new['candidate'],'candidate_promotions':new['candidate_promotions'],'actual_finalizer':new['actual_finalizer'],'original_independent_peer_exact_body_and_time':original_peer,'original_independent_status_and_errors_preserved':True,'original_author_preparation_native_body_and_time_unchanged':True,'new_review_or_native_execution_claimed':False,'scope':'Only explicit Root-relative aliases of the unchanged independently reviewed candidate/promotions and actual preparation pointers. The original independent decision body, timestamps and genuine native records remain byte-exact.'}
 interface_path=BASE/'applied28-current60-original-independent-review-canonical-pointer-interface-v1.json'
 with interface_path.open('x')as f:f.write(json.dumps(interface,indent=2,ensure_ascii=False)+'\n')
 new['final_independent_candidate_mapping_peer']=ref(interface_path)
 native=load(checked(old['actual_isolated_candidate_preparation']))
 original_native_names=set(native['helper_sha256_before'])|{native['log']}
 assert all(n in aliases for n in original_native_names)
 new['actual_finalizer_original_byte_aliases']={n:aliases[n]for n in sorted(original_native_names)}
 new['original_closed_byte_aliases']=aliases
 closure={}
 for n,h in old['required_evidence_artifacts_sha256'].items():
  c=canon({'file':n,'sha256':h});assert c['file']not in closure or closure[c['file']]==h;closure[c['file']]=h
 for r in aliases.values():closure[r['file']]=r['sha256']
 closure[ref(interface_path)['file']]=sha(interface_path)
 closure[ref(Path(__file__))['file']]=sha(Path(__file__))
 new['required_evidence_artifacts_sha256']=closure
 new['root_exact_current60_identity_byte_copy']={'copied_at_utc':datetime.now(timezone.utc).isoformat(),'original_final_offer':aliases[str(source)],'original_catalog':aliases[str(CATALOG)],'helper':ref(Path(__file__)),'candidate_and_promotions_bytes_unchanged':True,'new_proofs':0,'installed_owner_write':False}
 dest=BASE/'applied28-current60-identity-offer-canonical-v1.json'
 with dest.open('x')as f:f.write(json.dumps(new,indent=2,ensure_ascii=False)+'\n')
 for n,h in held.items():assert sha(ROOT/n)==h
 assert sha(ROOT/'book/coverage/inventory.json')==INV_SHA
 for r in entries.values():checked(r)
 assert checked(new['candidate']).read_bytes()==checked(old['candidate']).read_bytes()
 assert checked(new['candidate_promotions']).read_bytes()==checked(old['candidate_promotions']).read_bytes()
 print(json.dumps({'status':'passed_exact_applied28_current60_root_identity_copy','offer':ref(dest),'candidate':new['candidate'],'promotions':new['candidate_promotions'],'aliases':len(aliases),'new_proofs':0,'installed_owner_write':False}))
if __name__=='__main__':main()

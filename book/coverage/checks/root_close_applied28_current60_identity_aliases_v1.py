"""Close explicit durable pointers of the unchanged Applied60 independent review."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,copy,hashlib,json
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/applied-future28/current60-identity-v1'
SOURCE=BASE/'applied28-current60-identity-offer-canonical-v1.json'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();J=lambda p:json.loads(p.read_bytes())
def path(n):
 p=Path(n);return p if p.is_absolute()else ROOT/p
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':H(p)}
def checked(r):
 assert set(r)=={'file','sha256'};p=path(r['file']);assert p.is_file()and not p.is_symlink()and p.resolve().is_relative_to(ROOT)and H(p)==r['sha256'];return p
def prepare():
 old=J(SOURCE);assert old['status']=='independently_reviewed_isolated_applied28_current60_identity_offer'and old['errors']==[]and old['proof_files']=={}
 assert old['inventory_sha256']==H(ROOT/'book/coverage/inventory.json')=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
 aliases=old['original_closed_byte_aliases'];peer_ref=old['final_independent_candidate_mapping_peer'];assert peer_ref['sha256']=='d267fdb10f27fc6cfda1fd5ab7512c15b427831483147539989f6dda9116bd81'
 peer=J(checked(peer_ref));assert peer['status']=='passed_independent_applied28_current60_zero_proof_candidate_mechanics'and peer['errors']==[]
 for k in ['candidate','candidate_promotions']:
  original=peer['reader_decision'][k];assert aliases[original['file']]==old[k]and old[k]['sha256']==original['sha256'];checked(old[k])
 original_actual=peer['reader_decision']['native_author_preparation'];actual_ref=old['actual_isolated_candidate_preparation'];assert aliases[original_actual['file']]==actual_ref and actual_ref['sha256']==original_actual['sha256']=='37eb879d7bb468d327019531b1e9508d76caf9c9a883d931d3aff03dc5c23299'
 actual=J(checked(actual_ref));assert type(actual['actual_exit_code'])is int and actual['actual_exit_code']==0 and actual['helper_sha256_before']==actual['helper_sha256_after']
 names=set(actual['helper_sha256_before'])|{actual['log']};native_aliases={n:aliases[n]for n in sorted(names)}
 for n,r in native_aliases.items():assert Path(n).is_relative_to('/tmp');checked(r)
 assert all(native_aliases[n]['sha256']==h for n,h in actual['helper_sha256_before'].items())and native_aliases[actual['log']]['sha256']==actual['log_sha256']
 root_actual=ROOT/'reports/full-coverage/applied28-current60-root-identity-copy-execution-v1.json';ra=J(root_actual);assert type(ra['actual_exit_code'])is int and ra['actual_exit_code']==0 and H(ROOT/ra['log'])==ra['log_sha256']
 for n,h in old['required_evidence_artifacts_sha256'].items():assert H(ROOT/n)==h
 for n,h in old['baseline27_owner_sha256'].items():assert H(ROOT/n)==h
 return old,peer_ref,actual_ref,native_aliases,root_actual
def main():
 p=argparse.ArgumentParser();p.add_argument('--apply',action='store_true');a=p.parse_args();old,peer_ref,actual_ref,native_aliases,root_actual=prepare()
 interface_path=BASE/'applied28-current60-original-independent-peer-pointer-alias-interface-v1.json';offer_path=BASE/'applied28-current60-identity-offer-canonical-v2.json';assert not interface_path.exists()and not offer_path.exists()
 if not a.apply:print(json.dumps({'status':'passed_read_only_applied28_current60_exact_alias_interface_preflight','candidate':old['candidate'],'native_absolute_aliases':len(native_aliases),'writes':False}));return
 interface={'status':'exact_original_independent_peer_pointer_alias_interface','errors':[],'candidate':old['candidate'],'candidate_promotions':old['candidate_promotions'],'actual_finalizer':actual_ref,'original_peer':peer_ref,'original_peer_status':'passed_independent_applied28_current60_zero_proof_candidate_mechanics','original_peer_body_and_time_byte_identity':True,'native_actual_preparation_byte_identity':True,'native_absolute_helper_and_log_byte_aliases':native_aliases,'new_semantic_review_or_native_execution_claimed':False,'scope':'Only existing explicit Root pointer aliases for the exact original independent peer; no new review time or semantic decision.'}
 with interface_path.open('x')as f:f.write(json.dumps(interface,indent=2)+'\n')
 new=copy.deepcopy(old);new['final_independent_candidate_mapping_peer']=ref(interface_path);new['independent_peer_expected_status']=interface['status'];new['actual_finalizer']=actual_ref;new['actual_finalizer_original_byte_aliases']=native_aliases;new['original_complete_independent_peer']=peer_ref;new['root_copy_actual_execution']=ref(root_actual)
 for f in [SOURCE,interface_path,root_actual,ROOT/J(root_actual)['log'],Path(__file__)]:new['required_evidence_artifacts_sha256'][ref(f)['file']]=H(f)
 new['root_pointer_alias_closure']={'original_root_canonical_offer':ref(SOURCE),'helper':ref(Path(__file__)),'alias_only_closed_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_promotions_and_original_review_native_bytes_unchanged':True}
 with offer_path.open('x')as f:f.write(json.dumps(new,indent=2,ensure_ascii=False)+'\n')
 prepare();print(json.dumps({'status':'passed_exact_applied28_current60_original_pointer_alias_closure','offer':ref(offer_path),'interface':ref(interface_path),'candidate':new['candidate'],'promotions':new['candidate_promotions'],'actual_finalizer':actual_ref,'new_proofs':0,'installed_owner_written':False}))
if __name__=='__main__':main()

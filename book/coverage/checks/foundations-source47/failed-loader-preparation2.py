import json,hashlib,datetime,shutil
from pathlib import Path
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest='book/coverage/checks/foundations-source47-unchanged-review-identity-manifest-v2.json'
assert sha(manifest)=='def624c9cd63ce052aa07973e832670e413b7260fcff15e9bbf3fc6c9244e16f'
m=json.loads(Path(manifest).read_text())
peer_tmp='/tmp/modules-foundations-source47-unchanged-review-identity-manifest-v2-independent-mechanics-confirmation20-v1.json'
assert sha(peer_tmp)=='838002f6407ecb23dbf9ae1760f57cf2c8e86a394616bb6882c85a069f497dd3'
peer='book/coverage/checks/foundations-source47-unchanged-review-identity-independent-modules-confirmation-v2.json'
assert Path(peer).exists() and sha(peer)==sha(peer_tmp)
assert sha(peer)==sha(peer_tmp)
for r in m['preserved_current44_owner_assets']:
 assert sha(r['original'])==r['original_sha256']==sha(r['byte_copy'])==r['byte_copy_sha256']
promotions=Path('book/coverage/foundations_promotions.py'); before=promotions.read_text(); updated=before
changes=[]
for r in m['review_identity_versions']:
 assert sha(r['original_review'])==r['original_review_sha256']
 assert sha(r['new_identity_review'])==r['new_identity_review_sha256']
 assert updated.count(r['original_review'])>=1,(r['original_review'],'path absent')
 assert updated.count(r['original_review_sha256'])>=1,(r['original_review'],'sha absent')
 changes.append({'old_review':r['original_review'],'new_review':r['new_identity_review'],'old_sha256':r['original_review_sha256'],'new_sha256':r['new_identity_review_sha256'],'path_occurrences':updated.count(r['original_review']),'hash_occurrences':updated.count(r['original_review_sha256'])})
 updated=updated.replace(r['original_review'],r['new_identity_review']).replace(r['original_review_sha256'],r['new_identity_review_sha256'])
updated += '\n# Released20: exact current47 material decisions with immutable original reviews.\nfrom foundations_material20 import apply as _apply_material20\n_apply_material20(REVIEWED_COMPLETE_MATERIAL, REVIEWED_NONFORMAL_MATERIAL, REVIEWED_PARTIAL_MATERIAL)\n'
assert updated!=before; promotions.write_text(updated)
held=Path('book/coverage/foundations_held19.py'); oldheld=held.read_text(); newheld=oldheld.replace(m['held19_prior_binding'],m['held19_current47_binding']).replace(m['held19_prior_binding_sha256'],m['held19_current47_binding_sha256'])
assert newheld!=oldheld; held.write_text(newheld)
report={'schema_version':1,'status':'prepared_current47_confirmed_review_loaders_and_material20_integration','prepared_by':'/root/foundations_next','prepared_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'immutable_inventory_after':m['immutable_inventory_after'],'immutable_inventory_after_sha256':m['immutable_inventory_after_sha256'],'identity_manifest':manifest,'identity_manifest_sha256':sha(manifest),'identity_peer':peer,'identity_peer_sha256':sha(peer),'original_identity_peer_byte_copy':peer_tmp,'original_identity_peer_byte_copy_sha256':sha(peer_tmp),'exact_review_path_hash_replacements':changes,'held19_current_binding':m['held19_current47_binding'],'held19_current_binding_sha256':m['held19_current47_binding_sha256'],'material20_interface_binding':'book/coverage/checks/foundations-material20-source47-interface-binding-v1.json','material20_interface_binding_sha256':sha('book/coverage/checks/foundations-material20-source47-interface-binding-v1.json'),'material20_interface_peer':'book/coverage/checks/foundations-material20-source47-interface-independent-applied-confirmation-v1.json','material20_interface_peer_sha256':sha('book/coverage/checks/foundations-material20-source47-interface-independent-applied-confirmation-v1.json'),'current_helpers_sha256':{str(p):sha(p) for p in [promotions,held,Path('book/coverage/foundations_material20.py'),Path('book/coverage/build_foundations.py')]},'preserved_current44_owner_assets':m['preserved_current44_owner_assets'],'new_material_dispositions':{'units':256,'proved':31,'not_a_formal_claim':48,'pending':177,'approved_precise_components':15},'changed_five_basics_excluded':m['changed5_material_units_excluded'],'limits':['No mathematical review body, original review time, proof, compiler execution record or source file is changed.','The 29 identity references preserve literal text/hypotheses/gaps; only current inventory/page identity and explicit provenance differ.','The five newly changed Basics material units await fresh individual current47 source decisions.','The builder is run separately and its actual exit/log are recorded independently.']}
out=Path('book/coverage/checks/foundations-source47-reviewed20-loader-integration-v1.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'manifest':str(out),'sha256':sha(out),'helper_hashes':report['current_helpers_sha256']}))

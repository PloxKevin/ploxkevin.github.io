"""Copy the reviewed zero-proof Applied current55 offer into immutable Root paths."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/applied-future27/current55-identity-v1'
PACK=Path('/tmp/applied27-current55-reviewed-offer-original-byte-pack-v1/applied27-current55-reviewed-offer-original-byte-pack-v1.json')
PACK_SHA='f4745df04e99f3271e7a14b7fbc4d2b565fbbfab5aa6d610b4a178417f000fe1'
INV_SHA='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def checked(r):
 p=Path(r['file']);p=p if p.is_absolute() else ROOT/p
 assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256']
 assert p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to(Path('/tmp'))
 return p
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
assert sha(PACK)==PACK_SHA and not BASE.exists()
assert sha(ROOT/'book/coverage/inventory.json')==INV_SHA
pack=json.loads(PACK.read_bytes());offer_path=checked(pack['final_reviewed_offer']);old=json.loads(offer_path.read_bytes())
assert old==pack['entire_original_final_reviewed_offer_body_and_time']
assert old['status']=='independently_reviewed_isolated_applied27_current55_identity_only_offer' and old['errors']==[]
assert old['proof_files']=={} and old['new_actual_paired_records']==[] and old['new_material_keys']==[]
assert old['inventory_sha256']==INV_SHA and old['counts']['exercises']==old['counts']['complete_math']==128
assert old['counts']['partial']==old['counts']['pending']==0
peer_original=old['final_independent_candidate_mapping_peer']
assert peer_original['sha256']=='acf2bd0c04e30124109507023d7db14e0a0bfd54ce961fc61306296035f2e5f6'
peer=json.loads(checked(peer_original).read_bytes())
assert 'passed' in peer['status'] and peer.get('errors',[])==[]
assert peer==old['entire_original_independent_identity_peer_body_and_time']
held={n:sha(ROOT/n) for n in old['baseline26_owner_sha256']}
assert held==old['baseline26_owner_sha256']
originals=dict(pack['original_closed_byte_aliases'])
originals[str(PACK)]={'file':str(PACK),'sha256':PACK_SHA}
for p in ['prepare-applied27-current55-reviewed-offer-original-byte-pack-v1.py','run-applied27-current55-reviewed-offer-original-byte-pack-v1.py','applied27-current55-reviewed-offer-original-byte-pack-actual-v1.json','applied27-current55-reviewed-offer-original-byte-pack-actual-v1.log']:
 path=Path('/tmp')/p;originals[str(path)]={'file':str(path),'sha256':sha(path)}
actual=json.loads(checked(originals['/tmp/applied27-current55-reviewed-offer-original-byte-pack-actual-v1.json']).read_bytes())
assert type(actual['actual_exit_code']) is int and actual['actual_exit_code']==0
assert actual['helper_sha256_before']==actual['helper_sha256_after']
assert actual['actual_workdir']==str(ROOT)
assert sha(Path(actual['raw_log']))==actual['raw_log_sha256']
for n,h in pack['unchanged_root_evidence_sha256'].items():
 checked({'file':n,'sha256':h})
for r in originals.values():checked(r)
assert old['candidate']=={'file':old['mapped_ledger'],'sha256':old['mapped_ledger_sha256']}
assert old['candidate_promotions']=={'file':old['mapped_promotions'],'sha256':old['mapped_promotions_sha256']}
for r in [old['candidate'],old['candidate_promotions']]:
 assert r['file'] in originals and originals[r['file']]['sha256']==r['sha256']
BASE.mkdir(parents=True)
aliases={}
for original,r in sorted(originals.items()):
 source=checked(r);target=BASE/'original-closed-bytes'/r['sha256']/source.name
 target.parent.mkdir(parents=True,exist_ok=True)
 if not target.exists():
  with target.open('xb') as f:f.write(source.read_bytes())
 assert sha(target)==r['sha256'];aliases[original]=ref(target)
def canon(r):
 if r['file'] in aliases:
  a=aliases[r['file']];assert a['sha256']==r['sha256'];return a
 p=checked(r);assert p.is_relative_to(ROOT)
 return ref(p)
new=copy.deepcopy(old)
for k in ['candidate','candidate_promotions','candidate_builder','identity_sidecar','identity_integrity','original_source53_final_offer','final_independent_candidate_mapping_peer','actual_isolated_candidate_preparation','preserved_original_draft_offer']:
 new[k]=canon(old[k])
new['mapped_ledger']=new['candidate']['file'];new['mapped_promotions']=new['candidate_promotions']['file']
new['original_installed26_exact_byte_copies']={k:canon(v) for k,v in old['original_installed26_exact_byte_copies'].items()}
new['original_closed_byte_aliases']=aliases
evidence={}
for n,h in old['required_evidence_artifacts_sha256'].items():
 r=canon({'file':n,'sha256':h});assert r['file'] not in evidence or evidence[r['file']]==h;evidence[r['file']]=h
for r in aliases.values():evidence[r['file']]=r['sha256']
new['required_evidence_artifacts_sha256']=evidence
new['root_exact_canonical_identity_copy']={'copied_at_utc':datetime.now(timezone.utc).isoformat(),'original_final_offer':aliases[str(offer_path)],'original_pack':aliases[str(PACK)],'actual_pack_preparation':aliases['/tmp/applied27-current55-reviewed-offer-original-byte-pack-actual-v1.json'],'root_copy_helper':ref(Path(__file__)),'candidate_bytes_and_promotions_bytes_unchanged':True,'new_proof_sources':0,'owner_installation_claimed':False}
new['scope']='Exact Root byte copies and active path aliases of the independently reviewed current55 identity-only offer. All128 exercise and1954 material bodies, old mathematical decisions and times, and312 unpruned proof metadata remain unchanged; no installed owner, new proof, selection, aggregate or publication claim.'
path=BASE/'applied27-current55-identity-offer-canonical-v1.json'
with path.open('x') as f:f.write(json.dumps(new,ensure_ascii=False,indent=2)+'\n')
assert sha(checked(new['candidate']))==old['mapped_ledger_sha256']
assert sha(checked(new['candidate_promotions']))==old['mapped_promotions_sha256']
for n,h in held.items():assert sha(ROOT/n)==h
assert sha(ROOT/'book/coverage/inventory.json')==INV_SHA
print(json.dumps({'status':'passed_exact_isolated_applied27_root_identity_copy','offer':ref(path),'candidate':new['candidate'],'promotions':new['candidate_promotions'],'original_alias_count':len(aliases),'new_proof_sources':0,'installed_owner_write':False}))

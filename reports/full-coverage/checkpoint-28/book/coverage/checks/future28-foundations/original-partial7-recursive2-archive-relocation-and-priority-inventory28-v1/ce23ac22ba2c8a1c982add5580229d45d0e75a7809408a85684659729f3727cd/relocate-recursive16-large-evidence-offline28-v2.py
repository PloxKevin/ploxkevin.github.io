from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,shutil
ROOT=Path('/home/oxrexkevin/SafetyBased')
OLD=ROOT/'book/coverage/checks/future28-foundations/original-recursive16-new2-large-review-raw-bytes28-v1'
NEW=Path('/tmp/mpc-recursive16-new2-original-raw-shards-offline28-v1')
COMPACT=ROOT/'book/coverage/checks/future28-foundations/mpc-recursive16-new2-independent-foundations28-byte-binding-v1.json'
ORIGINAL_COMPACT=Path('/tmp/mpc-recursive16-new2-independent-foundations28-byte-binding-v1.json')
OUTPUT=ROOT/'book/coverage/checks/future28-foundations/mpc-recursive16-new2-independent-foundations28-byte-binding-v2.json'
assert OLD.is_dir()and not NEW.exists()and COMPACT.is_file()and not ORIGINAL_COMPACT.exists()and not OUTPUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def encode(j):return (json.dumps(j,indent=2)+'\n').encode()
before={str(p.relative_to(OLD)):sha(p)for p in OLD.rglob('*')if p.is_file()}
oldcatalog=OLD/'exact-original-raw-byte-shards-v1.json';original=json.loads(oldcatalog.read_bytes())
oldcompactsha=sha(COMPACT);compact=json.loads(COMPACT.read_bytes())
shutil.copytree(OLD,NEW)
for n,h in before.items():assert sha(NEW/n)==h,n
shutil.copyfile(COMPACT,ORIGINAL_COMPACT)
assert sha(ORIGINAL_COMPACT)==oldcompactsha
shutil.rmtree(OLD);COMPACT.unlink()
assert sha(ORIGINAL_COMPACT)==oldcompactsha
for n,h in before.items():assert sha(NEW/n)==h,n
updated=copy.deepcopy(original)
for body in updated['original_files'].values():
    digest=hashlib.sha256();offset=0
    for part in body['concatenate_parts_in_list_order_without_changes']:
        oldp=ROOT/part['file'];newp=NEW/oldp.relative_to(OLD)
        assert sha(newp)==part['sha256']and newp.stat().st_size==part['bytes']and offset==part['offset']
        part['file']=str(newp);digest.update(newp.read_bytes());offset+=part['bytes']
    assert digest.hexdigest()==body['original_sha256']==body['exact_reconstruction_sha256']and offset==body['original_bytes']
updated['offline_relocation']={'relocated_at_utc':datetime.now(timezone.utc).isoformat(),'original_catalog_exact_bytes':{'file':str(NEW/oldcatalog.name),'sha256':before[oldcatalog.name]},'original_archive_root':str(OLD),'offline_root':str(NEW),'all_original_part_bytes_unchanged':True,'website_publication_of_large_raw_payloads_claimed':False}
offlinecatalog=NEW/'exact-original-offline-raw-byte-shards-v2.json'
with offlinecatalog.open('xb')as f:f.write(encode(updated))
binding=copy.deepcopy(compact)
binding['original_large_review_exact_raw_byte_storage']['ordered_original_raw_byte_shards']={'file':str(offlinecatalog),'sha256':sha(offlinecatalog)}
binding['canonical_byte_binding']['offline_relocation']={'relocated_at_utc':updated['offline_relocation']['relocated_at_utc'],'entire_original_compact_binding_bytes':{'file':str(ORIGINAL_COMPACT),'sha256':oldcompactsha},'large_raw_piece_website_paths_removed':True,'original_large_peer_and_findings_unchanged_TMP':True,'new_mathematical_review_or_execution_claimed':False,'entire_original_failed_cross_device_relocation_body_and_time':json.loads(Path('/tmp/recursive16-large-evidence-offline-relocation28-actual-v1.json').read_text()),'original_failed_cross_device_relocation_raw_log':{'file':'/tmp/recursive16-large-evidence-offline-relocation28-actual-v1.log','sha256':sha(Path('/tmp/recursive16-large-evidence-offline-relocation28-actual-v1.log'))}}
with OUTPUT.open('xb')as f:f.write(encode(binding))
for k in ('status','errors','reviewer','reviewed_at_utc','completed_at_utc','component_decisions','source','entire_source','entire_new2_reviewed_bodies','whole_exercise18_approved','whole_material_units_approved'):assert binding[k]==compact[k]
print(json.dumps({'compact_current_binding':{'file':str(OUTPUT.relative_to(ROOT)),'sha256':sha(OUTPUT)},'offline_raw_shard_catalog':{'file':str(offlinecatalog),'sha256':sha(offlinecatalog)},'entire_original_compact_binding':{'file':str(ORIGINAL_COMPACT),'sha256':sha(ORIGINAL_COMPACT)},'raw_piece_count':len(before)-1,'all_original_raw_piece_bytes_unchanged':True,'large_raw_payload_bytes_added_to_website':0}))

"""Preserve an unintended timestamp-only parser regeneration and restore approved55 bytes."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
ROOT=Path(__file__).resolve().parents[3]
current=ROOT/'book/coverage/inventory.json';approved=ROOT/'book/coverage/inventory-after-correction55.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(current)=='c235b64161f635dd2f2170424cd38b7ed8bad32088426fa42f85e9e76b64da14'
assert sha(approved)=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
before=current.read_bytes();a=json.loads(before);b=json.loads(approved.read_bytes())
diffs=[k for k in set(a)|set(b) if a.get(k)!=b.get(k)];assert diffs==['generated_at_utc']
assert len(a['exercises'])==556 and len(a['material_source_units'])==12774
for n,h in a['source_sha256'].items():assert sha(ROOT/n)==h
archive=ROOT/'reports/full-coverage/working-inventory55-timestamp-regeneration-before-restoration28-v1.json'
result=ROOT/'reports/full-coverage/approved-inventory55-exact-byte-restoration28-v1.json'
assert not archive.exists() and not result.exists()
with archive.open('xb') as f:f.write(before)
assert sha(current)==sha(archive)
current.write_bytes(approved.read_bytes());assert sha(current)==sha(approved)
record={'status':'passed_timestamp_only_unintended_parser_regeneration_preserved_approved55_exact_bytes_restored','restored_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':sha(Path(__file__)),'original_regeneration':{'file':archive.relative_to(ROOT).as_posix(),'sha256':sha(archive)},'restored_inventory':{'file':'book/coverage/inventory.json','sha256':sha(current)},'approved_original':{'file':'book/coverage/inventory-after-correction55.json','sha256':sha(approved)},'only_changed_field':'generated_at_utc','regenerated_timestamp':a['generated_at_utc'],'approved_original_timestamp':b['generated_at_utc'],'all_source_fingerprints_and_556_exercise_12774_material_records_equal':True,'new_mathematical_or_compiler_coverage_claimed':False}
with result.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))

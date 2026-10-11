from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased');OLD=Path('/tmp/modules-conformal45-canonical-byte-history27-v1/conformal45-original-source-and-history-preparation27-v1.json');PEER=Path('/tmp/modules-conformal45-source55-independent-foundations-full-whole-review27-v1.json');BASE=Path('/tmp/modules-conformal45-canonical-byte-history27-v2');OUT=BASE/'conformal45-reviewed-source-and-history-preparation27-v2.json';assert not BASE.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
assert sha(OLD)=='762584a3a757e2498f8e9a40bd45f10953de9f61b785b2c7bc13a4fff52ffcdd';assert sha(PEER)=='554fcbf844cbb8ef0f79e2df86cc0a09a42e009e94408f416cdf61666dc5d3f5'
old=json.loads(OLD.read_text());peer=json.loads(PEER.read_text());assert peer['errors']==[] and peer['public_theorem_count']==45 and peer['source55_virtual_exercise']['whole_exercise_approved'] is True and peer['source55_virtual_exercise']['missing_clauses']==[]
assert len(peer['material_units'])==5 and all(r['whole_unit_approved'] is True and r['missing_clauses']==[] for r in peer['material_units'])
history={n:r['sha256'] for n,r in old['original_closed_byte_aliases'].items()}
for n,h in peer['closed_evidence_sha256'].items():assert n not in history or history[n]==h;history[n]=h
for p in [OLD,PEER,Path('/tmp/check-modules-conformal45-source55-independent-foundations-v1.py'),Path('/tmp/run-modules-conformal45-source55-independent-foundations-v1.py'),Path('/tmp/modules-conformal45-source55-independent-foundations-actual-v1.json'),Path('/tmp/modules-conformal45-source55-independent-foundations-actual-v1.log'),Path(__file__)]:history[str(p)]=sha(p)
actual=json.loads(Path('/tmp/modules-conformal45-source55-independent-foundations-actual-v1.json').read_text());assert type(actual['actual_exit_code']) is int and actual['actual_exit_code']==0
plan={};aliases={}
for n,h in history.items():
 original=path(n)
 if n in old['original_closed_byte_aliases']:p=Path(old['original_closed_byte_aliases'][n]['file']);assert sha(p)==h
 else:p=original;assert p.is_file() and not p.is_symlink() and sha(p)==h,n
 target=BASE/('original-tmp' if original.parent==Path('/tmp') else 'original-root')/(original.name if original.parent==Path('/tmp') else original.relative_to(ROOT))
 assert target not in plan;plan[target]=p;aliases[n]={'file':str(target),'sha256':h}
BASE.mkdir(parents=True)
for target,p in plan.items():
 target.parent.mkdir(parents=True,exist_ok=True)
 with target.open('xb') as f:f.write(p.read_bytes())
 assert sha(target)==sha(p)
sources=[]
for row in old['sources']:
 p=Path(row['prospective_exact_byte_copy']['file']);target=BASE/p.name
 with target.open('xb') as f:f.write(p.read_bytes())
 assert sha(target)==row['original_source']['sha256'];sources.append({**row,'prospective_exact_byte_copy':{'file':str(target),'sha256':sha(target)}})
result={'status':'prepared_exact_tmp_reviewed_source45_and_closed_original_histories_no_canonical_execution','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_preparation_v1':{'file':str(OLD),'sha256':sha(OLD)},'entire_original_preparation_v1_body_and_time':old,'full_whole_virtual55_source_peer':{'file':str(PEER),'sha256':sha(PEER)},'entire_original_full_whole_peer_body_and_time':peer,'sources':sources,'source_count':3,'public_theorem_count':45,'fresh_virtual55_whole_exercises':1,'fresh_virtual55_whole_material_units':5,'original_closed_byte_aliases':aliases,'history_count':len(aliases),'scope':'TMP-only source45 preparation after genuine independent whole virtual55 review. Original current53 inventory/verification bytes use exact retained v1 copies. All original decisions/body/time/commands/failures preserved; no canonical build, current55 identity or owner mutation.'}
with OUT.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'prepared_tmp_only','packet':str(OUT),'sha256':sha(OUT),'sources':3,'public':45,'history':len(aliases)}))

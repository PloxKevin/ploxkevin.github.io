"""Archive the original closed118-label review without changing any live ledger."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/future26-core/box-labels'
PEER=Path('/tmp/root-core26-box-label-118-independent-applied-full-context-review-v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(PEER)=='c1d15307054f027da5f5ff25b7bec6d9703360e629947c452888d1cc20ded167'
peer=json.loads(PEER.read_text());assert 'passed' in peer['status'] and peer['errors']==[]
assert peer['individually_read_complete_labels']==118 and peer['whole_nonformal_labels_approved']==48 and peer['substantive_titles_retained_pending']==70
assert peer['proved_mathematical_units']==0 and peer['lean_declarations']==[]
assert sha(ROOT/'book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
assert sha(ROOT/'book/coverage/core.json')==peer['original_core24_sha256']=='47b676890af40692cc1161c5472b461397b224e1a3724ee6990f03bb64d56bf5'
owner_names=['core','foundations','applied','modules','applied-promotions']
held={f'book/coverage/{n}.json':sha(ROOT/f'book/coverage/{n}.json') for n in owner_names}
inputs={str(PEER):sha(PEER),**peer['closed_evidence_sha256']}
assert len(inputs)==9 and len({Path(n).name for n in inputs})==9
out=BASE/'closed-original-byte-aliases-v1.json';assert not out.exists()
for n,d in inputs.items():
 p=Path(n);assert p.is_absolute() and p.parent==Path('/tmp') and p.is_file() and not p.is_symlink() and sha(p)==d
 assert not (BASE/'original-tmp'/p.name).exists()
actual=json.loads(Path(peer['actual_read_only_checker']['file']).read_text())
assert actual['actual_exit_code']==0 and sha(Path(actual['raw_log']))==actual['raw_log_sha256']
assert actual['helper_sha256_before']==actual['helper_sha256_after']==sha(Path(actual['actual_command'][1]))
rows=[]
for n,d in sorted(inputs.items()):
 p=Path(n);q=BASE/'original-tmp'/p.name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);assert sha(q)==d
 rows.append({'original_absolute_path':n,'canonical_file':q.relative_to(ROOT).as_posix(),'sha256':d})
assert all(sha(ROOT/n)==d for n,d in held.items())
record={'status':'closed_original_full118_label_review_archived_byte_identically_without_live_owner_changes',
 'archived_at_utc':datetime.now(timezone.utc).isoformat(),
 'original_review':{'file':str(PEER),'sha256':sha(PEER),'original_review_time':peer['reviewed_at_utc']},
 'original_absolute_path_byte_aliases':rows,'unchanged_live_owner_sha256':held,
 'scope':'Original48 whole label-only nonformal decisions and70 substantive pending labels remain unchanged. No exercise, mathematical theorem, source or live ledger is promoted.'}
with out.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'passed','originals':len(rows),'whole_nonformal_labels':48,'substantive_pending':70,'live_owners_unchanged':True}))

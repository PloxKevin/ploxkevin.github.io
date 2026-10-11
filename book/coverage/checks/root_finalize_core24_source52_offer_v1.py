"""Append the completed independent source52 identity peer to a new offer."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

ROOT=Path(__file__).resolve().parents[3]
OLD='book/coverage/checks/future24-core/source52/core-audit24-candidate-source52-material-additions-v2.json'
NEW='book/coverage/checks/future24-core/source52/core-audit24-candidate-source52-material-additions-v2-reviewed.json'
PEER='book/coverage/checks/future24-core/source52-independent-owner-identity-peer/core24-source52-identity-independent-modules-confirmation-v1.json'
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
old=read(OLD);peer=read(PEER)
assert sha(OLD)=='312ccfb3e2c233fc19bdc7d30e00eed986619282711d4325c2bcab56f4d6e469'
assert sha(PEER)=='3d8b341542d43a8fe5e06f998548e5bc01c92ae5f78d078accb7eb5c764ae72b'
assert peer['status']=='independent_exact_inventory_identity_rebase_confirmation_passed' and peer['errors']==[]
assert peer['source52_offer']==ref(OLD) and peer['source52_candidate']==old['candidate_ledger']
assert read(peer['actual_independent_checker_execution']['file'])['actual_exit_code']==0
assert old['final_independent_source52_identity_peer_pending'] is True
for n,s in old['source_sha256'].items():assert sha(n)==s
new=copy.deepcopy(old)
new['final_independent_source52_identity_peer_pending']=False
added={'final_independent_source52_identity_peer':ref(PEER),
    'entire_original_source52_identity_peer_body_and_time':peer,
    'original_source52_offer_before_final_peer':ref(OLD),
    'source52_final_peer_added_at_utc':datetime.now(timezone.utc).isoformat(),
    'source52_finalization_helper':ref(str(Path(__file__).relative_to(ROOT)))}
assert not set(added)&set(old);new.update(added)
inverse=copy.deepcopy(new)
for k in added:inverse.pop(k)
inverse['final_independent_source52_identity_peer_pending']=True
assert inverse==old
with (ROOT/NEW).open('x') as f:f.write(json.dumps(new,indent=2)+'\n')
print(json.dumps({'status':'passed_new_source52_reviewed_core_offer','offer':ref(NEW),'candidate':new['candidate_ledger'],'peer':ref(PEER)}))

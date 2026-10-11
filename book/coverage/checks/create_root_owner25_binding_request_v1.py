"""Pin the reviewed owner25 input template and the actually completed24 delivery."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
ROOT=Path(__file__).resolve().parents[3]
OUT='book/coverage/checks/root-owner25-binding-preparation-inputs-v1.json'
CAT='book/coverage/checks/future25-core/closed-checkpoint24-delivery-originals-v1/closed-original-byte-aliases-v1.json'
OBS='book/coverage/checks/future25-core/checkpoint25-native-final-owner-binding-request-observation-v1.json'
PEER='book/coverage/checks/future25-core/owner25-integration-and-binding-helpers-independent-foundations-code-review-v1.json'
HELPER='book/coverage/checks/prepare_root_owner25_bindings_v2.py'
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
assert not (ROOT/OUT).exists()
assert sha(CAT)=='bb5037892e16c06ae7ee8f7e43f98e675531004d70c0bd1c3d72beb9de716959'
catalog=read(CAT);assert catalog['status']=='completed_checkpoint24_actual_content_and_metadata_delivery_original_bytes_closed'
assert catalog['both_actual_pages_runs_and_all31_live_assets_passed'] is True
assert sha(PEER)=='a01c88f5f7b9b3aac425e00f1a51be4ece8455d9388fa4c4a0fccc37d018e4b2'
peer=read(PEER);assert 'passed' in peer['status'] and peer['errors']==[]
assert peer['helpers_sha256'][HELPER]==sha(HELPER)
config=copy.deepcopy(read(OBS)['production_binding_input_template_without_independent_helper_peer'])
config['preparation_helper']=ref(HELPER);config['independent_integration_helper_review']=ref(PEER)
extras={r['file']:r['sha256'] for r in config['extra_closed_evidence']['core']}
for row in catalog['aliases']:
 r=row['immutable_original_byte_copy'];assert sha(r['file'])==r['sha256'];extras[r['file']]=r['sha256']
r=catalog['original_absolute_recorder_byte_alias'];assert sha(r['canonical_file'])==r['sha256'];extras[r['canonical_file']]=r['sha256']
for n in [CAT,OBS,PEER,str(Path(__file__).relative_to(ROOT)),
 'book/coverage/checks/close_root_checkpoint24_delivery_originals_v1.py',
 'reports/full-coverage/close-checkpoint24-delivery-originals-execution-v1.json','reports/full-coverage/close-checkpoint24-delivery-originals-execution-v1.log',
 'reports/full-coverage/root-core25-canonical-pair-execution-v1.json','reports/full-coverage/root-core25-canonical-pair-execution-v1.log',
 'reports/full-coverage/root-core25-offer-finalization-execution-v1.json','reports/full-coverage/root-core25-offer-finalization-execution-v1.log',
 'book/coverage/checks/future25-core/checkpoint25-selector-retainer-independent-applied-review-v2.json',
 'book/coverage/checks/future25-core/owner25-live-interface-helper-independent-foundations-final-code-review-v1.json']:
 extras[n]=sha(n)
for n,h in peer['closed_evidence_sha256'].items():assert sha(n)==h;extras[n]=h
config['extra_closed_evidence']['core']=[{'file':n,'sha256':h} for n,h in sorted(extras.items())]
config['root_requested_at_utc']=datetime.now(timezone.utc).isoformat()
config['actual_completed24_delivery_originals']=ref(CAT)
for rows in config['extra_closed_evidence'].values():
 for row in rows:assert sha(row['file'])==row['sha256']
for row in config['offers'].values():assert sha(row['file'])==row['sha256']
with (ROOT/OUT).open('x') as f:f.write(json.dumps(config,indent=2)+'\n')
print(json.dumps({'status':'passed_pinned_root25_binding_request','input':ref(OUT),'owners':4,'extra_core_closed_artifacts':len(extras),'actual24_delivery_complete':True,'live_owner_written':False}))

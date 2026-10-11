"""Bind the real isolated candidate to its unchanged reviews and compiler records."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations
BASE='book/coverage/checks/future24-core'
CANDIDATE=BASE+'/core24-source51-material-candidate-v1.json'
PEER=BASE+'/core24-material-candidate-independent-applied-confirmation-v1.json'
READY=BASE+'/barrier-intro/root-barrier-intro24-canonical-readiness-v1.json'
SOURCE='verification/lean/SafeLearning/CompleteBarrierIntroMaterial24.lean'
OUT=BASE+'/core-audit24-candidate-source51-material-additions-v1-reviewed.json'
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
assert not (ROOT/OUT).exists()
manifest=read('reports/full-coverage/checkpoint-23-manifest.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert len(manifest['proof_files'])==1131
assert sha('book/coverage/core.json')=='1358c11b912820b5fd07d8742ebe04e9b3c371b1e4c80d462641876f00c0d39a'
inventory=read('book/coverage/inventory.json')
assert sha('book/coverage/inventory.json')=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
candidate=read(CANDIDATE);ready=read(READY);peer=read(PEER)
assert sha(PEER)=='4925212eef39f69a3b166925931cfb176313622c9fc164bce25d2428cfbb46e7'
assert peer['status']=='passed_independent_isolated_core24_candidate_mechanics' and peer['errors']==[]
assert peer['candidate']==ref(CANDIDATE) and peer['reviewer']=='/root/applied_next'
assert candidate['exercises']==read('book/coverage/core.json')['exercises']
builder='reports/full-coverage/root-core24-material-candidate-execution-v1.json'
execution=read(builder)
assert execution['actual_exit_code']==0 and sha(execution['log'])==execution['log_sha256']
names=declarations((ROOT/SOURCE).read_text())
assert len([n for n in names if n['kind']=='theorem'])==4
required={str(p.relative_to(ROOT)):sha(str(p.relative_to(ROOT))) for p in (ROOT/BASE).rglob('*')
          if p.is_file() and p.suffix in {'.py','.json','.log','.lean'} and '__pycache__' not in p.parts}
for n in [builder,execution['log'],'reports/full-coverage/root-barrier-intro24-canonical-pair-execution-v1.json',
          'reports/full-coverage/root-barrier-intro24-canonical-pair-execution-v1.log',
          'book/coverage/checks/prepare_root_core24_material_candidate_v1.py',
          'book/coverage/checks/run_root_barrier_intro24_canonical_pair_v1.py',
          'book/coverage/checks/finalize_root_core24_material_offer_v1.py']:
    required[n]=sha(n)
for pair in ready['actual_canonical_pair']:
    row=read(pair['file'])
    assert row['exit_code']==0 and sha(pair['file'])==pair['sha256']
    assert sha(row['log'])==row['log_sha256']
    required[pair['file']]=sha(pair['file']);required[row['log']]=sha(row['log'])
proof={'sha256':sha(SOURCE),'evidence_scope':'Actual standalone and named builds, independently reviewed whole scalar barrier example. Kernel replay and axiom audit remain future24 requirements.',
       'declarations':names,'actual_pairs':ready['actual_canonical_pair'],
       'independent_whole_source_review':candidate['future24_material_candidate_binding']['whole_source_reviews'][0],
       'evidence_sha256':required}
offer={'status':'candidate_only_independently_reviewed_future24_material_additions_unselected_unpublished',
       'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'checkpoint':24,
       'base_verified_checkpoint':23,'candidate_ledger':ref(CANDIDATE),
       'inventory':'book/coverage/inventory.json','inventory_sha256':sha('book/coverage/inventory.json'),
       'source_sha256':inventory['source_sha256'],'proof_files':{SOURCE:proof},
       'actual_builder':ref(builder),'final_independent_candidate_peer':ref(PEER),
       'whole_source_reviews':candidate['future24_material_candidate_binding']['whole_source_reviews'],
       'required_evidence_artifacts_sha256':required,'new_public_theorems':4,
       'whole_material_units':10,'proved_whole_units':1,'study_guidance_whole_units':9,
       'exercise_counts_unchanged':{'complete_math':88,'partial':4},
       'scope':'Exact current51 literals, ten separately approved whole-unit decisions and real compiler pairs. All original review bodies/times and prior pending rows remain preserved. No live owner, source, frozen23 input or publication change.',
       'coverage_complete':False}
(ROOT/OUT).write_text(json.dumps(offer,indent=2,ensure_ascii=False)+'\n')
assert sha('book/coverage/core.json')=='1358c11b912820b5fd07d8742ebe04e9b3c371b1e4c80d462641876f00c0d39a'
print(json.dumps({'status':'prepared_unselected','offer':ref(OUT),'new_public_theorems':4,'whole_material_units':10}))

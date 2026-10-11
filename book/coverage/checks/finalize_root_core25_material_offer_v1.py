"""Bind the real isolated candidate to its unchanged reviews and compiler records."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations
BASE='book/coverage/checks/future25-core'
CANDIDATE=BASE+'/core25-source52-material-candidate-v1.json'
PEER=BASE+'/core25-material-candidate-independent-applied-confirmation-v1.json'
READY=BASE+'/barrier-control/root-barrier-control25-canonical-readiness-v1.json'
SOURCE='verification/lean/SafeLearning/CompleteBarrierControlMaterial25.lean'
OUT=BASE+'/core-audit25-candidate-source52-material-additions-v1-reviewed.json'
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
assert not (ROOT/OUT).exists()
manifest=read('reports/full-coverage/checkpoint-24-manifest.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert len(manifest['proof_files'])==1144
assert sha('book/coverage/core.json')=='47b676890af40692cc1161c5472b461397b224e1a3724ee6990f03bb64d56bf5'
inventory=read('book/coverage/inventory.json')
assert sha('book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
candidate=read(CANDIDATE);ready=read(READY);peer=read(PEER)
assert len(sys.argv)==2 and len(sys.argv[1])==64
assert sha(PEER)==sys.argv[1]
assert peer['status']=='passed_independent_isolated_core25_candidate_mechanics' and peer['errors']==[]
assert peer['candidate']==ref(CANDIDATE) and peer['reviewer']=='/root/applied_next'
assert candidate['exercises']==read('book/coverage/core.json')['exercises']
builder='reports/full-coverage/root-core25-candidate-preparation-execution-v1.json'
execution=read(builder)
assert execution['actual_exit_code']==0 and sha(execution['log'])==execution['log_sha256']
names=declarations((ROOT/SOURCE).read_text())
assert len([n for n in names if n['kind']=='theorem'])==7
required={str(p.relative_to(ROOT)):sha(str(p.relative_to(ROOT))) for p in (ROOT/BASE).rglob('*')
          if p.is_file() and p.suffix in {'.py','.json','.log','.lean'} and '__pycache__' not in p.parts}
for n in [builder,execution['log'],'reports/full-coverage/root-core25-canonical-pair-execution-v1.json',
          'reports/full-coverage/root-core25-canonical-pair-execution-v1.log',
          'book/coverage/checks/prepare_root_core25_material_candidate_v1.py',
          'book/coverage/checks/run_root_barrier_control25_canonical_pair_v1.py',
          'book/coverage/checks/finalize_root_core25_material_offer_v1.py']:
    required[n]=sha(n)
for pair in ready['actual_canonical_pair']:
    row=read(pair['file'])
    assert row['exit_code']==0 and sha(pair['file'])==pair['sha256']
    assert sha(row['log'])==row['log_sha256']
    required[pair['file']]=sha(pair['file']);required[row['log']]=sha(row['log'])
proof={'sha256':sha(SOURCE),'evidence_scope':'Actual standalone and named builds, independently reviewed whole control-affine calculus units. Kernel replay and axiom audit remain future25 requirements.',
       'declarations':names,'actual_pairs':ready['actual_canonical_pair'],
       'independent_whole_source_review':candidate['future25_material_candidate_binding']['whole_source_reviews'][0],
       'evidence_sha256':required}
offer={'status':'candidate_only_independently_reviewed_future25_material_additions_unselected_unpublished',
       'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'checkpoint':25,
       'base_verified_checkpoint':24,'candidate_ledger':ref(CANDIDATE),
       'inventory':'book/coverage/inventory.json','inventory_sha256':sha('book/coverage/inventory.json'),
       'source_sha256':inventory['source_sha256'],'proof_files':{SOURCE:proof},
       'actual_builder':ref(builder),'final_independent_candidate_peer':ref(PEER),
       'whole_source_reviews':candidate['future25_material_candidate_binding']['whole_source_reviews'],
       'required_evidence_artifacts_sha256':required,'new_public_theorems':7,
       'whole_material_units':7,'proved_whole_units':2,'study_guidance_whole_units':5,
       'exercise_counts_unchanged':{'complete_math':88,'partial':4},
       'scope':'Exact current52 literals, seven separately approved whole-unit decisions and real compiler pairs. All original review bodies/times and prior pending rows remain preserved. No live owner, source, frozen24 input or publication change.',
       'coverage_complete':False}
(ROOT/OUT).write_text(json.dumps(offer,indent=2,ensure_ascii=False)+'\n')
assert sha('book/coverage/core.json')=='47b676890af40692cc1161c5472b461397b224e1a3724ee6990f03bb64d56bf5'
print(json.dumps({'status':'prepared_unselected','offer':ref(OUT),'new_public_theorems':7,'whole_material_units':7}))

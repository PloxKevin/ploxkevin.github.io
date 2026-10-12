"""Close real fixed-selector experiments and request complete source review."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json
ROOT=Path(__file__).resolve().parents[3]
DEST=ROOT/'book/coverage/checks/future29-core/monitoring-fixed-selector29-v1'
SOURCE=Path('/tmp/CompleteCoreMonitoringFixedSelector29-draft-v6.lean')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
assert not DEST.exists()
originals={};copies={}
paths=[Path(__file__),SOURCE,Path('/tmp/root_tmp_lean_current64_owner28_runner_v1.py'),Path('/tmp/root_tmp_lean_current64_owner28_context_v1.json')]
for i,expected in enumerate([1,1,0,1,0,0],1):
    p=Path(f'/tmp/root-core-monitoring-fixed-selector29-trial{i}.json');d=json.loads(p.read_bytes())
    assert d['actual_exit_code']==d['actual_runner_exit_code']==expected and d['protection_errors']==[]
    assert d['source_sha256_before']==d['source_sha256_after']==d['source_snapshot_sha256']
    assert sha(Path(d['source']))==sha(Path(d['source_snapshot']))==d['source_sha256_before']
    assert sha(Path(d['raw_log']))==d['raw_log_sha256']
    paths.extend([p,Path(d['source']),Path(d['source_snapshot']),Path(d['raw_log'])])
for p in dict.fromkeys(paths):
    h=sha(p);target=DEST/'original-closed-bytes'/h/p.name
    copies[target]=p;originals[str(p)]={'file':target.relative_to(ROOT).as_posix(),'sha256':h}
spec=importlib.util.spec_from_file_location('monitoring29_names',ROOT/'book/coverage/lean_names.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
declarations=names.declarations(SOURCE.read_text());assert len(declarations)==29 and sum(r['kind'] in ['theorem','lemma'] for r in declarations)==16
core=json.loads((ROOT/'book/coverage/core.json').read_bytes())
exercise=[r for r in core['exercises'] if r['inventory_key']=='cmdp.html::exercise-21'];assert len(exercise)==1 and exercise[0]['status']=='partial'
material=[r for r in core['material_claims'] if r['source_unit_keys']==['cmdp.html::node-1141']]
assert material and any(r['status']=='pending' for r in material)
for target,p in copies.items():
    target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('xb') as f:f.write(p.read_bytes())
    assert sha(target)==sha(p)
request={'status':'full_genuine_fixed_price_monitoring_selector29_semantic_review_request','prepared_at_utc':datetime.now(timezone.utc).isoformat(),
 'final_actual_source':originals[str(SOURCE)],'source_level_public_declarations':declarations,
 'original_actual_trial':originals['/tmp/root-core-monitoring-fixed-selector29-trial6.json'],
 'original_TMP_receipts_sources_snapshots_raw_logs_and_context':originals,
 'whole_exercise21_literal_and_current_all_claims':exercise[0],'entire_node1141_current_all_claims':material,
 'source_literal':ref(ROOT/'reports/full-coverage/checkpoint-28/SafeLearning/cmdp.html'),
 'source64_inventory':ref(ROOT/'book/coverage/inventory-after-correction64.json'),
 'original_owner28_source60':ref(ROOT/'reports/full-coverage/source-history/approved-corrections61-64-20261011/source60-owner28-original/book/coverage/core.json'),
 'actual_source61_to64_application':ref(ROOT/'reports/full-coverage/source61-64-corrections-application-v1.json'),
 'correspondence_requested':'Exact fixed-price stationary selector in Exercise8.6(c), for every real pair of prices and each R0/R1/R2 initial state. The primitive model changes only its initial point mass and retains the original controlled transition. The stationary action rule follows the literal ties above1/at1. The genuine controlled law follows its actual deterministic orbit almost surely. The orbit reaches period1or2 after two transient steps; a directly derived bounded telescoping potential proves all-horizon 3/T error and almost-sure and actual expected fractions. The resulting fractions are an IsMaximizer on the entire achievable polytope for every price and initial state, including both price ties and threshold equality. No periodicity, limiting fractions, maximality or controlled-law outcome is supplied as a primitive assumption.',
 'whole_exercise21_or_node1141_approval_requested':False,
 'remaining_gaps':['Generic Section7 stochastic feasibility and expected near-optimality under exact-maximizer A1–A3 remain pending.','No finite epoch estimate is assumed unbiased merely from long-run maximization.','Prior genuine projected-dual cycle, full face classification, arbitrary history policies and augmentation comparisons remain separate immutable selected proofs.'],
 'canonical_installation_selection_aggregate_owner_or_publication_claimed':False,'coverage_complete':False}
p=DEST/'core-monitoring-fixed-selector29-full-semantic-review-request-v1.json'
with p.open('xb') as f:f.write((json.dumps(request,indent=2)+'\n').encode())
print(json.dumps({'request':ref(p),'public_names':29,'theorem_lemma_count':16,'genuine_trial_statuses':[1,1,0,1,0,0],'coverage_complete':False}))

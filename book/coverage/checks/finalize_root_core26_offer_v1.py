"""Package the exact isolated Core26 candidate after its independent mapping peer."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json
ROOT=Path(__file__).resolve().parents[3]
BASE='book/coverage/checks/future26-core/composed-source53-v3'
CANDIDATE=BASE+'/core26-source53-composed-candidate-v1.json'
CANDIDATE_SHA='1aeba23aee0fab8a64df0070928ef18bbfc708d32655ce16862b446862d62c38'
OUT=BASE+'/core-audit26-candidate-source53-additions-v1-reviewed.json'
BUILDER='book/coverage/checks/prepare_root_core26_composed_candidate_source53_v3.py'
BUILDER_SHA='62516dd993ca5978d6a953e45ee4f292f2b2cdeee842b4b748a338dc1b9ce226'
ACTUAL='reports/full-coverage/root-core26-composed-candidate-execution-v2.json'
def safe(n):
    assert isinstance(n,str) and n
    p=Path(n);assert not p.is_absolute() and '..' not in p.parts and str(p)==n
    assert (ROOT/p).resolve().is_relative_to(ROOT.resolve())
    return ROOT/p
def sha(n):return hashlib.sha256(safe(n).read_bytes()).hexdigest()
def read(n):return json.loads(safe(n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
def checked(r):assert sha(r['file'])==r['sha256'];return read(r['file'])
def zero(d):
    values=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
    assert values and all(type(v) is int and v==0 for v in values)
def collect(v,out):
    if isinstance(v,dict):
        if isinstance(v.get('file'),str) and isinstance(v.get('sha256'),str) and not Path(v['file']).is_absolute():
            n,h=v['file'],v['sha256'];assert sha(n)==h,n
            assert n not in out or out[n]==h;out[n]=h
        for x in v.values():collect(x,out)
    elif isinstance(v,list):
        for x in v:collect(x,out)
args=argparse.ArgumentParser();args.add_argument('--peer',required=True);args.add_argument('--peer-sha256',required=True);a=args.parse_args()
assert not safe(OUT).exists()
assert sha(CANDIDATE)==CANDIDATE_SHA and sha(BUILDER)==BUILDER_SHA
assert sha(a.peer)==a.peer_sha256
peer=read(a.peer);assert 'passed' in peer['status'] and peer.get('errors',[])==[]
assert peer['candidate']==ref(CANDIDATE)
candidate=read(CANDIDATE);binding=candidate['future26_composed_candidate_binding']
actual=read(ACTUAL);zero(actual)
assert actual['actual_command']==['python3',BUILDER] and actual['actual_workdir']==str(ROOT)
assert actual['helper_sha256_before']==actual['helper_sha256_after']=={BUILDER:BUILDER_SHA}
assert sha(actual['log'])==actual['log_sha256']
assert candidate['current_inventory_sha256']==sha('book/coverage/inventory.json')=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
assert binding['entire_original_current53_whole_exercise_review_body_and_time']['whole_exercise_approved'] is True
assert next(e for e in candidate['exercises'] if e['inventory_key']=='lyapunov-mpc.html::exercise-18')['status']=='partial'
assert next(e for e in candidate['exercises'] if e['inventory_key']=='lyapunov-mpc.html::exercise-19')['status']=='complete_math'
extra={};collect(binding,extra)
# Close both actual candidate executions, including the retained genuine failure.
archive=ROOT/BASE/'original-root-candidate-executions';assert not archive.exists();archive.mkdir()
for n in [ACTUAL,actual['log'],'reports/full-coverage/root-core26-composed-candidate-execution-v1.json','reports/full-coverage/root-core26-composed-candidate-execution-v1.log']:
    h=sha(n);target=archive/(h+Path(n).suffix)
    with target.open('xb') as f:f.write(safe(n).read_bytes())
    canonical=str(target.relative_to(ROOT));assert sha(canonical)==h;extra[canonical]=h
extra.update({CANDIDATE:CANDIDATE_SHA,BUILDER:BUILDER_SHA,a.peer:a.peer_sha256})
proofs={}
for row in binding['new_proof_sources']:
    source=row['source'];assert sha(source['file'])==source['sha256']
    readiness=checked(row['readiness']);evidence={};collect(readiness,evidence)
    collect(row,evidence)
    for r in row['pair']:
        record=r.get('record',r);d=checked(record);zero(d)
        assert d['source']==source['file'] and d['source_sha256_before']==d['source_sha256_after']==source['sha256']
        assert d['actual_workdir']==str(ROOT/'verification/lean')
        command=d.get('actual_command',d.get('command'))
        assert command in [['lake','env','lean',str(Path(source['file']).relative_to('verification/lean'))],['lake','build','SafeLearning.'+Path(source['file']).stem]]
        log=d.get('log',d.get('raw_log'));log_hash=d.get('log_sha256',d.get('raw_log_sha256'));assert sha(log)==log_hash
        evidence[log]=log_hash
    evidence[row['readiness']['file']]=row['readiness']['sha256']
    proofs[source['file']]={'sha256':source['sha256'],'evidence_sha256':evidence,'public_export_count':row['public_count']}
    extra.update(evidence)
assert len(proofs)==4 and sum(p['public_export_count'] for p in proofs.values())==48
inventory=read('book/coverage/inventory.json')
out={'schema_version':1,'status':'independently_reviewed_core26_candidate_source53_additions_ready_for_root_integration',
    'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'mapped_ledger':CANDIDATE,'mapped_ledger_sha256':CANDIDATE_SHA,
    'current_inventory':'book/coverage/inventory-after-correction53.json','current_inventory_sha256':candidate['current_inventory_sha256'],
    'source_sha256':inventory['source_sha256'],'proof_files':proofs,'new_proof_file_count':4,'new_theorem_or_lemma_count':48,
    'current_owner_builder':BUILDER,'current_owner_builder_sha256':BUILDER_SHA,
    'actual_builder_record':ACTUAL,'actual_builder_record_sha256':sha(ACTUAL),
    'actual_builder_raw_log':ref(actual['log']),'final_independent_candidate_mapping_peer':ref(a.peer),
    'whole_source_review':binding['whole_source_review'],'exact_candidate_binding':binding,
    'additional_frozen_inputs':extra,'coverage_complete':False,
    'scope':'Exact isolated reviewed candidate. Forty-eight nonformal labels, conditional MPC components and complete Exercise19; Exercise18 remains partial. No live installation, aggregate audit or publication inferred.'}
assert sha(CANDIDATE)==CANDIDATE_SHA and sha(BUILDER)==BUILDER_SHA
with safe(OUT).open('x') as f:f.write(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':'passed','offer':ref(OUT),'new_sources':4,'new_public_exports':48}))

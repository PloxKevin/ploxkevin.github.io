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
HISTORICAL_REF_ALIASES={
 ('verification/lean/.lake/packages/mathlib/Mathlib/Probability/CDF.lean','78586bddc289a171cbcb7fa155892333c4702c4f7f1185f9d6602ffac8b914e9'):'book/coverage/checks/future26-core/composed-source53-v3/original-primary-mathlib-context/CDF.lean',
 ('verification/lean/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean','e2da9c2a5d8874cf2397cc98c114d678fc648e74d62d96c58ed546bcacdaa6be'):'book/coverage/checks/future26-core/composed-source53-v3/original-primary-mathlib-context/Regular.lean',
 ('book/coverage/core.json','4e96c717055187cfc24e9e60a19a7d183499336570d99fbf9954ff199ff49572'):'book/coverage/checks/future26-core/closed-checkpoint25-delivery-originals-v1/original-root/book/coverage/core.json',
 ('book/coverage/inventory.json','38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'):'book/coverage/inventory-after-correction52.json',
 ('book/coverage/inventory.json','67c800179f90c6d152f5934be9187ad4c4b18275e6cd6678a2b2a2f7ff20ca99'):'book/coverage/inventory-after-correction49.json',
 ('SafeLearning/lyapunov-mpc.html','228e4e22eaa32ad287069001abe9507706ec0112ec2ed9e1d3cfb2d569c4be7c'):'reports/full-coverage/source-history/approved-mpc-scenario-scope-correction53-20261011/SafeLearning/lyapunov-mpc.html'}
historical_aliases={}
def collect(v,out):
    if isinstance(v,dict):
        if isinstance(v.get('file'),str) and isinstance(v.get('sha256'),str) and not Path(v['file']).is_absolute():
            n,h=v['file'],v['sha256']
            if (n,h) in HISTORICAL_REF_ALIASES:
                original=n;n=HISTORICAL_REF_ALIASES[(n,h)]
                historical_aliases[(original,h)]=n
            assert sha(n)==h,n
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
# Close both actual candidate executions, including the retained genuine failure.
archive=ROOT/BASE/'original-root-candidate-executions';assert not archive.exists();archive.mkdir()
for n in [ACTUAL,actual['log'],'reports/full-coverage/root-core26-composed-candidate-execution-v1.json','reports/full-coverage/root-core26-composed-candidate-execution-v1.log']:
    h=sha(n);target=archive/(h+Path(n).suffix)
    with target.open('xb') as f:f.write(safe(n).read_bytes())
    canonical=str(target.relative_to(ROOT));assert sha(canonical)==h;extra[canonical]=h
extra.update({CANDIDATE:CANDIDATE_SHA,BUILDER:BUILDER_SHA,a.peer:a.peer_sha256})
inventory=read('book/coverage/inventory.json')
out={'schema_version':1,'status':'independently_reviewed_core26_candidate_source53_additions_ready_for_root_integration',
    'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'mapped_ledger':CANDIDATE,'mapped_ledger_sha256':CANDIDATE_SHA,
    'current_inventory':'book/coverage/inventory-after-correction53.json','current_inventory_sha256':candidate['current_inventory_sha256'],
    'source_sha256':inventory['source_sha256'],'proof_files':proofs,'new_proof_file_count':4,'new_theorem_or_lemma_count':48,
    'current_owner_builder':BUILDER,'current_owner_builder_sha256':BUILDER_SHA,
    'actual_builder_record':ACTUAL,'actual_builder_record_sha256':sha(ACTUAL),
    'actual_builder_raw_log':ref(actual['log']),'final_independent_candidate_mapping_peer':ref(a.peer),
    'whole_source_review':binding['whole_source_review'],'exact_candidate_binding':binding,
    'additional_frozen_inputs':{n:h for n,h in extra.items() if n.startswith('book/coverage/') or n.startswith('reports/full-coverage/source-history/')},'historical_reference_path_aliases':[{'original':{'file':n,'sha256':h},'immutable_original_byte_copy':{'file':canonical,'sha256':h}} for (n,h),canonical in sorted(historical_aliases.items())],'coverage_complete':False,
    'scope':'Exact isolated reviewed candidate. Forty-eight nonformal labels, conditional MPC components and complete Exercise19; Exercise18 remains partial. No live installation, aggregate audit or publication inferred.'}
assert sha(CANDIDATE)==CANDIDATE_SHA and sha(BUILDER)==BUILDER_SHA
with safe(OUT).open('x') as f:f.write(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':'passed','offer':ref(OUT),'new_sources':4,'new_public_exports':48}))

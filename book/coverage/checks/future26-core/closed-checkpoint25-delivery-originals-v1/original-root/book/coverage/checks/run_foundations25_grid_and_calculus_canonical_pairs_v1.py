"""Genuine serial new future25 canonical compiler pairs; run only after slot release."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,time
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/foundations-future25/material-batch1'
INPUT=BASE/'two-source31-export-original-history-inputs-v1.json'
OUT=BASE/'two-source31-export-actual-canonical-readiness25-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
def write(p,d):
    with p.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
inputs=read(INPUT)
assert inputs['source_count']==2 and inputs['public_theorem_count']==31 and inputs['whole_mathematical_unit_count']==4
assert not OUT.exists()
def guard():
    r=inputs['baseline24_selection'];assert sha(ROOT/r['file'])==r['sha256']
    for n,d in {**inputs['protected_selected24_source_sha256'],**inputs['current52_asset_sha256'],**inputs['current24_owner_and_inventory_sha256']}.items():assert sha(ROOT/n)==d,n
    for n,d in {**inputs['protected_selected24_source_sha256'],**inputs['current52_asset_sha256']}.items():assert sha(ROOT/'reports/full-coverage/checkpoint-24'/n)==d,n
guard();groups=[]
for gr in inputs['groups']:
    p=ROOT/gr['file'];assert sha(p)==gr['sha256'];prep=read(p);group=p.parent
    canonical=ROOT/prep['canonical_source']['file'];snapshot=ROOT/prep['source_snapshot']['file']
    assert sha(canonical)==sha(snapshot)==prep['canonical_source']['sha256']
    assert canonical.relative_to(ROOT).as_posix() not in inputs['protected_selected24_source_sha256']
    for n,r in prep['all_original_TMP_byte_aliases'].items():assert sha(Path(n))==sha(ROOT/r['file'])==r['sha256'],n
    pairs=[]
    for mode,cmd in [('named-build',['lake','build',prep['module']]),('standalone',['lake','env','lean','SafeLearning/'+canonical.name])]:
        record=group/(canonical.stem+'-'+mode+'-actual-v1.json');log=record.with_suffix('.log')
        assert not record.exists() and not log.exists();guard()
        before=sha(canonical);started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
        with log.open('xb') as f:actual=subprocess.run(cmd,cwd=ROOT/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
        row={'kind':'actual_future25_source_exact_canonical_'+mode,'status':'passed' if actual.returncode==0 else 'failed',
             'source':canonical.relative_to(ROOT).as_posix(),'source_sha256_before':before,'source_sha256_after':sha(canonical),
             'source_unchanged':before==sha(canonical),'source_snapshot':snapshot.relative_to(ROOT).as_posix(),'source_snapshot_sha256':sha(snapshot),
             'actual_command':cmd,'actual_workdir':str(ROOT/'verification/lean'),'actual_exit_code':actual.returncode,
             'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,
             'log':log.relative_to(ROOT).as_posix(),'log_sha256':sha(log),
             'actual_pair_helper':Path(__file__).relative_to(ROOT).as_posix(),'actual_pair_helper_sha256':sha(Path(__file__)),
             'all1144_selected24_sources_and_frozen_copies_exact':True,
             'scope':'Genuine new unselected future25 canonical compiler command. Original semantic decisions and times retained; no current owner, source HTML, inventory, progress, frozen24 or selection24 amendment.'}
        write(record,row);pairs.append({'actual_record':ref(record),'raw_log':ref(log),'source_snapshot':ref(snapshot),'actual_exit_code':actual.returncode})
        assert before==sha(canonical)==prep['canonical_source']['sha256'];guard()
        print(json.dumps({'group':prep['group'],'mode':mode,'actual_exit_code':actual.returncode,'elapsed_seconds':row['elapsed_seconds']}),flush=True)
        if actual.returncode:raise SystemExit(actual.returncode)
    result={'status':'passed_actual_future25_source_exact_canonical_pair_original_full_semantics_and_times_retained',
            'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'group':prep['group'],
            'canonical_source':prep['canonical_source'],'canonical_source_snapshot':prep['source_snapshot'],
            'public_theorem_names':prep['public_theorem_names'],'public_theorem_count':prep['public_theorem_count'],
            'whole_material_unit_keys':prep['whole_material_unit_keys'],'actual_canonical_pair':pairs,
            'original_preparation':gr,'entire_original_preparation_body_and_time':prep,
            'original_TMP_request':prep['original_TMP_request'],'entire_original_TMP_request_body_and_time':prep['entire_original_TMP_request_body_and_time'],
            'original_full_semantic_peer':prep['original_full_semantic_peer'],'entire_original_full_semantic_peer_body_and_time':prep['entire_original_full_semantic_peer_body_and_time'],
            'all_original_TMP_byte_aliases':prep['all_original_TMP_byte_aliases'],'actual_helper':ref(Path(__file__)),
            'all1144_selected24_sources_and_frozen_copies_exact':True,'all31_current52_assets_and_frozen_copies_exact':True,
            'current24_five_owner_ledgers_and_inventory_exact':True,'coverage_complete':False,
            'scope':'Actual canonical source/evidence closure only. Original complete semantic bodies/reasons/hypotheses/times unchanged. Narrow independent canonical binding and isolated candidate25 remain separate.'}
    out=group/'source-exact-canonical-paired-readiness25-v1.json';write(out,result);groups.append(ref(out))
guard();write(OUT,{'status':'passed_actual_two_source31_export_canonical_pairs_future25_only','prepared_at_utc':datetime.now(timezone.utc).isoformat(),
                 'source_count':2,'public_theorem_count':31,'whole_mathematical_unit_count':4,'groups':groups,'inputs':ref(INPUT),
                 'actual_helper':ref(Path(__file__)),'all1144_selected24_sources_and_frozen_copies_exact':True,
                 'all31_current52_assets_and_frozen_copies_exact':True,'current24_five_owner_ledgers_and_inventory_exact':True,'coverage_complete':False})
print(json.dumps({'status':'passed','readiness':ref(OUT)}),flush=True)

"""Record a real TMP Lean trial while holding the actually audited27/current55 inputs.

This installs no proof or ledger and claims no new aggregate or source coverage.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys, time
ROOT=Path('/home/oxrexkevin/SafetyBased')
assert len(sys.argv)==3
source,record=map(Path,sys.argv[1:])
for p in (source,record):
    assert p.is_absolute() and p.resolve().is_relative_to(Path('/tmp')) and not p.is_symlink()
assert source.is_file() and source.suffix=='.lean' and record.suffix=='.json'
log=record.with_suffix('.log');snapshot=record.with_name(record.stem+'-source.lean')
assert all(not p.exists() for p in (record,log,snapshot))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_bytes())
def ref(n):return {'file':n,'sha256':sha(ROOT/n)}
def safe(n):
    assert type(n) is str and n and str(Path(n))==n and not Path(n).is_absolute() and '..' not in Path(n).parts
    p=ROOT/n;assert p.resolve().is_relative_to(ROOT) and not p.is_symlink();return p
PINNED={
'reports/full-coverage/checkpoint-27-selection.json':'ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd',
'reports/full-coverage/checkpoint-26-selection.json':'12527ed93a283e1b37a491f7f799ac04e6217b1d7e20aee74116b312e580e23f',
'reports/full-coverage/root-source55-final-owner-integration27-v1.json':'aa2cfe3ee0c56ea0758b900abce5121cc36c9725444702ee775e75ab67dd50ea',
'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json':'5b6c87b7cc5e385f1e45d78dbd2340cdfa93f44d54989ef05fcd5a1ff77aa75b',
'book/coverage/inventory.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf',
'book/coverage/inventory-after-correction55.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf',
'book/coverage/material-corrections.json':'21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94',
'reports/full-coverage/source54-55-corrections-application-v1.json':'845937be3efd0d3bb88518fe9597b4bf6f22ead237cd1292a28ad5b16265c528',
'book/coverage/checks/future27-core/eight-source141-canonical-v1/eight-source141-actual-canonical-paired-readiness27-v1.json':'74f6e5413cb390698e6090b798d6f0eed0b667082bd24681f7b2e82c49deef1f',
}
for n,h in PINNED.items():assert sha(safe(n))==h,n
selection=read('reports/full-coverage/checkpoint-27-selection.json');baseline=read('reports/full-coverage/checkpoint-26-selection.json')
assert selection['proof_file_count']==len(selection['proof_files'])==1175 and selection['new_file_count']==8
assert len(baseline['proof_files'])==1167 and set(baseline['proof_files'])<=set(selection['proof_files'])
assert all(selection['proof_files'][n]['sha256']==r['sha256'] for n,r in baseline['proof_files'].items())
global_audit=read('reports/full-coverage/root-source55-final-owner-integration27-v1.json')
assert global_audit['integrity_status']=='passed' and global_audit['errors']==[] and global_audit['mathematical_coverage_complete'] is False
assert global_audit['inventory_sha256']==PINNED['book/coverage/inventory.json']
integration=read('reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')
assert integration['applied'] is True
owners={r['destination']:r['candidate']['sha256'] for r in integration['exact_replacements']};assert len(owners)==5
for row in global_audit['domains']:assert row['ledger_sha256']==owners['book/coverage/'+row['domain']+'.json']
assets=dict(selection['current_book_assets_sha256'])
assert len(assets)==31
assert assets['SafeLearning/lyapunov-mpc.html']=='63a1ac8be7f5cf8b490dd1dd872d416affee95f6de0d5ba3c1c618f4b86cd79f'
assert assets['SafeLearning/verification.html']=='d01ce44636cd6100bef100a0f466539d61ab6d6c3e8ab64b0d39c7dbdf740f53'
assert read('book/coverage/inventory.json')['source_sha256']=={n:h for n,h in assets.items() if n.endswith('.html')}
assert len(read('book/coverage/material-corrections.json')['corrections'])==55
held={n:r['sha256'] for n,r in selection['proof_files'].items()};held.update(assets);held.update(owners)

def actual(n,command):
    d=read(n);assert type(d['actual_exit_code']) is int and d['actual_exit_code']==0
    assert d['actual_command']==command and d['actual_workdir']==str(ROOT)
    assert d['helper_sha256_before']==d['helper_sha256_after'] and d['helper_sha256_after']
    assert sha(safe(d['log']))==d['log_sha256']
    for helper,h in d['helper_sha256_after'].items():assert sha(safe(helper))==h;PINNED[helper]=h
    PINNED[n]=sha(safe(n));PINNED[d['log']]=d['log_sha256'];return d
actual('reports/full-coverage/owner27-reviewed-candidate-integration-execution-v1.json',['python3','book/coverage/checks/root_integrate_owner27_candidates_v2.py','--bindings','book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json','--apply'])
actual('reports/full-coverage/prepare-checkpoint27-selection-execution-v1.json',['python3','book/coverage/prepare_checkpoint27_selection_v2.py','--plan','book/coverage/checks/future27-core/checkpoint27-installed-owner-selection-plan-v2.json','--apply'])
actual('reports/full-coverage/verify-checkpoint27-execution-v1.json',['python3','reports/full-coverage/checkpoint-27/verification/lean/verify.py','--reuse-kernel-from',str(ROOT/'reports/full-coverage/checkpoint-26')])
auditn='reports/full-coverage/checkpoint-27/reports/lean-verification/verification.json';audit=read(auditn)
assert audit['status']=='passed' and audit['proof_file_count']==1175 and audit['theorem_count']==9644
assert audit['proof_sha256']=={n:r['sha256'] for n,r in selection['proof_files'].items()}
assert len(audit['declarations'])==len(audit['axiom_dependencies'])==9644
assert {r['name'] for r in audit['declarations']}==set(audit['axiom_dependencies'])
assert set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert all(set(v)<=set(audit['allowed_standard_axioms']) for v in audit['axiom_dependencies'].values())
assert audit['checks'] and all(type(r['exit_code']) is int and r['exit_code']==0 for r in audit['checks'])
assert sum(r.get('evidence_mode')=='fresh_kernel_replay' for r in audit['checks'])==8
assert sum(r.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for r in audit['checks'])==1167
PINNED[auditn]=sha(safe(auditn))
for n in ('verification/lean/lean-toolchain','verification/lean/lakefile.toml','verification/lean/lake-manifest.json'):PINNED[n]=sha(safe(n))
pairs=read('book/coverage/checks/future27-core/eight-source141-canonical-v1/eight-source141-actual-canonical-paired-readiness27-v1.json')
assert pairs['errors']==[] and pairs['source_count']==8 and pairs['public_theorem_count']==141
new={r['canonical_source']:r['source']['sha256'] for r in pairs['sources']}
assert new=={n:held[n] for n in set(selection['proof_files'])-set(baseline['proof_files'])}
assert len(pairs['actual_paired_records'])==16
seen=set()
for r in pairs['actual_paired_records']:
    n=r['source']['file'];kind=r['kind'];assert n in new and r['source']['sha256']==new[n]
    assert kind in {'standalone','named'} and (n,kind) not in seen;seen.add((n,kind))
    assert type(r['actual_exit_code']) is int and r['actual_exit_code']==0
    d=read(r['actual_record']['file']);assert type(d['exit_code']) is int and d['exit_code']==0
    assert d['source']==n and d['source_sha256_before']==d['source_sha256_after']==new[n]
    stem=Path(n).stem;command=['lake','env','lean','SafeLearning/'+stem+'.lean'] if kind=='standalone' else ['lake','build','SafeLearning.'+stem]
    assert d['command']==command and d['actual_workdir']==str(ROOT/'verification/lean')
    assert r['raw_log']=={'file':d['log'],'sha256':d['log_sha256']} and r['source_snapshot']['sha256']==new[n]
    for key in ('actual_record','raw_log','source_snapshot'):
        row=r[key];assert sha(safe(row['file']))==row['sha256'];PINNED[row['file']]=row['sha256']
assert seen=={(n,k) for n in new for k in ('standalone','named')}
runner_before=sha(Path(__file__))
def guard():
    for n,h in {**PINNED,**held}.items():assert sha(safe(n))==h,n
    assert sha(Path(__file__))==runner_before

guard();before=sha(source)
with snapshot.open('xb') as f:f.write(source.read_bytes())
assert sha(snapshot)==before
command=['lake','env','lean',str(source)];started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with log.open('xb') as f:r=subprocess.run(command,cwd=ROOT/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
finished=datetime.now(timezone.utc).isoformat();after=sha(source);errors=[]
try:guard()
except Exception as error:errors.append(str(error))
passed=r.returncode==0 and before==after and not errors
out={'status':'passed_actual_tmp_lean_only' if passed else 'failed_actual_tmp_lean_or_protection','actual_exit_code':r.returncode,'actual_runner_exit_code':0 if passed else 1,'actual_command':command,'actual_workdir':str(ROOT/'verification/lean'),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,'source':str(source),'source_sha256_before':before,'source_sha256_after':after,'source_snapshot':str(snapshot),'source_snapshot_sha256':sha(snapshot),'raw_log':str(log),'raw_log_sha256':sha(log),'source_unchanged':before==after,'original_actual_runner':{'file':str(Path(__file__)),'sha256':runner_before},'actual_installed27_selection':ref('reports/full-coverage/checkpoint-27-selection.json'),'actual_current55_installed27_global_integrity':ref('reports/full-coverage/root-source55-final-owner-integration27-v1.json'),'actual_frozen27_original_audit':ref(auditn),'protected_proof_sources':1175,'protected_selected27_proof_sources':1175,'unchanged_baseline26_selected_proof_sources':1167,'unchanged_canonical_new27_proof_sources':8,'unchanged_current55_book_assets':31,'unchanged_installed27_live_owners':5,'installed27_owner_sha256':owners,'pinned_installed27_provenance_sha256':PINNED,'protection_errors':errors,'canonical_installation_or_aggregate_verification_claimed':False}
with record.open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps(out));raise SystemExit(0 if passed else 1)

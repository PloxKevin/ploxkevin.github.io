from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re

ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_bytes())
def ref(p): return {'file':str(p),'sha256':sha(p)}
def checked(r):
    p=Path(r['file']); p=p if p.is_absolute() else ROOT/p
    assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'],str(p)
    return p
def codes(d,w):
    keys=[k for k in ('exit_code','actual_exit_code','actual_runner_exit_code') if k in d]
    assert keys and all(type(d[k]) is int and d[k]==w for k in keys)
def guard():
    selection=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json')
    assert len(selection['proof_files'])==selection['proof_file_count']==1175
    held={k:v['sha256'] for k,v in selection['proof_files'].items()}
    held.update(read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256'])
    held.update({r['destination']:r['candidate']['sha256'] for r in read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']})
    held.update({'book/coverage/inventory.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf','book/coverage/material-corrections.json':'21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94','reports/full-coverage/checkpoint-27-selection.json':'ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'})
    for n,h in held.items(): assert sha(ROOT/n)==h,n
    return held
def archive(name,paths,scope):
    out=ROOT/'book/coverage/checks/future28-foundations'/name
    catalog=out/(name+'-byte-aliases-v1.json')
    assert not catalog.exists()
    aliases={}
    for p in dict.fromkeys(map(str,paths)):
        original=Path(p); body=original.read_bytes();h=sha(original)
        destination=out/h/original.name;destination.parent.mkdir(parents=True,exist_ok=True)
        if destination.exists(): assert destination.read_bytes()==body
        else:
            with destination.open('xb') as f:f.write(body)
        assert destination.read_bytes()==body
        aliases[p]={'file':str(destination.relative_to(ROOT)),'sha256':h}
    d={'status':'closed_exact_original_byte_aliases','archived_at_utc':datetime.now(timezone.utc).isoformat(),'scope':scope,'original_closed_byte_aliases':aliases,'original_file_count':len(aliases)}
    with catalog.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
    print(json.dumps({'catalog':ref(catalog),'original_file_count':len(aliases)}))

held=guard()
peerp=Path('/tmp/foundations-residual17-independent-modules-full-source-review28-v1.json')
assert sha(peerp)=='04b0d3c1ad2fd92657d8561ca0ae3ed62897cc7e4b837f510eccf4ec434f37e8'
p=read(peerp);request=read(checked(p['request'])); findings=read(checked(p['original_findings']))
assert p['entire_original_findings_body_and_time']==findings
for k,v in findings.items():
    if k!='closed_evidence_sha256':assert p[k]==v,k
assert p['errors']==[] and p['public_theorem_count']==17
assert p['entire_source']==request['entire_source']==checked(p['proof_source']).read_text()
assert p['full_reused_dependency_sources']==request['full_reused_dependency_sources']
assert p['entire_original_existing_material_claims_and_times']==request['current_existing_claims_unchanged']
assert p['entire_original_actual_record_and_time']==request['entire_original_actual_record_and_time']
assert p['entire_genuine_prior_failed_trials']==request['genuine_previous_failed_trials']
assert p['entire_raw_log']==checked(p['raw_log']).read_text()==request['entire_raw_log']
assert len(re.findall(r'^.*:\d+:\d+: warning:',p['entire_raw_log'],re.M))==p['actual_warning_count']==4
assert [u['source_unit_key'] for u in p['material_units']]==request['newly_requested_material_units']
for u in p['material_units']:
    assert u['whole_unit_approved'] is True and u['whole_literal_approved'] is True and u['status']=='proved'
    assert u['missing_clauses']==[] and u['remaining_gaps']==[]
actual=read(checked(p['actual_reader_execution']));codes(actual,0)
assert actual['actual_command']==['python3',str(checked(p['actual_checker']))]
assert actual['actual_workdir']==str(ROOT)
assert actual['checker_sha256_before']==actual['checker_sha256_after']==p['actual_checker']['sha256']
assert actual['actual_runner']==p['actual_reader_runner']
assert actual['raw_log_sha256']==p['actual_reader_raw_log']['sha256']
log=checked(p['actual_reader_raw_log']).read_text();logged= json.loads(log)
assert logged['findings']==p['original_findings'] and logged['errors']==[] and logged['public_theorem_count']==17
for n,h in p['closed_evidence_sha256'].items():assert sha(n)==h,n
residualpaths=[peerp]+[checked(p[k]) for k in ('actual_checker','actual_reader_execution','actual_reader_raw_log','actual_reader_runner','original_findings')]
archive('original-residual17-independent-modules-review28',residualpaths,'Original Modules full-three-literal semantic decisions and measured reader0/code/raw/findings retained without changing any original body or time; no canonical proof, owner, selection or aggregate installation.')

literalp=Path('/tmp/foundations-literal-gradient15-full-review28-v1/foundations-literal-gradient15-full-review28-v1.json')
assert sha(literalp)=='0be78755dd642eebc9fc9ae9ef2c9a19c365da23fdcd95cd28e4f5ea19e6664b'
j=read(literalp)
assert j['public_theorem_count']==15 and j['independent_whole_unit_approval'] is False
assert checked(j['proof_source']).read_text()==j['entire_source']
for i,row in enumerate(j['actual_trials_original_bodies_and_times']):
    trial=read(checked(row['record']));assert trial==row['entire_original_record_and_time'];codes(trial,0 if i==2 else 1)
    assert trial['protection_errors']==[] and trial['protected_proof_sources']==1175
    assert checked(row['raw_log']).read_text()==row['entire_raw_log']
    assert checked(row['source_snapshot']).read_text()==row['entire_original_source']
    assert trial['source_sha256_before']==trial['source_sha256_after']==trial['source_snapshot_sha256']==row['source_snapshot']['sha256']
    assert trial['actual_command']==['lake','env','lean',trial['source']]
    assert trial['actual_workdir']==str(ROOT/'verification/lean')
    assert trial['raw_log_sha256']==row['raw_log']['sha256']
    assert len(re.findall(r'^.*:\d+:\d+: warning:',row['entire_raw_log'],re.M))==row['actual_emitted_warning_diagnostics']
assert j['actual_successful_emitted_warning_diagnostics']==1
literalpaths=[literalp,Path('/tmp/prepare-foundations-literal-gradient15-full-review28-v1.py')]
for original,alias in j['original_closed_byte_aliases'].items():
    assert Path(original).read_bytes()==checked(alias).read_bytes()
    literalpaths.append(Path(original))
archive('original-literal-gradient15-three-unit-request28',literalpaths,'Original exact three-literal15-body request and all three genuine failed1/failed1/passed0 Lean trials preserved. One emitted pass warning. Independent whole-unit semantic review and canonical proof/owner/aggregate installation remain pending.')
assert guard()==held
print(json.dumps({'status':'passed_exact_original_semantic_reader_and_trial_closure','errors':[],'whole_residual_units':[1288,1290,1293],'literal_gradient_whole_approval_pending':True,'protected_proof_sources':1175,'current_source_assets':31,'current_owners':5}))

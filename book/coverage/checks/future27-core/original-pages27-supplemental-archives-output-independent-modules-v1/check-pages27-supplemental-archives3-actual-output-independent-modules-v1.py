from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased');PUB=ROOT/'reports/book/publication-repo'
HELPER='book/coverage/checks/root_prepare_pages27_supplemental_archives_v3.py'
REPORT='reports/full-coverage/pages27-supplemental-archive-configuration-v1.json'
ACTUAL='reports/full-coverage/pages27-supplemental-archive-configuration-execution-v1.json'
INPUT='book/coverage/checks/future27-core/checkpoint27-supplemental-archive-inputs-v1.json'
CODE='book/coverage/checks/pages27-supplemental-archives-helper-independent-modules-review-v1.json'
OUT=Path('/tmp/pages27-supplemental-archives3-actual-output-independent-modules-findings-v1.json')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_bytes())
def ref(n):return {'file':n,'sha256':sha(ROOT/n)}
def zero(d):
    values=[d[k]for k in ('actual_exit_code','exit_code')if k in d]
    assert values and all(type(v)is int and v==0 for v in values)
def native(d,command):
    zero(d)
    values=[d[k]for k in ('actual_command','command')if k in d];assert values and all(v==command for v in values)
    values=[d[k]for k in ('actual_workdir','working_directory','cwd')if k in d];assert values and all(v==str(ROOT)for v in values)
    assert d['helper_sha256_before']==d['helper_sha256_after']
    for n,h in d['helper_sha256_after'].items():assert sha(ROOT/n)==h
    for k in ('log','raw_log'):
        if k in d:assert d[k]==d['log']
    for k in ('log_sha256','raw_log_sha256'):
        if k in d:assert d[k]==d['log_sha256']
    assert sha(ROOT/d['log'])==d['log_sha256']
start=datetime.now(timezone.utc).isoformat()
assert sha(ROOT/HELPER)=='9b06ca5c50a93cae79a5a02bd8dd13400b2a69f331c013eb8a635812476377c0'
assert sha(ROOT/CODE)=='69dc83bba9a57d1f0fae4544c85fc32cf24af01f3c85dba501c4858602e75595'
code=read(CODE);assert code['errors']==[]and code['real_read_only_prepare_passed']is True and code['fixture_count']==32
execution=read(ACTUAL);native(execution,['python3',HELPER,'--apply'])
assert execution['helper_sha256_after']=={HELPER:sha(ROOT/HELPER)}
body=read(REPORT);assert body['status']=='passed_exact_checkpoint27_supplemental_archive_configuration_requires_actual_stage_and_pages'
assert body['helper']==ref(HELPER)and body['input_plan']==ref(INPUT)
assert sha(ROOT/INPUT)=='d3a35541efc570b1c1406170ceb67f68027220e62115106b0b260bce08b3a420'
assert (ROOT/REPORT).read_bytes()==(PUB/REPORT).read_bytes()
backup=body['previous_configuration'];assert set(backup)=={'file','sha256'}
assert sha(ROOT/backup['file'])==sha(PUB/backup['file'])==backup['sha256']=='37afb173e76aee80569b4903ca88b39c5e12d4729a65627f447d2060842db1ea'
prior=read(body['previous_configuration_report']['file'])
assert ref(body['previous_configuration_report']['file'])==body['previous_configuration_report']
assert prior['excluded_count']==129 and prior['config_sha256']==backup['sha256']
assert body['previous_actual_execution']==ref('reports/full-coverage/pages27-config-execution-v2.json')
prior_actual=read(body['previous_actual_execution']['file']);native(prior_actual,['python3','book/coverage/checks/root_prepare_pages27_config_v5.py','--apply'])
expected_added={'book/coverage/checks/future27-core/original-documentation27-foundations-review-v1','book/coverage/checks/future27-core/original-pages27-config5-actual-output-independent-modules-v2','reports/full-coverage/working-inventory55-timestamp-regeneration-before-restoration28-v1.json','reports/full-coverage/publication27-prestage-v1.json'}
assert set(body['new_literal_exclusions'])==expected_added
assert set(body['exclusions'])==set(prior['exclusions'])|expected_added
assert len(body['exclusions'])==body['excluded_count']==133
header='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'
expected_config=(header+''.join('  - '+n+'\n'for n in sorted(body['exclusions']))).encode()
assert (PUB/'_config.yml').read_bytes()==expected_config and sha(PUB/'_config.yml')==body['config_sha256']
assert (ROOT/backup['file']).read_bytes()==(header+''.join('  - '+n+'\n'for n in sorted(prior['exclusions']))).encode()
assert body['required_publication_files_sha256']==prior['required_publication_files_sha256']
required=body['required_publication_files_sha256'];assert len(required)==body['required_download_count']==1284
kept=lambda n:not any(n==e or n.startswith(e+'/')for e in body['exclusions'])
for n,h in required.items():assert kept(n)and sha(PUB/n)==h,n
inputs=read(INPUT);assert inputs['unresolved_references']==[]and len(inputs['supplemental_inputs_sha256'])==211
for n,h in inputs['supplemental_inputs_sha256'].items():assert sha(ROOT/n)==h,n
for original,r in inputs['original_byte_aliases'].items():assert sha(ROOT/r['file'])==r['sha256'],original
retired={n:h for n,h in inputs['supplemental_inputs_sha256'].items()if any(n==e or n.startswith(e+'/')for e in expected_added-{'reports/full-coverage/publication27-prestage-v1.json'})}
assert retired==body['retained_supplemental_originals_sha256']
assert body['generated_whitelist_metadata_exclusion']=='reports/full-coverage/publication27-prestage-v1.json'
selection=read('reports/full-coverage/checkpoint-27-selection.json')
assert len(selection['proof_files'])==1175 and sha(ROOT/'reports/full-coverage/checkpoint-27-selection.json')=='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
auditn='reports/full-coverage/lean-checkpoint-27/verification-original.json';audit=read(auditn)
assert sha(ROOT/auditn)=='fdd431eea1137c48032d20cdb31270b8d76a4ca715f19715167a1ec67cff194f'
assert audit['status']=='passed'and audit['proof_file_count']==1175 and audit['theorem_count']==9644 and len(audit['declarations'])==9644
assert audit['proof_sha256']=={n:r['sha256']for n,r in selection['proof_files'].items()}
assert len(audit['checks'])==1178
for r in audit['checks']:zero(r)
assert sum(r.get('evidence_mode')=='fresh_kernel_replay'for r in audit['checks'])==8
assert sum(r.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports'for r in audit['checks'])==1167
assert set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert all(set(v)<=set(audit['allowed_standard_axioms'])for v in audit['axiom_dependencies'].values())
bindings=read('book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')
assets=bindings['exact_current55_safelearning_assets_sha256'];assert len(assets)==31
integration=read('reports/full-coverage/owner27-reviewed-candidate-integration-v1.json');assert integration['applied']is True
owners={r['destination']:r['candidate']['sha256']for r in integration['exact_replacements']};assert len(owners)==5
held={n:r['sha256']for n,r in selection['proof_files'].items()};held.update(assets);held.update(owners)
def guard():
    for n,h in held.items():assert sha(ROOT/n)==h,n
    for n,h in assets.items():assert sha(PUB/n)==h,n
guard()
assert sha(ROOT/'book/coverage/inventory.json')=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
# Budget check describes the actual configuration and the exact not-yet-staged copies.
included=0
for p in PUB.rglob('*'):
    n=p.relative_to(PUB).as_posix()
    if '.git'in p.relative_to(PUB).parts or not kept(n):continue
    assert not p.is_symlink(),n
    if p.is_file():included+=p.stat().st_size
delta=sum((ROOT/n).stat().st_size-((PUB/n).stat().st_size if (PUB/n).is_file()else 0)for n in inputs['supplemental_inputs_sha256']if kept(n))
assert included+delta<850000000
assert body['prospective_website_bytes_with_explicit_supplemental_copy']==code['independent_prospective_website_bytes']==837725170
guard()
closure={n:sha(ROOT/n)for n in (HELPER,REPORT,ACTUAL,INPUT,CODE,backup['file'],auditn,'reports/full-coverage/pages27-config-preparation-v1.json','reports/full-coverage/pages27-config-execution-v2.json','book/coverage/checks/future27-core/pages27-config-independent-modules-output-v5.json','reports/full-coverage/checkpoint-27-manifest.json','reports/full-coverage/checkpoint-27-selection.json')}
closure.update(inputs['supplemental_inputs_sha256']);closure[execution['log']]=execution['log_sha256']
for r in inputs['original_byte_aliases'].values():closure[r['file']]=r['sha256']
assert not any(n.startswith('reports/book/publication-repo/')for n in closure)
out={'status':'passed_independent_actual_checkpoint27_supplemental_archive_configuration','errors':[],'reviewer':'/root/modules_resume','reviewed_at_utc':start,'completed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(HELPER),'config_sha256':body['config_sha256'],'excluded_count':133,'native_preparation_report':ref(REPORT),'actual_execution':ref(ACTUAL),'actual_execution_entire_original_body_and_time':execution,'native_preparation_entire_original_body_and_time':body,'original_config5_native_report_body_and_time':prior,'original_config5_actual_execution_body_and_time':prior_actual,'code_peer':ref(CODE),'input_plan':ref(INPUT),'selected_sources':1175,'public_theorems':9644,'fresh_kernel_replay':8,'reused_identical_kernel':1167,'required_publication_files_sha256':required,'new_literal_exclusions':sorted(expected_added),'unchanged_current55_assets31_and_installed27_owners5_and_sources1175_rehashed_before_after':True,'retained_git_stage_supplemental_original_inputs_count':211,'original_alias_count':697,'current_included_website_bytes':included,'prospective_exact_remaining_supplemental_copy_bytes':delta,'prospective_website_bytes_with_current_native_outputs':included+delta,'coverage_complete':False,'scope':'Actual helper3 apply0, Root/PUB native report and original backup, exact 129-to-133 configuration overlay and all required public downloads are independently confirmed. The 211 original stage inputs and 697 original byte aliases remain unchanged and are retained for the separate Git stage. New archive exclusions are website-only; no Git HEAD/Pages/live delivery is inferred. Config5 native129 and all old review bodies/times are preserved. Generated whitelist metadata is a future exact pathname exclusion, with no invented file hash. Current PUB config is bound by config_sha256 only; no publication repository path is copied into the Root closed evidence map.','closed_evidence_sha256':closure}
OUT.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'findings':{'file':str(OUT),'sha256':sha(OUT)},'config_sha256':body['config_sha256'],'prospective_bytes':included+delta}))

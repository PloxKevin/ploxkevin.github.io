"""Stage exact audited26 inputs and closed actual evidence. Root executes this.

Authoring and code review establish no audit, copy, Git, Pages or live result.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, subprocess
ROOT=Path(__file__).resolve().parents[3]
PUB=ROOT/'reports/book/publication-repo'
SELF=Path(__file__).relative_to(ROOT).as_posix()
REPORT='reports/full-coverage/publication26-prestage-v1.json'
PEER='book/coverage/checks/future26-core/publication26-stage-independent-review-v4.json'
CONFIG_HELPER='book/coverage/checks/root_prepare_pages26_config_v3.py'
CONFIG_HELPER_SHA='30d7f41eb587b915230eaa272efd44355b6a1965864ec71624ae295c2c03b50f'
CONFIG_CODE_PEER='book/coverage/checks/pages26-config-helper-independent-modules-review-v3.json'
CONFIG_OUTPUT_PEER='book/coverage/checks/future26-core/pages26-config-independent-modules-output-v3.json'
ROOT_OUTPUT='book/coverage/checks/future26-core/root-checkpoint26-production-output-independent-confirmation-v1.json'
ROOT_CHECKER='book/coverage/checks/root_check_checkpoint26_selection_output_v2.py'
ROOT_CHECKER_SHA='9c1959903a4f7a92808478c85a92fafe2e0381250e7b1fb83479e77bc1de86b4'
MODULE_OUTPUT='book/coverage/checks/future26-core/modules-checkpoint26-production-output-independent-confirmation-v1.json'
BROWSER_HELPER='book/coverage/checks/root_prepare_browser26_v2.py'
BROWSER_HELPER_SHA='b71fd49a7d5fe7ede6149a4ed8e1e2d4f2680036f9fb7f6507f42fea90ba19ab'
BROWSER_CODE_PEER='book/coverage/checks/browser26-preparation-helper-independent-modules-review-v1.json'
BROWSER_OUTPUT_PEER='book/coverage/checks/future26-core/browser26-actual-output-independent-modules-review-v1.json'
DOC_HELPER='book/coverage/checks/root_prepare_checkpoint26_documentation_v2.py'
DOC_HELPER_SHA='608690bc7a3094e02dd02b906729b4773c508edae6f8d54213f7a6eea118884a'
DOC_PEER='book/coverage/checks/future26-core/documentation26-helper-independent-applied-review-v2.json'

def safe(n):
    assert isinstance(n,str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts
    assert str(Path(n))==n and not any(c in n for c in ('\0','\n','\r'))
    p=ROOT/n;assert p.resolve().is_relative_to(ROOT.resolve());return p
def target(n):
    safe(n);p=PUB/n;assert p.resolve().is_relative_to(PUB.resolve());return p
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads(safe(n).read_text())
def zero(d,code=0):
    values=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
    assert values and all(type(v) is int and v==code for v in values)
def actual(n,code=0):
    d=read(n);zero(d,code)
    logs=[d[k] for k in ('log','raw_log') if k in d]
    hashes=[d[k] for k in ('log_sha256','raw_log_sha256') if k in d]
    assert logs and hashes and all(x==logs[0] for x in logs) and all(x==hashes[0] for x in hashes)
    assert sha(safe(logs[0]))==hashes[0];return d,logs[0]
def dirty():
    raw=subprocess.run(['git','status','--porcelain','-z','--untracked-files=all'],cwd=PUB,check=True,capture_output=True).stdout
    out=set()
    for entry in filter(None,raw.decode().split('\0')):
        assert entry[:2] not in {'R ',' R','C ',' C'} and 'D' not in entry[:2],entry
        out.add(entry[3:])
    return out
def staged():
    return {n.decode() for n in subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUB,check=True,capture_output=True).stdout.split(b'\0') if n}
def peer_evidence(n,paths):
    peer=read(n);assert 'passed' in peer['status'] and peer.get('errors',[])==[];paths.add(n)
    aliases=peer.get('original_closed_byte_aliases',{})
    if isinstance(aliases,list):
        assert all(isinstance(r,dict) and set(r)=={'original_path','file','sha256'} for r in aliases)
        assert len({r['original_path'] for r in aliases})==len(aliases)
        aliases={r['original_path']:{'file':r['file'],'sha256':r['sha256']} for r in aliases}
    assert isinstance(aliases,dict)
    canonical={}
    for original,row in aliases.items():
        assert isinstance(original,str) and Path(original).is_absolute() and not any(c in original for c in ('\0','\n','\r'))
        assert isinstance(row,dict) and set(row)=={'file','sha256'}
        n2,digest=row['file'],row['sha256']
        assert isinstance(digest,str) and len(digest)==64 and all(c in '0123456789abcdef' for c in digest)
        assert n2 not in canonical or canonical[n2]==digest
        assert sha(safe(n2))==digest;canonical[n2]=digest;paths.add(n2)
    closed=peer.get('closed_evidence_sha256',{});assert isinstance(closed,dict)
    for original,digest in closed.items():
        if Path(original).is_absolute():
            assert original in aliases and aliases[original]['sha256']==digest;n2=aliases[original]['file']
        else:n2=original
        assert sha(safe(n2))==digest;paths.add(n2)
    return peer

def add_refs(value,paths):
    """Read only explicitly typed native byte references, never glob guesses."""
    if isinstance(value,dict):
        name=value.get('file',value.get('path'));digest=value.get('sha256')
        if isinstance(name,str) and isinstance(digest,str):
            assert sha(safe(name))==digest;paths.add(name)
        for v in value.values():add_refs(v,paths)
    elif isinstance(value,list):
        for v in value:add_refs(v,paths)

def main():
    assert not safe(REPORT).exists() and not target(REPORT).exists()
    manifest_name='reports/full-coverage/checkpoint-26-manifest.json'
    selection_name='reports/full-coverage/checkpoint-26-selection.json'
    audit_name='reports/full-coverage/lean-checkpoint-26/verification-original.json'
    manifest,selection,audit=map(read,(manifest_name,selection_name,audit_name))
    assert manifest['status']=='formal_verification_passed_partial_coverage'
    assert manifest['selection_sha256']==sha(safe(selection_name))
    assert len(manifest['proof_files'])==selection['proof_file_count']==audit['proof_file_count']==1167
    assert manifest['proof_files']==selection['proof_files'] and selection['new_file_count']==11 and selection['coverage_complete'] is False
    assert audit['status']=='passed' and audit['theorem_count']==9503
    assert len(audit['declarations'])==len(audit['axiom_dependencies'])==9503
    assert {d['name'] for d in audit['declarations']}==set(audit['axiom_dependencies'])
    assert set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
    assert all(set(v)<=set(audit['allowed_standard_axioms']) for v in audit['axiom_dependencies'].values())
    assert all(type(c['exit_code']) is int and c['exit_code']==0 for c in audit['checks'])
    assert sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])==11
    assert sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])==1156
    assert audit['proof_sha256']=={n:r['sha256'] for n,r in manifest['proof_files'].items()}
    assert manifest['successful_verification']['report_sha256']==sha(safe(audit_name))
    assert selection['current_inventory_sha256']==sha(safe('book/coverage/inventory.json'))==sha(safe('book/coverage/inventory-after-correction53.json'))=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
    ledger_name='reports/full-coverage/publication-checks/ledger-checkpoint-26.json';ledger=read(ledger_name)
    assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
    assert ledger['inventory_sha256']==selection['current_inventory_sha256']
    for row in ledger['domains']:assert row['ledger_sha256']==sha(target('book/coverage/'+row['domain']+'.json'))
    paths=set(read('reports/full-coverage/publication-prepared-26-files.json'))
    assert set(manifest['frozen_inputs_sha256'])<=paths
    snapshot=safe(manifest['snapshot'])
    for n,digest in manifest['frozen_inputs_sha256'].items():
        assert sha(snapshot/n)==digest and target(n).is_file(),n
        if n not in {'book/coverage/progress.json','reports/full-coverage/README.md'}:assert sha(target(n))==digest,n
    for n,row in manifest['proof_files'].items():assert sha(safe(n))==sha(target(n))==row['sha256'],n
    # Live unpruned metadata and published frozen metadata differ only by the
    # same three explicitly unreferenced Applied rows; all mathematical bodies stay exact.
    prior=read('reports/full-coverage/checkpoint-25-manifest.json')
    assert set(prior['proof_files'])<=set(manifest['proof_files']) and len(prior['proof_files'])==1156
    for n,row in prior['proof_files'].items():assert manifest['proof_files'][n]['sha256']==row['sha256']
    for owner in ('core','foundations','applied','modules'):
        n='book/coverage/'+owner+'.json';assert sha(safe(n))==manifest['working_inputs_sha256'][n]
        removed=manifest['excluded_unreferenced_ledger_metadata'][owner]
        assert removed==prior['excluded_unreferenced_ledger_metadata'][owner] and len(removed)==(3 if owner=='applied' else 0)
        normalized=read(n)
        for source in removed:
            assert source in normalized['proof_files'] and source not in manifest['proof_files'];normalized['proof_files'].pop(source)
        assert normalized==json.loads(target(n).read_text())
    content_ref=selection['previous_frozen_input_content_binding'];assert sha(safe(content_ref['file']))==content_ref['sha256']
    binding=read(content_ref['file']);rows=binding['input_bindings']
    assert binding['original_input_count']==len(rows)==44111
    assert len({r['original_frozen_path'] for r in rows})==44111
    assert {r['original_frozen_path']:r['sha256'] for r in rows}==prior['frozen_inputs_sha256']
    for r in rows:
        n=r['retained_input'];assert n in paths and sha(safe(n))==sha(target(n))==r['sha256'],n
    assets={n:d for n,d in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
    for n,d in assets.items():assert sha(safe(n))==sha(target(n))==d,n
    config_name='reports/full-coverage/pages26-config-preparation-v1.json';config=read(config_name)
    assert 'passed' in config['status'] and config['coverage_complete'] is False
    assert config['required_publication_files_sha256'][audit_name]==sha(safe(audit_name))
    assert config['required_publication_files_sha256'][manifest_name]==sha(safe(manifest_name))
    assert config['required_publication_files_sha256'][selection_name]==sha(safe(selection_name))
    assert config['exact_original_metadata_removals']==manifest['excluded_unreferenced_ledger_metadata']
    for owner in ('core','foundations','applied','modules'):
        n='book/coverage/'+owner+'.json'
        assert config['working_ledger_sha256'][n]==manifest['working_inputs_sha256'][n]
        assert config['published_frozen_ledger_sha256'][n]==manifest['frozen_inputs_sha256'][n]
    assert config['excluded_count']==len(config['exclusions'])==116 and config['website_budget_bytes']==850_000_000
    assert type(config['prospective_included_website_bytes_before_new_native_records']) is int
    assert 0<=config['prospective_included_website_bytes_before_new_native_records']<850_000_000
    assert sha(PUB/'_config.yml')==config['config_sha256']
    assert config['helper']=={'file':CONFIG_HELPER,'sha256':CONFIG_HELPER_SHA} and sha(safe(CONFIG_HELPER))==CONFIG_HELPER_SHA
    for n,h in config['required_publication_files_sha256'].items():assert sha(target(n))==h,n
    browser_name='reports/full-coverage/browser-checkpoint-26.json';browser=read(browser_name)
    assert browser['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence' and browser['coverage_complete'] is False
    assert browser['source_sha256']==assets
    assert (browser['page_count'],browser['requested_viewport_count'],browser['verified_viewport_count'])==(29,145,145)
    assert (browser['fresh_verified_viewport_count'],browser['retained_verified_viewport_count'])==(5,140)
    assert (browser['screenshot_count'],browser['skipped_capture_target_count'])==(48,10)
    assert browser['manual_visual_inspection']['status']=='whole_48_capture_manual_review_remains_pending'
    for n,h in browser['qa_source_sha256'].items():assert sha(safe(n))==sha(target(n))==h
    manual_ref=browser['manual_visual_inspection']['scoped_changed_prose_review']
    assert manual_ref=={'file':'reports/full-coverage/source53-six-paragraph-content-manual-review26-v1.json','sha256':'44e380bda0d0c0a6945c7980eca2d15da069b027280dd2144a48082d29620719'}
    assert sha(safe(manual_ref['file']))==manual_ref['sha256'];manual=read(manual_ref['file'])
    assert manual['status']=='passed_actual_six_scoped_content_image_inspections' and manual['source_sha256']==assets['SafeLearning/lyapunov-mpc.html']
    assert len(manual['inspected_captures'])==len({c['path'] for c in manual['inspected_captures']})==6
    assert sha(safe(BROWSER_HELPER))==BROWSER_HELPER_SHA and sha(safe(DOC_HELPER))==DOC_HELPER_SHA
    progress=read('book/coverage/progress.json');doc_name='reports/full-coverage/progress-checkpoint26-preparation-update-v1.json';doc=read(doc_name)
    assert doc['status']=='passed_actual_checkpoint26_audit_documentation_prepared_delivery_pending'
    assert doc['helper']=={'file':DOC_HELPER,'sha256':DOC_HELPER_SHA}
    assert doc['current_progress']=={'file':'book/coverage/progress.json','sha256':sha(safe('book/coverage/progress.json'))}
    assert doc['current_readme']=={'file':'reports/full-coverage/README.md','sha256':sha(safe('reports/full-coverage/README.md'))}
    assert progress['verified_checkpoint']['proof_files']==1167 and progress['verified_checkpoint']['theorems']==9503 and progress['verified_checkpoint']['coverage_complete'] is False
    assert progress['publication_status']=='checkpoint26_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks'
    assert progress['live_delivery_status']=='checkpoint26_awaiting_actual_pages_and_live_checks' and progress['current_documented_material_corrections']==53
    static_name='reports/full-coverage/integration-26.json';static=read(static_name)
    assert static['status']=='PASS' and static['errors']==[] and static['counts']['html_pages']==29 and static['counts']['all_current_exercises']==556
    extra={SELF,PEER,manifest_name,selection_name,audit_name,ledger_name,content_ref['file'],CONFIG_HELPER,CONFIG_CODE_PEER,CONFIG_OUTPUT_PEER,ROOT_OUTPUT,MODULE_OUTPUT,BROWSER_HELPER,BROWSER_CODE_PEER,BROWSER_OUTPUT_PEER,DOC_HELPER,DOC_PEER,doc_name,config_name,browser_name,static_name,
        'book/coverage/progress.json','reports/full-coverage/README.md','reports/full-coverage/publication-prepared-26-files.json',
        'reports/full-coverage/pages26-config-previous-original-v1.yml','reports/full-coverage/pages26-config-previous-original-v1.json',
        'reports/full-coverage/root-source53-final-owner-integration26-v1.json',
        'book/coverage/checks/root_stage_publication26_v1.py','book/coverage/checks/root_stage_publication26_delivery_metadata_v1.py',
        'book/coverage/checks/root_prepare_pages26_config_v1.py','book/coverage/checks/pages26-config-helper-independent-foundations-review-v1.json',
        'book/coverage/checks/root_prepare_pages26_config_v2.py','book/coverage/checks/pages26-config-helper-independent-modules-review-v2.json',
        'book/coverage/checks/root_stage_publication26_v2.py','book/coverage/checks/root_stage_publication26_delivery_metadata_v2.py',
        'book/coverage/checks/future26-core/publication26-stage-independent-review-v2.json',
        'book/coverage/checks/future26-core/publication26-delivery-metadata-stager-independent-foundations-review-v2.json',
        'book/coverage/checks/root_stage_publication26_v3.py','book/coverage/checks/root_stage_publication26_delivery_metadata_v3.py',
        'book/coverage/checks/future26-core/publication26-stage-independent-review-v3.json',
        'book/coverage/checks/future26-core/publication26-delivery-metadata-stager-independent-foundations-review-v3.json'}
    add_refs(doc,extra);add_refs(browser,extra);add_refs(manual,extra)
    for field in ('actual_execution','fresh_run_inputs'):
        n=browser[field];assert sha(safe(n))==browser[field+'_sha256'];extra.add(n)
    add_refs(read(browser['fresh_run_inputs']),extra)
    stems=('owner26-integration-dry-execution-v1','owner26-integration-apply-execution-v1',
        'root-source53-final-owner-integration26-execution-v1','prepare-checkpoint26-selection-execution-v1',
        'root-independent-selection26-output-execution-v1','freeze-checkpoint26-execution-v1',
        'prepare-checkpoint26-cache-execution-v1','verify-checkpoint26-execution-v1','export-checkpoint26-execution-v1',
        'export-integrity-checkpoint26-execution-v1','frozen-ledger-checkpoint26-execution-v1','static-checkpoint26-execution-v1',
        'prepare-documentation26-execution-v1','prepare-publication26-execution-v1','publication26-ledger-check-execution-v1',
        'prepare-browser26-execution-v1','pages26-config-execution-v1')
    closed={}
    for stem in stems:
        n='reports/full-coverage/'+stem+'.json';d,log=actual(n);extra.update([n,log]);closed[n]=sha(safe(n));closed[log]=sha(safe(log))
        if stem=='pages26-config-execution-v1':
            assert d['actual_command']==['python3',CONFIG_HELPER]
            assert d['helper_sha256_before']==d['helper_sha256_after']=={CONFIG_HELPER:CONFIG_HELPER_SHA}
    for n in [PEER,CONFIG_CODE_PEER,CONFIG_OUTPUT_PEER,ROOT_OUTPUT,MODULE_OUTPUT,BROWSER_CODE_PEER,BROWSER_OUTPUT_PEER,DOC_PEER]:
        peer=peer_evidence(n,extra)
        if n==PEER:assert peer['helper_sha256']==sha(Path(__file__))
        if n==CONFIG_CODE_PEER:assert peer['helper_sha256']==CONFIG_HELPER_SHA
        if n==BROWSER_CODE_PEER:assert peer['helper_sha256']==BROWSER_HELPER_SHA
        if n==DOC_PEER:assert peer['helper_sha256']==DOC_HELPER_SHA
        if n==CONFIG_OUTPUT_PEER:assert peer['config_sha256']==config['config_sha256'] and peer['excluded_count']==116
        if n==BROWSER_OUTPUT_PEER:
            assert peer['browser_report']=={'file':browser_name,'sha256':sha(safe(browser_name))}
            assert peer['fresh_run_inputs']=={'file':browser['fresh_run_inputs'],'sha256':browser['fresh_run_inputs_sha256']}
            preparation_name='reports/full-coverage/prepare-browser26-execution-v1.json'
            assert peer['actual_execution']=={'file':preparation_name,'sha256':sha(safe(preparation_name))}
            preparation,preparation_log=actual(preparation_name)
            assert preparation['actual_command']==['python3',BROWSER_HELPER]
            assert preparation['helper_sha256_before']==preparation['helper_sha256_after']=={BROWSER_HELPER:BROWSER_HELPER_SHA}
            fresh_capture,fresh_capture_log=actual(browser['actual_execution'])
            assert sha(safe(browser['actual_execution']))==browser['actual_execution_sha256']
            extra.update([preparation_name,preparation_log,browser['actual_execution'],fresh_capture_log])
        if n in {ROOT_OUTPUT,MODULE_OUTPUT}:assert peer['selection']=={'file':selection_name,'sha256':sha(safe(selection_name))}
        if n==ROOT_OUTPUT:
            assert peer['status']=='passed_independent_root_actual_selection26_output_review'
            assert (peer['selected_proof_sources'],peer['public_theorems'],peer['new_sources'])==(1167,9503,11)
            assert peer['actual_checker']=={'file':ROOT_CHECKER,'sha256':ROOT_CHECKER_SHA}
            add_refs(peer['actual_checker'],extra)
    failed_name='reports/full-coverage/stage-publication26-execution-v1.json'
    failed,failed_log=actual(failed_name,code=1)
    old_helper='book/coverage/checks/root_stage_publication26_v3.py'
    assert failed['actual_command']==['python3',old_helper]
    assert failed['helper_sha256_before']==failed['helper_sha256_after']=={old_helper:'1e2a97f4576e197fcb3eb99a39017b97131800a200b9f6c1dd55cfaed8606f21'}
    assert failed['log_sha256']=='54dd53010c9b2d2c7cdd7716a9aa4f2fb948687547bb1bd2bc3f0fe9df9effd0'
    extra.update([failed_name,failed_log])
    retained_failure={n:sha(safe(n)) for n in (failed_name,failed_log)}
    expected={}
    for n in extra:
        assert not n.startswith('verification/lean/'),n
        p=safe(n);assert p.is_file() and not p.is_symlink();expected[n]=sha(p)
    paths.update(extra);paths.update(['_config.yml',REPORT])
    assert dirty()<=paths and staged()<=paths,sorted(dirty()-paths)
    record={'status':'passed_explicit_audited_checkpoint26_publication_whitelist_ready_to_stage',
        'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':sha(Path(__file__)),
        'selection_sha256':sha(safe(selection_name)),'manifest_sha256':sha(safe(manifest_name)),
        'sources':1167,'public_theorems':9503,'new_sources':11,'source53_assets_sha256':assets,
        'config_sha256':config['config_sha256'],'staged_paths':sorted(paths),
        'additional_closed_paths_sha256':expected,'closed_actual_execution_evidence_sha256':closed,
        'retained_actual_stager3_prewrite_failure_sha256':retained_failure,
        'changed_paths_before_explicit_copy':sorted(dirty()),'coverage_complete':False,
        'publication_still_awaits_actual_commit_push_pages_and_live_checks':True,
        'historical_frozen_archive_scope':'All exact prior and current frozen inputs remain archival evidence. Unselected future proof trials add no26 verified coverage.'}
    exclusions=config['exclusions'];assert isinstance(exclusions,list) and len(exclusions)==len(set(exclusions))==116
    assert all(isinstance(n,str) and n and not Path(n).is_absolute() and '..' not in Path(n).parts and not any(c in n for c in ('\0','\n','\r','*','?','[','{')) for n in exclusions)
    kept=lambda n:not any(n==e or n.startswith(e+'/') for e in exclusions)
    included_now=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix()))
    replacements=sum(safe(n).stat().st_size-(target(n).stat().st_size if target(n).is_file() else 0) for n in expected if kept(n))
    record['included_website_bytes_before_explicit_copy']=included_now;record['included_closed_replacement_byte_delta']=replacements
    record_bytes=(json.dumps(record,indent=2)+'\n').encode();prospective=included_now+replacements+(len(record_bytes) if kept(REPORT) else 0)
    assert 0<=prospective<850_000_000,prospective
    for n,digest in expected.items():
        p=target(n);p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(safe(n),p)
        assert sha(safe(n))==sha(p)==digest,n
    assert all(target(n).is_file() for n in paths if n!=REPORT)
    with safe(REPORT).open('xb') as f:f.write(record_bytes)
    shutil.copyfile(safe(REPORT),target(REPORT))
    assert dirty()<=paths and staged()<=paths
    payload=''.join(n+'\0' for n in sorted(paths)).encode()
    subprocess.run(['git','add','-f','--pathspec-from-file=-','--pathspec-file-nul'],cwd=PUB,input=payload,check=True)
    assert staged() and staged()<=paths
    for n,digest in expected.items():assert sha(target(n))==digest,n
    assert not subprocess.run(['git','diff','--name-only','-z'],cwd=PUB,check=True,capture_output=True).stdout
    print(json.dumps({'status':'passed','actual_staged_paths':len(staged()),'allowed_paths':len(paths),'coverage_complete':False}))

if __name__=='__main__':main()

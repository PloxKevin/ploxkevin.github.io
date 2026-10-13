"""Export exact successful Source91 audit evidence with original execution provenance."""
import copy
from datetime import datetime
import json
from pathlib import Path

import solution_review as review
import solution_release as release
import prepare_solution_runtime as runtime

OUTPUT='reports/solution-review/lean-source91-selected35-v1'
NATIVE='reports/solution-review/source91-lean-audit-execution-v1.json'


def main():
    preparation=review.read(runtime.REPORT)
    native=review.read(NATIVE)
    assert native['status']=='passed' and native['actual_exit_code']==0
    assert review.ref(native['log'])['sha256']==native['log_sha256']
    assert native['helper_sha256_before']==native['helper_sha256_after']
    expected_command=['python3','-B','verification/lean/verify.py','--reuse-kernel-from',
                      str(review.ROOT/runtime.PRIOR),'--output',
                      str(review.ROOT/runtime.RUNTIME/'reports/lean-verification')]
    assert native['actual_command']==expected_command, 'Receipt is not the intended selected-proof audit command'
    assert native['actual_workdir']==str(review.ROOT/runtime.RUNTIME), 'Receipt has a different audit workdir'
    required_inputs=[runtime.RUNTIME+'/verification/lean/'+n for n in
                     ['verify.py','SafeLearning.lean','lean-toolchain','lakefile.toml','lake-manifest.json']]
    required_inputs += [runtime.REPORT,release.PLAN,runtime.RUNTIME+'/book/coverage/lean_names.py']
    for name in required_inputs:
        assert native['helper_sha256_before'].get(name)==review.ref(name)['sha256'], 'Native audit input is unbound: '+name
    started=review.read(native['started_receipt'])
    assert review.ref(native['started_receipt'])['sha256']==native['started_receipt_sha256']
    assert started['actual_command']==expected_command and started['actual_workdir']==native['actual_workdir']
    directory=runtime.RUNTIME+'/reports/lean-verification'
    original=directory+'/verification.json';report=review.read(original)
    assert report['status']=='passed' and report['proof_file_count']==1267 and report['theorem_count']==11472
    assert datetime.fromisoformat(native['started_at_utc'])<=datetime.fromisoformat(report['verified_at_utc'])<=datetime.fromisoformat(native['finished_at_utc'])
    assert all(c['exit_code']==0 for c in report['checks'])
    assert report['source_sha256']==preparation['all31_site_source91_sha256']
    prior=review.read(release.PRIOR_AUDIT)
    assert report['proof_sha256']==prior['proof_sha256']
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in report['axiom_dependencies'].values())
    assert len(report['axiom_dependencies'])==11472
    for field in ('source_sha256','proof_sha256','project_sha256'):
        for name,fingerprint in report[field].items():
            assert review.ref(runtime.RUNTIME+'/'+name)['sha256']==fingerprint
    # Reject corrupted or missing bound logs before any immutable export file
    # is installed. A repaired source can then resume without stale bad copies.
    checked_logs={}
    for check in report['checks']:
        name=check['output_file']
        assert name.startswith('reports/lean-verification/')
        source=runtime.RUNTIME+'/'+name
        fingerprint=checked_logs.setdefault(source,review.ref(source)['sha256'])
        if 'log_sha256' in check:
            assert fingerprint==check['log_sha256'], 'Runtime check log differs: '+name
        reused=check.get('reused_from')
        if reused:
            name=reused['report'];assert name.startswith('reports/lean-verification/')
            source=runtime.RUNTIME+'/'+name
            if source not in checked_logs:checked_logs[source]=review.ref(source)['sha256']
            assert checked_logs[source]==reused['report_sha256'], 'Runtime reused report differs'
    staged=[]
    for source in sorted(review.path(directory).iterdir()):
        assert source.is_file() and not source.is_symlink()
        raw=source.read_bytes()
        name=source.relative_to(review.ROOT).as_posix()
        if name in checked_logs:assert review.sha(raw)==checked_logs[name]
        staged.append((source.name,raw))
    artifacts=[]
    # Copy just the verifier's flat evidence directory, never the runtime,
    # source objects, dependency caches, or any prior snapshot tree.
    for basename,raw in staged:
        name='verification-original.json' if basename=='verification.json' else basename
        target=OUTPUT+'/'+name;review.put(target,raw);artifacts.append(review.ref(target))
    relocated=copy.deepcopy(report)
    def relocate(check):
        name=check.get('output_file')
        if isinstance(name,str) and name.startswith('reports/lean-verification/'):
            check['output_file']=OUTPUT+'/'+name.removeprefix('reports/lean-verification/')
        reused=check.get('reused_from')
        if isinstance(reused,dict):
            name=reused.get('report')
            if isinstance(name,str) and name.startswith('reports/lean-verification/'):
                reused['report']=OUTPUT+'/'+name.removeprefix('reports/lean-verification/')
    for check in relocated['checks']:
        relocate(check)
        if 'module' in check:
            assert review.ref(check['output_file'])['sha256']==check['log_sha256']
    relocated['audit_origin']={'original_report':review.ref(OUTPUT+'/verification-original.json'),
                               'native_execution':review.ref(NATIVE),'actual_runtime':runtime.RUNTIME,
                               'relocation':'Only current report/log locations relocated; actual commands, workdirs and historical reuse ancestry remain as observed.'}
    relocated['html_to_proof_correspondence_for_rewritten_answers']='pending_explicit_rebase'
    review.json_put(OUTPUT+'/verification.json',relocated)
    artifacts.append(review.ref(OUTPUT+'/verification.json'))
    evidence={'status':'passed_actual_source91_selected35_build_kernel_and_all_axiom_audit_export',
              'helper':review.ref(Path(__file__).relative_to(review.ROOT).as_posix()),
              'native_execution':review.ref(NATIVE),'runtime_preparation':review.ref(runtime.REPORT),
              'original_native_report':review.ref(OUTPUT+'/verification-original.json'),
              'relocated_report':review.ref(OUTPUT+'/verification.json'),'artifacts':artifacts,
              'proof_files':1267,'public_theorems':11472,
              'fresh_kernel_modules':sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in report['checks']),
              'reused_identical_kernel_modules':sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in report['checks']),
              'fresh_build_and_all_theorem_axiom_audit':True,'formal_source_correspondence_rebase':'pending_for_rewritten_answers',
              'historical_checkpoint35_coverage_unchanged':True,'coverage_complete':False}
    review.json_put('reports/solution-review/source91-lean-audit-export-v1.json',evidence)
    print(json.dumps({'status':evidence['status'],'proof_files':1267,'public_theorems':11472,'report':review.ref('reports/solution-review/source91-lean-audit-export-v1.json')}))


if __name__=='__main__':
    main()

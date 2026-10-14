"""Export a genuine selected native audit, preserving all original provenance."""
import copy
import json
from datetime import datetime
from pathlib import Path
import common as c
import prepare_runtime as runtime

NATIVE='reports/full-coverage/source91-piece01/selected-audit-native-v1.json'
OUTPUT='reports/full-coverage/source91-piece01/lean-audit'
REPORT='reports/full-coverage/source91-piece01/audit-export-v1.json'


def main():
    plan=c.read(runtime.PLAN);preparation=c.read(runtime.REPORT);native=c.read(NATIVE)
    assert native['status']=='passed' and native['actual_exit_code']==0
    assert native['helper_sha256_before']==native['helper_sha256_after']
    assert c.ref(native['log'])['sha256']==native['log_sha256']
    assert c.ref(native['started_receipt'])['sha256']==native['started_receipt_sha256']
    command=['python3','-B','verification/lean/verify.py','--reuse-kernel-from',str(c.ROOT/runtime.PRIOR),
             '--output',str(c.ROOT/runtime.RUNTIME/'reports/lean-verification')]
    assert native['actual_command']==command and native['actual_workdir']==str(c.ROOT/runtime.RUNTIME)
    for name in [runtime.PLAN,runtime.REPORT]+[runtime.RUNTIME+'/'+n for n in
        ['verification/lean/verify.py','verification/lean/SafeLearning.lean','verification/lean/lean-toolchain',
         'verification/lean/lakefile.toml','verification/lean/lake-manifest.json','book/coverage/lean_names.py']]:
        assert native['helper_sha256_before'][name]==c.ref(name)['sha256']
    directory=runtime.RUNTIME+'/reports/lean-verification';original=directory+'/verification.json'
    original_raw=c.path(original).read_bytes()
    report=json.loads(original_raw)
    assert report['status']=='passed' and report['proof_file_count']==1271 and report['theorem_count']==11508
    assert datetime.fromisoformat(native['started_at_utc'])<=datetime.fromisoformat(report['verified_at_utc'])<=datetime.fromisoformat(native['finished_at_utc'])
    assert all(r['exit_code']==0 for r in report['checks'])
    assert report['source_sha256']==plan['site_source91_sha256']
    expected={r['target']:r['sha256'] for r in plan['files']}
    assert report['proof_sha256']=={n:h for n,h in expected.items() if n.startswith('verification/lean/SafeLearning/')}
    assert preparation['runtime_source_sha256']==expected
    assert len(report['axiom_dependencies'])==11508
    declared={r['name'] for r in report['declarations']}
    assert len(declared)==len(report['declarations'])==11508 and declared==set(report['axiom_dependencies'])
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in report['axiom_dependencies'].values())
    fresh={r['module'] for r in report['checks'] if r.get('evidence_mode')=='fresh_kernel_replay'}
    assert fresh=={'SafeLearning.'+n for n in runtime.ADDITIONS}
    assert sum(r.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for r in report['checks'])==1267
    for field in ['proof_sha256','source_sha256','project_sha256']:
        for name,h in report[field].items():assert c.ref(runtime.RUNTIME+'/'+name)['sha256']==h
    checked={'reports/lean-verification/verification.json':c.sha(original_raw)}
    for row in report['checks']:
        name=row['output_file'];assert name.startswith('reports/lean-verification/')
        checked[name]=c.ref(runtime.RUNTIME+'/'+name)['sha256']
        if 'log_sha256' in row:assert checked[name]==row['log_sha256']
        if row.get('reused_from'):
            r=row['reused_from'];name=r['report'];assert name.startswith('reports/lean-verification/')
            observed=c.ref(runtime.RUNTIME+'/'+name)['sha256']
            assert observed==r['report_sha256']
            if name in checked:assert checked[name]==observed
            checked[name]=observed
    # Preflight every bound log before creating any immutable export copy.
    staged=[]
    for path in sorted(c.path(directory).iterdir()):
        assert path.is_file() and not path.is_symlink()
        raw=path.read_bytes();name=path.relative_to(c.ROOT/runtime.RUNTIME).as_posix()
        if name in checked:assert c.sha(raw)==checked[name]
        staged.append((path.name,raw))
    artifacts=[]
    for name,raw in staged:
        target=OUTPUT+'/'+('verification-original.json' if name=='verification.json' else name)
        c.put(target,raw);artifacts.append(c.ref(target))
    relocated=copy.deepcopy(report)
    for row in relocated['checks']:
        row['output_file']=OUTPUT+'/'+row['output_file'].removeprefix('reports/lean-verification/')
        if row.get('reused_from'):
            row['reused_from']['report']=OUTPUT+'/'+row['reused_from']['report'].removeprefix('reports/lean-verification/')
        if 'log_sha256' in row:assert c.ref(row['output_file'])['sha256']==row['log_sha256']
    relocated['audit_origin']={'original_report':c.ref(OUTPUT+'/verification-original.json'),
        'native_execution':c.ref(NATIVE),'actual_runtime':runtime.RUNTIME,
        'relocation':'Only current output/report paths changed; actual commands, workdirs and historical reuse ancestry remain as observed.'}
    relocated['source_correspondence']='Only the separately reviewed piece01 claims may be promoted; all other Source91 mappings remain pending.'
    c.json_put(OUTPUT+'/verification.json',relocated);artifacts.append(c.ref(OUTPUT+'/verification.json'))
    result={'status':'passed_actual_source91_piece01_selected_build_fresh4_kernel_and_all_axiom_audit_export',
        'helper':c.ref('book/coverage/source91-piece01/export_audit.py'),'native_execution':c.ref(NATIVE),
        'runtime_preparation':c.ref(runtime.REPORT),'runtime_plan':c.ref(runtime.PLAN),
        'original_native_report':c.ref(OUTPUT+'/verification-original.json'),'relocated_report':c.ref(OUTPUT+'/verification.json'),
        'proof_files':1271,'public_theorems':11508,'fresh_kernel_modules':4,'exact_prior_kernel_reuses':1267,
        'fresh_build_and_all_theorem_axiom_audit':True,'artifacts':artifacts,'formal_coverage_complete':False}
    c.json_put(REPORT,result)
    print({'status':result['status'],'report':c.ref(REPORT)})


if __name__=='__main__':main()

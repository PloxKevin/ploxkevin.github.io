from pathlib import Path
from datetime import datetime,timezone
import argparse,ast,json,hashlib,sys,time,importlib.util,traceback
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
RUNTIME=ROOT/'reports/full-coverage/runtime-checkpoint-31-source81-v1'
ORIGINAL=RUNTIME/'reports/lean-verification'
OUT=Path('/tmp/applied31-export-freeze31-readonly-review-v1')
HELPERS={'book/coverage/export_runtime_audit31_v1.py':'fb038ecb465215ce3e9f3a9eb51840da311d4ef6517ad16472aed88c134bba1b','book/coverage/freeze_checkpoint31_source_only_v1.py':'6c1190af9991ddaa076502018da0a311c1c756ecf9bd3d56e2c69764fe8bcef3'}
SELECTION='reports/full-coverage/checkpoint-31-selection.json'
SELECTION_SHA='cfe49bb94bf13fe8e464df60213a6639ffb99e63383f2f9300b93ef8a21d33da'
AUDIT_SHA='91e60eb646bc337f09bbab93631cdbf73f67fb5affb5b11da397ad0b8bf4c344'
INTEGRATION='reports/full-coverage/owner31-reviewed-candidate-integration-v4.json'
LEDGER='reports/full-coverage/lean-checkpoint-31/ledger-audit-working-v1.json'
NATIVE='reports/full-coverage/verify-runtime-checkpoint31-source81-execution-v1.json'
UNSELECTED={'verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean','verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean','verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean'}
ap=argparse.ArgumentParser();ap.add_argument('--context',required=True);ap.add_argument('--context-sha256',required=True);args=ap.parse_args()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def real(n):p=Path(n);return p if p.is_absolute() else ROOT/p
def reference(p):
    p=real(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def load(p):return json.loads(real(p).read_bytes())
def guard(table):
    for n,h in table.items():assert sha(real(n))==h,n
def write(p,d):
    with p.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
assert not OUT.exists();OUT.mkdir()
start=datetime.now(timezone.utc);tick=time.monotonic();before={};errors=[];assessment={};helper_before=sha(Path(__file__))
try:
    cp=Path(args.context);assert sha(cp)==args.context_sha256
    context=load(cp);assert context['status']=='actual_source81_installed_owner31_selected31_audited_TMP_context_only'
    assert context['protected_selected31_proof_sources']==1248 and context['coverage_complete'] is False
    before={**context['pins_sha256'],**context['held_current_source_sha256'],**context['owners_sha256'],str(cp):args.context_sha256,**HELPERS}
    guard(before)
    trees={}
    for n,h in HELPERS.items():
        assert sha(ROOT/n)==h;trees[n]=ast.parse((ROOT/n).read_text(),filename=n)
    assert len((ROOT/next(iter(HELPERS))).read_text().splitlines())==92
    assert len((ROOT/'book/coverage/freeze_checkpoint31_source_only_v1.py').read_text().splitlines())==161
    # Only extract the pure relocation function; neither producer is imported or invoked.
    tree=trees['book/coverage/export_runtime_audit31_v1.py']
    node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='relocate')
    namespace={'old_prefix':'reports/lean-verification/','new_prefix':'reports/full-coverage/lean-checkpoint-31-source81-v1/'}
    exec(compile(ast.Module(body=[node],type_ignores=[]),'<pure relocate function only>','exec'),namespace)
    relocate=namespace['relocate']
    reportpath=ORIGINAL/'verification.json';assert sha(reportpath)==AUDIT_SHA
    report=load(reportpath);selection=load(SELECTION);assert sha(ROOT/SELECTION)==SELECTION_SHA
    assert report['status']=='passed' and report['proof_file_count']==len(report['proof_sha256'])==1248
    assert report['theorem_count']==len(report['declarations'])==len(report['axiom_dependencies'])==11184
    assert report['proof_sha256']=={n:r['sha256'] for n,r in selection['proof_files'].items()}
    assert set(report['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
    assert all(set(a)<=set(report['allowed_standard_axioms']) for a in report['axiom_dependencies'].values())
    checks=report['checks'];assert len(checks)==1251 and all(type(c['exit_code']) is int and c['exit_code']==0 for c in checks)
    fresh=[c for c in checks if c.get('evidence_mode')=='fresh_kernel_replay'];reuse=[c for c in checks if c.get('reused_from')]
    assert len(fresh)==6 and len(reuse)==1242
    for table in ['source_sha256','proof_sha256','project_sha256']:
        for n,h in report[table].items():
            assert sha(RUNTIME/n)==h
            if n!='verification/lean/SafeLearning.lean':assert sha(ROOT/n)==h
    native=load(NATIVE);assert native['status']=='passed' and type(native['actual_exit_code']) is int and native['actual_exit_code']==0
    assert native['actual_command']==['python3','reports/full-coverage/runtime-checkpoint-31-source81-v1/verification/lean/verify.py','--reuse-kernel-from',str(ROOT/'reports/full-coverage/runtime-checkpoint-30-final-css-v1')]
    assert native['actual_workdir']==str(ROOT)
    assert sha(ROOT/native['log'])==native['log_sha256']
    assert native['helper_sha256_before']==native['helper_sha256_after']=={'reports/full-coverage/runtime-checkpoint-31-source81-v1/verification/lean/verify.py':sha(RUNTIME/'verification/lean/verify.py')}
    reused_report_hashes={}
    for c in checks:
        p=RUNTIME/c['output_file'];assert p.is_file()
        if 'log_sha256' in c:assert sha(p)==c['log_sha256']
        changed=json.loads(json.dumps(c));relocate(changed)
        assert changed['command']==c['command'] and changed['elapsed_seconds']==c['elapsed_seconds'] and changed['exit_code']==c['exit_code']
        assert changed.get('actual_workdir')==c.get('actual_workdir')
        diff={k for k in c if c[k]!=changed[k]};assert diff<={'output_file','reused_from'}
        if c.get('reused_from'):
            old=c['reused_from'];new=changed['reused_from'];assert old['original_check']==new['original_check']
            assert {k for k in old if old[k]!=new[k]}<={'report'}
            original_report=RUNTIME/old['report']
            if old['report'] not in reused_report_hashes:reused_report_hashes[old['report']]=sha(original_report)
            assert reused_report_hashes[old['report']]==old['report_sha256']
            execution=old['original_check'];assert execution['command']==c['command'] and execution['elapsed_seconds']==c['elapsed_seconds'] and execution['exit_code']==c['exit_code']
            assert execution['log_sha256']==c['log_sha256']
    outputfiles=sorted(p for p in ORIGINAL.rglob('*') if p.is_file())
    assert all(not p.is_symlink() and '.lake' not in p.relative_to(ORIGINAL).parts for p in outputfiles)
    original_output_hashes={str(p.relative_to(ROOT)):sha(p) for p in outputfiles}
    before.update(original_output_hashes)
    for n in [INTEGRATION,LEDGER,NATIVE,native['log']]:before[n]=sha(ROOT/n)
    integration=load(INTEGRATION);ledger=load(LEDGER)
    assert integration['applied'] is True and integration['coverage_complete'] is False
    assert integration['new_canonical_files']==6 and integration['new_public_theorems']==104
    assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
    assert ledger['counts']['exercises']==556 and ledger['counts']['material_source_units']==12774
    for r in integration['exact_replacements']:assert sha(ROOT/r['destination'])==r['candidate']['sha256']
    assert ledger['inventory_sha256']==sha(ROOT/'book/coverage/inventory.json')
    for d in ledger['domains']:assert sha(ROOT/('book/coverage/'+d['domain']+'.json'))==d['ledger_sha256']
    files=set(report['proof_sha256'])|set(report['source_sha256'])|set(report['project_sha256'])
    files|={'book/coverage/'+n for n in ['inventory.json','material-corrections.json','core.json','foundations.json','applied.json','modules.json','applied-promotions.json','validate.py','lean_names.py']}
    sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
    public={r['name'] for n in report['proof_sha256'] for r in declarations((ROOT/n).read_text())}
    excluded={};owners=[]
    for domain in ['core','foundations','applied','modules']:
        owner=load('book/coverage/'+domain+'.json');owners.append(owner)
        for n,h in owner.get('chapter_fragment_sha256',{}).items():assert n.startswith('book/chapters/') and sha(ROOT/n)==h;files.add(n)
        claims=owner.get('material_claims',[])+[c for e in owner['exercises'] for c in e['claims']]
        assert all(set(c['lean_declarations'])<=public for c in claims)
        excluded[domain]=sorted(set(owner['proof_files'])-set(report['proof_sha256']))
        assert set(excluded[domain])==(UNSELECTED if domain=='applied' else set())
    generated='verification/lean/SafeLearning.lean'
    plan={n:reference(RUNTIME/n if n==generated else ROOT/n) for n in sorted(files)}
    assert not any('.lake' in Path(n).parts or 'checkpoint-' in n for n in files)
    assert len(report['source_sha256'])==31
    for n,r in plan.items():
        if n!=generated:before[n]=r['sha256']
    # Exact pruning simulation remains in memory; working/frozen owner files are never written.
    old=load('book/coverage/applied.json');pruned=json.loads(json.dumps(old));assert isinstance(old['proof_files'],dict)
    pruned['proof_files']={n:r for n,r in pruned['proof_files'].items() if n not in UNSELECTED}
    if 'proof_sha256' in pruned:pruned['proof_sha256']={n:h for n,h in pruned['proof_sha256'].items() if n not in UNSELECTED}
    assert set(old['proof_files'])-set(pruned['proof_files'])==UNSELECTED
    assert all(old[k]==pruned[k] for k in old if k not in ['proof_files','proof_sha256'])
    guard(before)
    assessment={'status':'passed_independent_export31_freeze31_full_code_actual_input_read_only_review','errors':[],'full_code_read':True,'reviewed_helpers':[reference(n) for n in HELPERS],'exact_source31_audit':reference(reportpath),'actual_Root_execution':reference(NATIVE),'installed_owner31_integration':reference(INTEGRATION),'actual_working_ledger':reference(LEDGER),'current_context':reference(cp),'proof_file_count':1248,'public_theorem_count':11184,'actual_check_count':1251,'fresh_kernel_modules':[c['module'] for c in fresh],'reused_original_kernel_checks':1242,'every_original_command_cwd_time_original_check_and_log_SHA_preserved_by_relocation':True,'all_actual_original_runtime_output_hashes':original_output_hashes,'source_only_copy_plan':plan,'excluded_exact_unreferenced_metadata':excluded,'pruned_owner_keeps_all_claims_histories_and_other_fields_unchanged':True,'entire_runtime_audit_report_and_all_output_byte_hashes_read':True,'exporter_freezer_or_snapshot_mutation_by_reviewer':False,'new_compiler_or_publication_by_reviewer':False,'coverage_complete':False,'scope':'Exact export fb038 and freeze6c119 plus audit91e60 and actual installed owner31. Only the pure relocation function is extracted; neither top-level exporter nor freezer main is imported/invoked. All actual1251 outputs and all planned source input hashes are checked, without copying old snapshot/cache trees or installing a snapshot.'}
except Exception as exc:
    errors.append(type(exc).__name__+': '+str(exc));traceback.print_exc()
finish=datetime.now(timezone.utc);elapsed=time.monotonic()-tick
if errors:assessment={'status':'failed_independent_export31_freeze31_read_only_review','errors':errors}
write(OUT/'assessment.json',assessment)
write(OUT/'inner-actual-reader.json',{'status':'passed' if not errors else 'failed','actual_exit_code':0 if not errors else 1,'actual_command':[sys.executable,str(Path(__file__)),*sys.argv[1:]],'actual_workdir':str(ROOT),'started_at_utc':start.isoformat(),'finished_at_utc':finish.isoformat(),'elapsed_seconds':elapsed,'helper_sha256_before':{str(Path(__file__)):helper_before},'helper_sha256_after':{str(Path(__file__)):sha(Path(__file__))},'protected_inputs_sha256_before':before,'protected_inputs_sha256_after':{n:sha(real(n)) for n in before},'protection_errors':errors,'scope':'Actual independent read-only reviewer; no compiler/exporter/freezer/producer invoked.'})
print(json.dumps({'status':'passed' if not errors else 'failed','errors':errors,'assessment':reference(OUT/'assessment.json'),'elapsed_seconds':elapsed}))
sys.exit(0 if not errors else 1)

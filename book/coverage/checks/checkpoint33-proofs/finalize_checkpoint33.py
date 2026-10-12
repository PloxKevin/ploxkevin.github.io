"""Export the actual runtime33 audit and freeze its selected source bytes.

Prepared from recovery32_finalize.py without changing any executed helper.
The default check stage writes nothing. Export/freeze require the genuine
passing audit, applied owner installation and every explicit input SHA256.
The source-only snapshot records the runtime execution; it invents no snapshot run.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, copy, hashlib, importlib.util, json, re, shutil, sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
RUNTIME = 'reports/full-coverage/runtime-checkpoint-33-source88-v1'
ORIGINAL = RUNTIME + '/reports/lean-verification'
EXPORT = 'reports/full-coverage/lean-checkpoint-33-source88-v1'
SNAPSHOT = 'reports/full-coverage/checkpoint-33'
MANIFEST = 'reports/full-coverage/checkpoint-33-manifest.json'
SELECTION = 'reports/full-coverage/checkpoint-33-selection.json'
PREPARATION = 'reports/full-coverage/checkpoint33-runtime-source88-preparation-v1.json'
INTEGRATION = 'reports/full-coverage/owner33-integration-v1.json'
LEDGER = 'reports/full-coverage/ledger33-working-v1.json'
NATIVE = 'reports/full-coverage/verify-runtime33-execution-v1.json'
FROZEN_LEDGER = 'reports/full-coverage/ledger33-frozen-source-only-v1.json'
BASELINE_SELECTION = 'reports/full-coverage/checkpoint-32-selection.json'
BASELINE_SELECTION_SHA = 'c45d7f80ed33c780af30bdf58792bd5fa24cb0019a4e3b05a821520f9d703bb4'
BASELINE_RUNTIME = 'reports/full-coverage/runtime-checkpoint-32-source81-recovery-v1'
READINESS = 'book/coverage/checks/checkpoint33-proofs/actual-reviewed33-seven-canonical-paired-readiness-v1.json'
READINESS_SHA = 'c4a570116a807043fec19351b5b082b862c7b37d6ede0583d9c75d79e6b0f8c6'
UNSELECTED_METADATA = {
 'verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean',
 'verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean',
 'verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def path(n):
    assert isinstance(n, str) and n and Path(n).as_posix() == n
    assert not Path(n).is_absolute() and not {'..', '.git', '.lake'}.intersection(Path(n).parts)
    assert not any(c in n for c in '\0\n\r')
    p = ROOT/n; assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(ROOT))
    return p
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(n): return {'file': n, 'sha256': sha(path(n))}
def read(n, expected=None):
    p = path(n)
    if expected is not None: assert sha(p) == expected, n
    return json.loads(p.read_bytes())
def exact(r):
    p = path(r['file']); assert sha(p) == r['sha256'], r['file']
    if 'bytes' in r: assert p.stat().st_size == r['bytes']
    return p
def write(n, d, compact=False):
    p = path(n); assert not p.exists(); p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('x') as f:
        f.write(json.dumps(d, separators=(',', ':') if compact else None,
                           indent=None if compact else 2, ensure_ascii=False)+'\n')

def verify_inputs(args):
    for key, value in vars(args).items():
        if key.endswith('_sha256'):
            assert re.fullmatch('[0-9a-f]{64}', value), key
    selection = read(SELECTION, args.selection_sha256)
    assert selection['proof_file_count'] == len(selection['proof_files']) == 1261
    assert selection['new_file_count'] == 7 and selection['expected_public_theorem_count_pending_actual_aggregate'] == 11345
    exact(selection['baseline_selection']); exact(selection['baseline_actual_passing_audit'])
    assert selection['baseline_selection']['file'] == BASELINE_SELECTION
    assert selection['baseline_selection']['sha256'] == BASELINE_SELECTION_SHA
    additions = json.loads(exact(selection['additions_plan']).read_bytes())
    assert additions['status'] == 'passed_reviewed_compiled_additions_ready_for_selection'
    assert additions['new_public_theorem_count'] == 78 and additions['new_file_count'] == len(additions['sources']) == 7
    assert len({r['key'] for s in additions['sources'] for r in s['conditionally_approved_whole_material']}) == 10
    exact(additions['independent_actual_source_application_review'])
    exact(additions['independent_cumulative_qualifier_review'])
    baseline = read(BASELINE_SELECTION, BASELINE_SELECTION_SHA)
    assert baseline['proof_file_count'] == len(baseline['proof_files']) == 1254
    assert all(selection['proof_files'][n]['sha256'] == r['sha256'] for n, r in baseline['proof_files'].items())
    baseline_audit = json.loads(exact(selection['baseline_actual_passing_audit']).read_bytes())
    assert baseline_audit['status'] == 'passed' and baseline_audit['proof_file_count'] == 1254
    assert baseline_audit['theorem_count'] == 11267
    assert baseline_audit['proof_sha256'] == {n: r['sha256'] for n, r in baseline['proof_files'].items()}
    plan = read(READINESS, READINESS_SHA)
    assert plan['status'] == 'passed_actual_reviewed33_seven_canonical_standalone_and_named_pairs_unselected'
    assert plan['errors'] == [] and plan['source_count'] == len(plan['sources']) == 7
    assert plan['public_theorem_count'] == 78 and plan['public_name_count'] == 93
    assert plan['actual_compiler_command_count'] == len(plan['actual_paired_records']) == 14
    new_sources = set(selection['proof_files']) - set(baseline['proof_files'])
    assert new_sources == {r['canonical_source'] for r in plan['sources']}
    whole_keys = {r['key'] for s in plan['sources'] for r in s['conditionally_approved_whole_material']}
    assert len(whole_keys) == 10 and 'primer-basics.html::node-922' not in whole_keys
    for source in plan['sources']:
        exact(source['canonical_source_ref'])
        assert selection['proof_files'][source['canonical_source']]['sha256'] == source['canonical_source_ref']['sha256']
        for peer in source['independent_source_peers']:
            exact(peer)
        exact(source['independent_narrow_wording_and_parser_peer'])
    for pair in plan['actual_paired_records']:
        native_pair = json.loads(exact(pair['actual_record']).read_bytes())
        assert native_pair['actual_exit_code'] == native_pair['exit_code'] == 0
        assert native_pair['source_sha256_before'] == native_pair['source_sha256_after'] == pair['source']['sha256']
        exact(pair['source']); exact(pair['raw_log']); exact(pair['source_snapshot'])
    preparation = read(PREPARATION, args.preparation_sha256)
    assert preparation['selection']['file'] == SELECTION and preparation['selection']['sha256'] == args.selection_sha256
    assert preparation['runtime'] == RUNTIME
    assert preparation['selected_source_count'] == 1261 and preparation['new_sources'] == 7 and preparation['new_theorems'] == 78
    assert preparation['copied_lake_build_artifact_count'] == preparation['copied_earlier_snapshot_tree_count'] == 0
    assert preparation['inventory']['file'] == 'book/coverage/inventory.json'
    assert preparation['inventory']['sha256'] == args.inventory_sha256
    source_application = json.loads(exact(preparation['source_application']).read_bytes())
    assert source_application['status'] == 'passed_exact_reviewed_corrections82_88_applied_owner_rebase_pending'
    assert [r['correction_id'] for r in source_application['applications']] == list(range(82, 89))
    assert source_application['final_inventory']['sha256'] == args.inventory_sha256
    assert source_application['independent_cumulative_review']['sha256'] == plan['independent_cumulative_qualifier_review']['sha256']
    exact(source_application['independent_cumulative_review'])
    assert preparation['unchanged_site_assets_from_actual_checkpoint32'] == 29
    assert set(preparation['changed_site_pages_reviewed_source88']) == set(source_application['source_pages']) == {'SafeLearning/primer-basics.html', 'SafeLearning/primer-linalg.html'}
    for source, r in source_application['source_pages'].items():
        exact(r)
        assert preparation['source_hashes'][source] == r['sha256']
    source_input_sha = hashlib.sha256(json.dumps(preparation['source_hashes'], sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    assert source_input_sha == args.source_input_sha256
    audit = read(ORIGINAL+'/verification.json', args.actual_report_sha256)
    assert audit['status'] == 'passed' and audit['proof_file_count'] == len(audit['proof_sha256']) == 1261
    assert audit['theorem_count'] == len(audit['declarations']) == len(audit['axiom_dependencies']) == 11345
    assert audit['proof_sha256'] == {n:r['sha256'] for n,r in selection['proof_files'].items()}
    assert len(audit['checks']) == 1264 and all(type(c['exit_code']) is int and c['exit_code'] == 0 for c in audit['checks'])
    fresh = [c for c in audit['checks'] if c.get('evidence_mode') == 'fresh_kernel_replay']
    reused = [c for c in audit['checks'] if c.get('reused_from')]
    assert len(fresh) == 7 and len(reused) == 1254
    assert {c['module'] for c in fresh} == {'SafeLearning.'+Path(r['canonical_source']).stem for r in plan['sources']}
    assert all(c['actual_workdir'] == str(path(RUNTIME+'/verification/lean')) for c in fresh)
    assert all(c['reused_from']['report_sha256'] == selection['baseline_actual_passing_audit']['sha256'] for c in reused)
    assert set(audit['allowed_standard_axioms']) == ALLOWED
    assert all(set(a) <= ALLOWED for a in audit['axiom_dependencies'].values())
    assert len(audit['source_sha256']) == 31
    generated = 'verification/lean/SafeLearning.lean'
    for table in ['proof_sha256','source_sha256','project_sha256']:
        for n,h in audit[table].items():
            assert sha(path(RUNTIME+'/'+n)) == preparation['source_hashes'][n] == h, n
            if n != generated: assert sha(path(n)) == h, n
    aggregate = '\n'.join('import SafeLearning.'+Path(n).stem for n in sorted(selection['proof_files']))+'\n'
    assert path(RUNTIME+'/'+generated).read_text() == aggregate
    native = read(NATIVE, args.execution_sha256)
    assert native['status'] == 'passed' and native['actual_exit_code'] == 0
    command = native.get('actual_command', native.get('command'))
    assert isinstance(command, list) and command[0] == 'python3'
    normalized = [x for x in command if x != '-B']
    assert normalized == ['python3',RUNTIME+'/verification/lean/verify.py','--reuse-kernel-from',str(path(BASELINE_RUNTIME))]
    assert native['actual_workdir'] == str(ROOT)
    raw_log = native.get('log', native.get('raw_log')); log_hash = native.get('log_sha256',native.get('raw_log_sha256'))
    if isinstance(raw_log, dict): exact(raw_log)
    else: assert sha(path(raw_log)) == log_hash
    if 'helper_sha256_before' in native:
        assert native['helper_sha256_before'] == native['helper_sha256_after']
        assert native['helper_sha256_before'][RUNTIME+'/verification/lean/verify.py'] == sha(path(RUNTIME+'/verification/lean/verify.py'))
    integration = read(INTEGRATION, args.integration_sha256)
    assert integration['applied'] is True and integration['coverage_complete'] is False
    replacements = integration['exact_replacements']
    destinations = [r['destination'] for r in replacements]
    required_owners = {'book/coverage/'+n+'.json' for n in ['foundations','applied','modules','core']}
    assert len(destinations) == len(set(destinations))
    assert required_owners <= set(destinations) <= required_owners | {'book/coverage/applied-promotions.json'}
    for r in replacements:
        exact(r['candidate'])
        assert sha(path(r['destination'])) == r['candidate']['sha256']
        assert r.get('applied', True) is True
    inventory_sha = sha(path('book/coverage/inventory.json'))
    assert inventory_sha == args.inventory_sha256
    ledger = read(LEDGER,args.ledger_sha256)
    assert ledger['integrity_status'] == 'passed' and ledger['errors'] == [] and ledger['mathematical_coverage_complete'] is False
    assert ledger['counts']['exercises'] == 556 and ledger['counts']['material_source_units'] == 12774
    assert ledger['counts']['material_review_statuses'] == {'reviewed':4851,'pending':7923}
    assert ledger['counts']['statuses']['exercise:complete_math'] == 536
    assert ledger['counts']['statuses']['exercise:partial'] == 8 and ledger['counts']['statuses']['exercise:pending'] == 12
    assert ledger['inventory_sha256'] == inventory_sha
    for d in ledger['domains']: assert d['ledger_sha256'] == sha(path('book/coverage/'+d['domain']+'.json'))
    return selection, audit, integration, ledger

def export_audit(args,audit):
    assert not path(EXPORT).exists()
    original = path(ORIGINAL)
    entries = list(original.rglob('*'))
    assert all(not p.is_symlink() for p in entries)
    files = sorted(p for p in entries if p.is_file())
    assert files and all(not {'.lake','.git'}.intersection(p.relative_to(original).parts) for p in files)
    hashes = {p.relative_to(original).as_posix():sha(p) for p in files}
    for c in audit['checks']:
        if 'log_sha256' in c:
            assert c['output_file'].startswith('reports/lean-verification/')
            assert hashes[c['output_file'].removeprefix('reports/lean-verification/')] == c['log_sha256']
    output = path(EXPORT); output.mkdir()
    for p in files:
        target = output/p.relative_to(original); target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(p,target); assert sha(target) == hashes[p.relative_to(original).as_posix()]
    (output/'verification.json').rename(output/'verification-original.json')
    assert sha(output/'verification-original.json') == args.actual_report_sha256
    def relocate(c):
        for table,key in [(c,'output_file'),(c.get('reused_from',{}),'report')]:
            value = table.get(key)
            if isinstance(value,str) and value.startswith('reports/lean-verification/'):
                table[key] = EXPORT+'/'+value.removeprefix('reports/lean-verification/')
    relocated = copy.deepcopy(audit)
    for c in relocated['checks']: relocate(c)
    relocated['audit_origin'] = {'original_report':EXPORT+'/verification-original.json','original_report_sha256':args.actual_report_sha256,'actual_workdir':str(path(RUNTIME+'/verification/lean')),'actual_Root_execution':ref(NATIVE),'source_only_runtime_preparation':ref(PREPARATION),'scope':'Only exported report/output locations are relocated. Original command, original_check, cwd, time and source identities remain unchanged. The source-only snapshot records the actual runtime execution, not a compiler run in the snapshot.'}
    (output/'verification.json').write_text(json.dumps(relocated,indent=2)+'\n')
    progress = output/'kernel-progress.json'
    if progress.exists():
        d = json.loads(progress.read_bytes())
        for c in d['checks'].values(): relocate(c)
        progress.write_text(json.dumps(d,indent=2)+'\n')
    assert hashes == {p.relative_to(original).as_posix():sha(p) for p in files}
    return hashes

def freeze(args,selection,audit,integration,ledger):
    exported_original = EXPORT+'/verification-original.json'
    assert sha(path(exported_original)) == args.actual_report_sha256
    assert not path(SNAPSHOT).exists() and not path(MANIFEST).exists() and not path(FROZEN_LEDGER).exists()
    files = set(audit['proof_sha256']) | set(audit['source_sha256']) | set(audit['project_sha256'])
    files |= {'book/coverage/'+n for n in ['inventory.json','material-corrections.json','core.json','foundations.json','applied.json','modules.json','applied-promotions.json','validate.py','lean_names.py']}
    owners = {}
    for domain in ['core','foundations','applied','modules']:
        owners[domain] = read('book/coverage/'+domain+'.json')
        for n,h in owners[domain].get('chapter_fragment_sha256',{}).items():
            assert n.startswith('book/chapters/') and sha(path(n)) == h; files.add(n)
    sys.path.insert(0,str(path('book/coverage')))
    spec = importlib.util.spec_from_file_location('checkpoint33_final_names',path('book/coverage/lean_names.py'))
    names = importlib.util.module_from_spec(spec); spec.loader.exec_module(names)
    public = {r['name'] for n in audit['proof_sha256'] for r in names.declarations(path(n).read_text())}
    excluded = {}
    for domain,owner in owners.items():
        for claim in owner.get('material_claims',[]) + [c for e in owner['exercises'] for c in e['claims']]:
            assert set(claim['lean_declarations']) <= public
        excluded[domain] = sorted(set(owner['proof_files'])-set(audit['proof_sha256']))
        assert set(excluded[domain]) == (UNSELECTED_METADATA if domain == 'applied' else set())
    generated = 'verification/lean/SafeLearning.lean'
    inputs = {n:sha(path(n)) for n in sorted(files) if n != generated}
    protected = {**inputs,SELECTION:args.selection_sha256,ORIGINAL+'/verification.json':args.actual_report_sha256,exported_original:args.actual_report_sha256,INTEGRATION:args.integration_sha256,LEDGER:args.ledger_sha256,NATIVE:args.execution_sha256,PREPARATION:args.preparation_sha256,READINESS:READINESS_SHA,BASELINE_SELECTION:BASELINE_SELECTION_SHA,str(Path(__file__).relative_to(ROOT)):sha(Path(__file__))}
    snapshot = path(SNAPSHOT); snapshot.mkdir()
    for n in sorted(files):
        source = path(RUNTIME+'/'+n) if n == generated else path(n)
        target = snapshot/n; target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(source,target)
        assert sha(target) == (audit['project_sha256'][n] if n == generated else inputs[n])
    frozen_applied = snapshot/'book/coverage/applied.json'; applied = json.loads(frozen_applied.read_bytes())
    assert isinstance(applied['proof_files'],dict)
    applied['proof_files'] = {n:r for n,r in applied['proof_files'].items() if n not in UNSELECTED_METADATA}
    if 'proof_sha256' in applied: applied['proof_sha256'] = {n:h for n,h in applied['proof_sha256'].items() if n not in UNSELECTED_METADATA}
    assert applied['exercises'] == owners['applied']['exercises'] and applied['material_claims'] == owners['applied']['material_claims']
    frozen_applied.write_text(json.dumps(applied,indent=2)+'\n')
    spec = importlib.util.spec_from_file_location('checkpoint33_frozen_validator',path('book/coverage/validate.py'))
    validator = importlib.util.module_from_spec(spec); spec.loader.exec_module(validator); validator.ROOT = snapshot
    frozen_audit = validator.validate()
    assert frozen_audit['integrity_status'] == 'passed' and frozen_audit['errors'] == [] and frozen_audit['mathematical_coverage_complete'] is False
    assert frozen_audit['counts'] == ledger['counts']
    write(FROZEN_LEDGER,frozen_audit)
    assert protected == {n:sha(path(n)) for n in protected}
    entries = list(snapshot.rglob('*')); assert all(not p.is_symlink() for p in entries)
    frozen = {p.relative_to(snapshot).as_posix():sha(p) for p in entries if p.is_file()}
    assert set(frozen) == files and not any({'.lake','.git'}.intersection(Path(n).parts) for n in frozen)
    assert len([n for n in frozen if n.startswith('SafeLearning/')]) == 31
    assert all(frozen[n] == h for table in ['proof_sha256','source_sha256','project_sha256'] for n,h in audit[table].items())
    manifest = {
        'status': 'formal_verification_passed_partial_coverage',
        'created_at_utc': datetime.now(timezone.utc).isoformat(),
        'snapshot': SNAPSHOT, 'selection': SELECTION,
        'selection_sha256': args.selection_sha256,
        'proof_files': selection['proof_files'],
        'working_inputs_sha256': inputs, 'frozen_inputs_sha256': frozen,
        'inventory_sha256': args.inventory_sha256,
        'audited_runtime_source_input_sha256': args.source_input_sha256,
        'source_input_sha256_encoding': 'sha256(JSON source_hashes sorted keys, compact separators, UTF-8)',
        'coverage_complete': False, 'source_only_snapshot': True,
        'old_snapshot_or_lake_tree_copied': False,
        'new_whole_material_units': 10,
        'material_review_statuses': ledger['counts']['material_review_statuses'],
        'excluded_unreferenced_ledger_metadata': excluded,
        'owner_integration': ref(INTEGRATION),
        'working_ledger_audit': ref(LEDGER), 'frozen_ledger_audit': ref(FROZEN_LEDGER),
        'successful_verification': {
            'report': exported_original, 'report_sha256': args.actual_report_sha256,
            'actual_Root_execution': ref(NATIVE),
            'actual_workdir': str(path(RUNTIME+'/verification/lean')),
            'snapshot_execution_claimed': False, 'proof_files': 1261,
            'public_theorems': 11345, 'fresh_kernel_replays': 7,
            'exact_reused_kernel_checks': 1254,
        },
        'historical_provenance_not_recopied': {
            'baseline_selection': selection['baseline_selection'],
            'baseline_actual_audit': selection['baseline_actual_passing_audit'],
            'scope': 'Earlier original bodies/native records retain original paths, hashes and JSON pointers. No earlier snapshot, runtime cache symlink or recursive evidence archive is copied.',
        },
        'limits': [
            'Exercise and material coverage remain partial.',
            'Lean checked the encoded statements; independent source reviews establish correspondence.',
            'The exact selected Lean/site/project bytes were audited in runtime-checkpoint-33-source88-v1 before this source-only copy.',
            'Only three unused Applied proof metadata entries are omitted from the frozen ledger; every exercise and material claim is preserved.',
            'Node922 linked algorithm obligations and general Filippov local existence remain pending.',
        ],
    }
    write(MANIFEST,manifest,compact=True)
    return manifest

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--actual-report-sha256',required=True)
    parser.add_argument('--execution-sha256',required=True)
    parser.add_argument('--selection-sha256',required=True)
    parser.add_argument('--preparation-sha256',required=True)
    parser.add_argument('--integration-sha256',required=True)
    parser.add_argument('--ledger-sha256',required=True)
    parser.add_argument('--inventory-sha256',required=True)
    parser.add_argument('--source-input-sha256',required=True,
                        help='SHA256 of preparation.source_hashes encoded as sorted compact JSON, UTF-8.')
    parser.add_argument('--stage',choices=['check','all','export','freeze'],default='check')
    args = parser.parse_args()
    selection,audit,integration,ledger = verify_inputs(args)
    if args.stage in ['all','export']: export_audit(args,audit)
    manifest = freeze(args,selection,audit,integration,ledger) if args.stage in ['all','freeze'] else None
    status = ('passed_actual_runtime33_finalize_input_gates_no_mutations' if args.stage == 'check'
              else 'actual_runtime33_audit_exported_and_source_only_frozen' if manifest
              else 'actual_runtime33_audit_exported_original_provenance_preserved')
    print(json.dumps({'status':status,'proof_files':1261,'public_theorems':11345,
                      'fresh_kernels':7,'exact_reused_kernels':1254,
                      'new_whole_material_units':10,
                      'exported_original':ref(EXPORT+'/verification-original.json') if args.stage != 'check' else None,
                      'manifest':ref(MANIFEST) if manifest else None,
                      'coverage_complete':False},indent=2))

if __name__ == '__main__': main()

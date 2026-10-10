"""Run bounded, actual single-module kernel commands for verifier resumption.

Does not alter the frozen verifier, source inputs, or existing execution logs.
The original verifier must subsequently resume, rebuild, and audit all axioms.
"""
from pathlib import Path
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor, as_completed
import ast, hashlib, json, subprocess, time

ROOT = Path(__file__).resolve().parents[3]
SNAPSHOT = ROOT / 'reports/full-coverage/checkpoint-19'
PROJECT = SNAPSHOT / 'verification/lean'
OUT = SNAPSHOT / 'reports/lean-verification'
PROGRESS = OUT / 'kernel-progress.json'
LOGS = OUT / 'kernel-parallel19'
EXECUTION = ROOT / 'reports/full-coverage/parallel-kernel19-execution.json'
WORKERS = 4

def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()

def now():
    return datetime.now(timezone.utc).isoformat()

def write_new(path, value):
    assert not path.exists(), path
    path.write_text(json.dumps(value, indent=2)+'\n')

def environment_identity(reference):
    manifest = json.loads((PROJECT / 'lake-manifest.json').read_text())
    tree = ast.parse((PROJECT / 'verify.py').read_text())
    functions = [n for n in tree.body if isinstance(n, ast.FunctionDef)
                 and n.name in {'sha', 'dependency_environment'}]
    assert len(functions) == 2
    namespace = dict(PROJECT=PROJECT, manifest=manifest, subprocess=subprocess,
                     hashlib=hashlib)
    exec(compile(ast.Module(body=functions, type_ignores=[]), str(PROJECT / 'verify.py'), 'exec'), namespace)
    revisions = []
    for package in manifest['packages']:
        assert package['type'] == 'git'
        actual = subprocess.check_output(['git', '-C', str(PROJECT / manifest['packagesDir'] / package['name']),
                                          'rev-parse', 'HEAD'], text=True).strip()
        assert actual == package['rev']
        revisions.append(dict(name=package['name'], revision=actual))
    result = dict(input_sha256={name: sha(SNAPSHOT / name) for name in reference['input_sha256']},
        dependency_revisions=revisions,
        lean_version=subprocess.check_output(['lean', '--version'], cwd=PROJECT, text=True).strip(),
        dependency_environment_identity=namespace['dependency_environment']())
    assert result == reference, 'Frozen kernel identity changed'
    return result

def run(module):
    log = LOGS / ('kernel-' + module.replace('.', '-') + '.log')
    assert not log.exists(), log
    command = ['lake', 'env', 'leanchecker', '-v', module]
    started_at = now()
    started = time.monotonic()
    with log.open('wb') as output:
        result = subprocess.run(command, cwd=PROJECT, stdout=output, stderr=subprocess.STDOUT)
    return dict(command=command, exit_code=result.returncode,
        elapsed_seconds=round(time.monotonic()-started, 3),
        output_file=str(log.relative_to(SNAPSHOT)), module=module,
        log_sha256=sha(log), evidence_mode='fresh_kernel_replay',
        actual_workdir=str(PROJECT), started_at_utc=started_at, finished_at_utc=now(),
        execution_origin='actual_single_module_command_from_bounded_parallel_helper',
        execution_helper=str(Path(__file__).relative_to(ROOT)), execution_helper_sha256=sha(Path(__file__)))

def main():
    assert not EXECUTION.exists() and not LOGS.exists()
    progress = json.loads(PROGRESS.read_text())
    identity = environment_identity(progress['identity'])
    for module, record in progress['checks'].items():
        assert record['exit_code'] == 0 and record['module'] == module
        assert sha(SNAPSHOT / record['output_file']) == record['log_sha256']
    current = json.loads((ROOT / 'reports/full-coverage/checkpoint-19-selection.json').read_text())
    baseline = json.loads((ROOT / 'reports/full-coverage/checkpoint-18-selection.json').read_text())
    assert len(current['proof_files']) == 1055 and len(baseline['proof_files']) == 490
    new = sorted(set(current['proof_files']) - set(baseline['proof_files']))
    assert len(new) == 565
    modules = ['SafeLearning.' + Path(name).stem for name in new]
    modules = [module for module in modules if module not in progress['checks']]
    LOGS.mkdir()
    before = sha(Path(__file__))
    started_at, started = now(), time.monotonic()
    records = []
    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        futures = {pool.submit(run, module): module for module in modules}
        for future in as_completed(futures):
            record = future.result()
            records.append(record)
            write_new(LOGS / (record['module'].replace('.', '-')+'.json'), record)
            if record['exit_code'] == 0:
                progress['checks'][record['module']] = record
                temporary = PROGRESS.with_suffix('.parallel-tmp')
                temporary.write_text(json.dumps(progress, indent=2)+'\n')
                temporary.replace(PROGRESS)
            print(f"Actual kernel exit {record['exit_code']}: {record['module']} ({len(records)}/{len(modules)})", flush=True)
    after_identity = environment_identity(identity)
    passed = before == sha(Path(__file__)) and all(r['exit_code'] == 0 for r in records)
    write_new(EXECUTION, dict(status='actual_parallel_kernel_commands_passed_requires_original_verifier_resume' if passed else 'failed',
        actual_exit_code=0 if passed else 1, actual_command=['python3', str(Path(__file__).relative_to(ROOT))],
        actual_workdir=str(ROOT), started_at_utc=started_at, finished_at_utc=now(),
        elapsed_seconds=time.monotonic()-started, worker_count=WORKERS,
        helper_sha256_before=before, helper_sha256_after=sha(Path(__file__)),
        identity_before=identity, identity_after=after_identity, checks=records,
        completed_count=len(records), remaining_original_verifier_obligations=['actual resumed build', 'all public theorem axiom audit', 'final input and dependency fingerprint guard'],
        coverage_complete=False))
    raise SystemExit(0 if passed else 1)

if __name__ == '__main__':
    main()

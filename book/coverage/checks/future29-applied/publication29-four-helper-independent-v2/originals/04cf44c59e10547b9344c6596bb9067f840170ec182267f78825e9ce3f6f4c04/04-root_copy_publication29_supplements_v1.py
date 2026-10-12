"""Copy a bounded explicit set of genuine29 evidence; the frozen manifest stays unchanged."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
import root_prepare_checkpoint29_documents_v1 as docs

ROOT = docs.ROOT
PUB = ROOT/'reports/book/publication-repo'
OUT = 'reports/full-coverage/publication29-supplementary-copies-v1.json'
SUCCESS = {
    **docs.EXECUTIONS,
    'prepare-documents29-execution-v1': ['python3', 'book/coverage/checks/root_prepare_checkpoint29_documents_v1.py'],
    'prepare-publication29-execution-v1': ['python3', 'book/coverage/prepare_publication.py', '29']}
EXPLICIT_RECORDS = [
    'source61-64-contract-preparation29-execution-v1', 'source61-64-corrections-application29-execution-v1',
    'source65-readiness29-execution-v1', 'source65-correction-application29-execution-v1',
    'owner29-binding-preparation-execution-v1', 'owner29-reviewed-candidate-preflight-execution-v1',
    'owner29-reviewed-candidate-integration-execution-v1', 'root-source65-final-owner-integration29-execution-v1',
    'current65-canonical-plan10-preparation29-execution-v1', 'current65-canonical-pairs10-readiness29-execution-v1',
    'current65-canonical-pairs10-application29-execution-v1', 'monitoring29-canonical-plan-preparation-execution-v1',
    'current65-monitoring29-canonical-pair-application-execution-v1',
    'browser29-source65-helper-execution-v1', 'browser29-source65-helper-execution-v2',
    'browser-source65-29-v2-execution', 'browser29-evidence-merge-execution-v1',
    'source65-four-page-math-scroll29-execution-v1', 'source65-four-page-math-scroll29-execution-v2',
    'selection29-plan-preparation-execution-v1', 'selection29-plan-preparation-execution-v2',
    'selection29-preflight-execution-v1', 'selection29-preflight-execution-v2',
    'selection29-application-execution-v1', 'freeze-checkpoint29-execution-v1', 'prepare-cache29-execution-v1']
EXPLICIT_FILES = [
    'book/coverage/progress.json', 'reports/full-coverage/README.md',
    'reports/full-coverage/checkpoint29-document-preparation-v1.json',
    'reports/full-coverage/progress-checkpoint29-before-preparation-original-v1.json',
    'reports/full-coverage/readme-checkpoint29-before-preparation-original-v1.md',
    'reports/full-coverage/checkpoint29-cache-preparation.json',
    'reports/full-coverage/root-source65-final-owner-integration29-v1.json',
    'reports/full-coverage/owner29-reviewed-candidate-integration-v1.json',
    'reports/full-coverage/integration-29-source65-static-v1.json',
    'reports/full-coverage/browser-source65-29-v2-inputs.json',
    'reports/full-coverage/browser-source65-29-v2.json',
    'reports/full-coverage/browser-checkpoint-29.json',
    'reports/full-coverage/browser-corrections-29-inputs.json',
    'reports/full-coverage/source65-eight-captured-regions-manual-review29-v1.json',
    'reports/full-coverage/source65-four-page-math-scroll29-v1.json',
    'reports/full-coverage/source65-four-page-math-scroll29-v2.json',
    'book/coverage/checks/root_prepare_checkpoint29_documents_v1.py',
    'book/coverage/checks/root_copy_publication29_supplements_v1.py',
    'book/coverage/checks/root_prepare_publication29_stage_plan_v1.py',
    'book/coverage/checks/root_stage_publication29_v1.py',
    'book/coverage/checks/root_record_actual29_v1.py',
    'book/coverage/checks/root_check_export29_integrity_v1.py',
    'book/coverage/checks/root_prepare_browser29_v1.py',
    'book/coverage/checks/root_browser_source65_run29_v1.py',
    'book/coverage/checks/root_browser_source65_run29_v2.py',
    'book/coverage/checks/root_check_math_scroll29_v1.mjs',
    'book/coverage/checks/root_check_math_scroll29_v2.mjs',
    'book/coverage/checks/root_prepare_selection29_plan_v1.py',
    'book/coverage/checks/root_prepare_selection29_plan_v2.py',
    'book/coverage/prepare_checkpoint29_selection_v3.py',
    'book/coverage/prepare_checkpoint29_selection_v4.py',
    'book/coverage/checks/future29-core/checkpoint29-installed-owner-selection-plan-v1.json',
    'book/coverage/checks/future29-core/checkpoint29-installed-owner-selection-plan-v2.json']

def bind(paths, n, h=None):
    h = docs.sha(n) if h is None else h
    assert type(h) is str and len(h) == 64 and docs.sha(n) == h
    assert n not in paths or paths[n] == h
    assert docs.safe(ROOT, n).stat().st_size < 100_000_000
    paths[n] = h

def record(paths, n):
    d = docs.read(n)
    codes = [d[k] for k in ['actual_exit_code', 'exit_code', 'actual_runner_exit_code'] if k in d]
    assert codes and all(type(v) is int and v == codes[0] for v in codes)
    assert d['status'] == ('passed' if codes[0] == 0 else 'failed')
    docs.aliases(d, ['actual_command', 'command'], True, list)
    docs.aliases(d, ['actual_workdir', 'cwd', 'workdir', 'working_directory'], True, str)
    log = docs.aliases(d, ['log', 'raw_log'], True, str)
    h = docs.aliases(d, ['log_sha256', 'raw_log_sha256'], True, str)
    bind(paths, n)
    bind(paths, log, h)

def collect_closed(value, paths):
    if type(value) is dict:
        if set(value) == {'file', 'sha256'}:
            n, h = value['file'], value['sha256']
            if type(n) is str and not Path(n).is_absolute():
                bind(paths, n, h)
        for key, child in value.items():
            if key in ['closed_evidence_sha256', 'required_evidence_artifacts_sha256', 'reviewed_helpers_sha256'] and type(child) is dict:
                for n, h in child.items():
                    bind(paths, n, h)
            collect_closed(child, paths)
    elif type(value) is list:
        for child in value:
            collect_closed(child, paths)

def readiness():
    _, manifest, _, _, held = docs.readiness()
    for key, command in SUCCESS.items():
        docs.native('reports/full-coverage/'+key+'.json', command)
    assert all(not docs.safe(base, OUT).exists() for base in [ROOT, PUB])
    paths = {}
    for key in [*EXPLICIT_RECORDS, *SUCCESS]:
        record(paths, 'reports/full-coverage/'+key+'.json')
    for n in EXPLICIT_FILES:
        bind(paths, n)
    selection_plan = docs.read('book/coverage/checks/future29-core/checkpoint29-installed-owner-selection-plan-v2.json')
    peer_ref = selection_plan['independent_selection_helper_review']
    bind(paths, peer_ref['file'], peer_ref['sha256'])
    peer = docs.read(peer_ref['file'])
    assert peer['status'].startswith('passed_') and peer['errors'] == []
    collect_closed(peer, paths)
    for n in ['reports/full-coverage/browser-corrections-29-inputs.json', 'reports/full-coverage/source65-eight-captured-regions-manual-review29-v1.json']:
        d = docs.read(n)
        for r in d.get('screenshot_aliases', []) + d.get('inspected_captures', []):
            if 'original' in r:
                bind(paths, r['original'], r['sha256'])
                bind(paths, r['file'], r['sha256'])
            else:
                bind(paths, r['path'], r['sha256'])
    overrides = {'book/coverage/progress.json', 'reports/full-coverage/README.md'}
    for n, h in paths.items():
        target = docs.safe(PUB, n)
        if target.exists() and n not in overrides:
            assert docs.sha(n, PUB) == h, n
        if n in manifest['frozen_inputs_sha256'] and n not in overrides:
            assert h == manifest['frozen_inputs_sha256'][n], n
    assert all(docs.sha(n) == h for n, h in held.items())
    return paths, held

def main():
    paths, held = readiness()
    result = {'status': 'exact_explicit_publication29_supplementary_bytes_copied_delivery_pending',
        'copied_at_utc': datetime.now(timezone.utc).isoformat(), 'paths_sha256': dict(sorted(paths.items())),
        'coverage_complete': False,
        'scope': 'Bounded current29 native evidence including genuine prior failures, source65 browser/manual8/wheelv2 bytes and logs, and exact current documents. Supplemental files are not relabeled as frozen inputs; original commands, results, bodies and times remain unchanged.'}
    data = (json.dumps(result, separators=(',', ':'))+'\n').encode()
    assert len(data) < 100_000_000 and all(docs.sha(n) == h for n, h in paths.items())
    for n, h in paths.items():
        target = docs.safe(PUB, n)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(docs.safe(ROOT, n).read_bytes())
        assert docs.sha(n, PUB) == h
    assert all(docs.sha(n) == h for n, h in held.items())
    for base in [ROOT, PUB]:
        with docs.safe(base, OUT).open('xb') as f:
            f.write(data)
    print(json.dumps({'status': result['status'], 'paths': len(paths), 'report': docs.ref(OUT)}))

if __name__ == '__main__':
    main()

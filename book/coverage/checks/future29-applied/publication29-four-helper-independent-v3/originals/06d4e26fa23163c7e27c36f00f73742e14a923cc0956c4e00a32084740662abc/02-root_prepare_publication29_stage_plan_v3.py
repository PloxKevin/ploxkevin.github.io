"""Bind actual29 evidence and full reviewed helper bytes into an explicit publication plan."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json
import root_prepare_checkpoint29_documents_v1 as docs
import root_stage_publication29_v3 as stager

ROOT = docs.ROOT
PUB = ROOT/'reports/book/publication-repo'
DEST = 'book/coverage/checks/future29-core/root-explicit-audited29-publication-stage-plan-v3.json'
HELPERS = [
    'book/coverage/checks/root_prepare_checkpoint29_documents_v1.py',
    'book/coverage/checks/root_copy_publication29_supplements_v2.py',
    'book/coverage/checks/root_prepare_publication29_stage_plan_v3.py',
    'book/coverage/checks/root_stage_publication29_v3.py']
PREREQUISITES = {
    **docs.EXECUTIONS,
    'prepare-publication29-execution-v1': ['python3', 'book/coverage/prepare_publication.py', '29'],
    'publication29-ledger-check-execution-v1': ['python3', 'reports/book/publication-repo/book/coverage/validate.py', '--output', 'reports/full-coverage/publication-checks/ledger-checkpoint-29.json'],
    'prepare-documents29-execution-v1': ['python3', 'book/coverage/checks/root_prepare_checkpoint29_documents_v1.py']}

HISTORICAL_READONLY_INPUTS_SHA256 = {'book/coverage/checks/root_prepare_pages29_config_v1.py': 'a2713d6642553ce3e9f79df682557b53af19b141d7fef05e4a35eb06a9192f1e', 'book/coverage/checks/root_prepare_publication29_stage_plan_v2.py': '8ee29a85c1ee1c6f0d57ce30ab142c36261a5fd3a9c6338ec36be4a2c010bc6c', 'book/coverage/checks/root_stage_publication29_v2.py': '00d3f4d6dc06142fa1d23f4e1bc76535810fc3c08fc3443198762f171302ce18', 'reports/full-coverage/prepare-publication29-stage-plan-execution-v1.json': '307cb40ee26ad2ca9b138b7651a3eb78882bd37648a078ed777e74f2f59cc43b', 'reports/full-coverage/prepare-publication29-stage-plan-execution-v1.log': '23df068d451f5d1868f8be2129aec24a5fa94860cb9c1d57428fc223663395ae', 'reports/full-coverage/prepare-publication29-stage-plan-execution-v2.json': '7922881d54e15131cf8da39306d166ed211d611b41617131554b3792636ceb4d', 'reports/full-coverage/prepare-publication29-stage-plan-execution-v2.log': '16bd599b4ba4c93538f0276085ac084546cd0002cc6b44062684dea61641f524', 'reports/full-coverage/pages29-config-preparation-v1.json': '6560cc29d825b00ad8adcf8e66c8483fd25220e62cbb3504ea3a625dec58e0d5', 'reports/full-coverage/pages29-config-application-execution-v1.json': '8b2b63fc3fee4d3804e29c30d08078a16b7a9e4cabc6d2edb6297846a78278df', 'reports/full-coverage/pages29-config-application-execution-v1.log': '6677d18d73086eb51ac5e653ce16bd145a4c8e20a140cd0c1306b1211f57053d', 'reports/full-coverage/pages29-config-previous-original-v1.yml': '1f8ac723695777fc029ec267efab2141978b11f3c8b0604aebcfb9d9d953e7bd'}
DELIVERY_HELPER = 'book/coverage/checks/root_close_publication29_delivery_v4.py'

def bind(paths, n, h=None):
    h = docs.sha(n) if h is None else h
    assert type(h) is str and len(h) == 64 and docs.sha(n) == h
    assert n not in paths or paths[n] == h
    assert docs.safe(ROOT, n).stat().st_size < 100_000_000
    paths[n] = h

def peer(n, h):
    assert docs.sha(n) == h
    d = docs.read(n)
    assert d['errors'] == [] and d['status'].startswith('passed_')
    return d

def collect(value, paths):
    if type(value) is dict:
        if set(value) == {'file', 'sha256'}:
            n, h = value['file'], value['sha256']
            if type(n) is str and not Path(n).is_absolute():
                bind(paths, n, h)
        for key, child in value.items():
            if key in ['closed_evidence_sha256', 'required_evidence_artifacts_sha256', 'reviewed_helpers_sha256'] and type(child) is dict:
                for n, h in child.items():
                    bind(paths, n, h)
            collect(child, paths)
    elif type(value) is list:
        for child in value:
            collect(child, paths)

def main():
    ap = argparse.ArgumentParser()
    for kind in ['staging', 'pages', 'audit', 'delivery']:
        ap.add_argument('--'+kind+'-peer', required=True)
        ap.add_argument('--'+kind+'-peer-sha256', required=True)
    args = ap.parse_args()
    _, manifest, _, _, held = docs.readiness()
    assert stager.git(['rev-parse', 'HEAD']).stdout.decode().strip() == stager.HEAD
    assert all(not docs.safe(base, DEST).exists() for base in [ROOT, PUB])
    extra = dict(docs.read('reports/full-coverage/publication29-supplementary-copies-v2.json')['paths_sha256'])
    for n, h in HISTORICAL_READONLY_INPUTS_SHA256.items():
        bind(extra, n, h)
    for n in ['reports/full-coverage/prepare-publication29-stage-plan-execution-v1.json', 'reports/full-coverage/prepare-publication29-stage-plan-execution-v2.json']:
        historical = docs.read(n)
        assert historical['status'] == 'failed' and type(historical['actual_exit_code']) is int and historical['actual_exit_code'] == 1
        assert docs.sha(historical['log']) == historical['log_sha256']
    configuration = docs.read('reports/full-coverage/pages29-config-preparation-v2.json')
    config_helper = configuration['helper']
    assert config_helper['file'].startswith('book/coverage/checks/root_prepare_pages29_config_v') and config_helper['file'].endswith('.py')
    assert docs.sha(config_helper['file']) == config_helper['sha256']
    prerequisites = {}
    commands = {**PREREQUISITES, 'pages29-config-application-execution-v2': ['python3', config_helper['file'], '--apply']}
    for key, command in commands.items():
        n = 'reports/full-coverage/'+key+'.json'
        d = docs.native(n, command)
        prerequisites[key] = docs.ref(n)
        bind(extra, n)
        bind(extra, d['log'], d['log_sha256'])
    copy_n = 'reports/full-coverage/copy-publication29-supplements-execution-v1.json'
    copy_d = docs.native(copy_n, ['python3', 'book/coverage/checks/root_copy_publication29_supplements_v2.py'])
    bind(extra, copy_n)
    bind(extra, copy_d['log'], copy_d['log_sha256'])
    helpers = {n: docs.sha(n) for n in HELPERS}
    peers = {}
    for kind in ['staging', 'pages', 'audit', 'delivery']:
        n, h = getattr(args, kind+'_peer'), getattr(args, kind+'_peer_sha256')
        peers[kind] = peer(n, h)
        bind(extra, n, h)
        collect(peers[kind], extra)
    assert peers['staging']['reviewed_helpers_sha256'] == helpers
    assert peers['pages']['helper'] == config_helper
    assert peers['audit']['unchanged_exported_original_report'] == docs.ref(docs.AUDIT)
    assert peers['delivery']['helper'] == docs.ref(DELIVERY_HELPER)
    bind(extra, DELIVERY_HELPER)
    for n in [*HELPERS,
        'reports/full-coverage/publication29-supplementary-copies-v2.json',
        'reports/full-coverage/publication-checks/ledger-checkpoint-29.json',
        'reports/full-coverage/pages29-config-preparation-v2.json',
        'reports/full-coverage/pages29-config177-previous-original-v2.yml',
        'reports/full-coverage/publication-prepared-29-files.json',
        'reports/full-coverage/checkpoint-29/verification/lean/AxiomAudit.lean']:
        bind(extra, n)
    plan = {'status': 'explicit_actual_audited_checkpoint29_publication_plan', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'baseline_publication_head': stager.HEAD,
        'manifest': docs.ref('reports/full-coverage/checkpoint-29-manifest.json'),
        'selection': docs.ref('reports/full-coverage/checkpoint-29-selection.json'),
        'original_audit': docs.ref(docs.AUDIT),
        'prepared_file_list': docs.ref('reports/full-coverage/publication-prepared-29-files.json'),
        'actual_prerequisites': prerequisites,
        'publication_ledger': docs.ref('reports/full-coverage/publication-checks/ledger-checkpoint-29.json'),
        'configuration_preparation': docs.ref('reports/full-coverage/pages29-config-preparation-v2.json'),
        'helper_inputs_sha256': helpers,
        'independent_staging_helper_review': docs.ref(args.staging_peer),
        'independent_pages_helper_review': docs.ref(args.pages_peer),
        'independent_actual_audit_review': docs.ref(args.audit_peer),
        'independent_delivery_helper_review': docs.ref(args.delivery_peer),
        'original_failed_stage_plan_executions': [docs.ref('reports/full-coverage/prepare-publication29-stage-plan-execution-v'+str(i)+'.json') for i in [1, 2]],
        'original_pages29_configuration1_execution': docs.ref('reports/full-coverage/pages29-config-application-execution-v1.json'),
        'original_readonly_publication_history_sha256': HISTORICAL_READONLY_INPUTS_SHA256,
        'supplementary_paths_sha256': dict(sorted(extra.items())), 'coverage_complete': False}
    data = (json.dumps(plan, separators=(',', ':'))+'\n').encode()
    assert len(data) < 100_000_000
    exclusions = [line[4:] for line in docs.safe(PUB, '_config.yml').read_text().splitlines() if line.startswith('  - ')]
    assert len(exclusions) == len(set(exclusions)) == 177
    prospect = stager.website_size()
    for n, h in extra.items():
        assert docs.sha(n) == h
        target = docs.safe(PUB, n)
        if target.exists():
            assert docs.sha(n, PUB) == h, n
        if not any(n == e or n.startswith(e+'/') for e in exclusions) and not target.exists():
            prospect += docs.safe(ROOT, n).stat().st_size
    if not any(DEST == e or DEST.startswith(e+'/') for e in exclusions):
        prospect += len(data)
    assert prospect < 850_000_000 and all(docs.sha(n) == h for n, h in held.items())
    assert all(not docs.safe(base, DEST).exists() for base in [ROOT, PUB])
    for n, h in extra.items():
        target = docs.safe(PUB, n)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(docs.safe(ROOT, n).read_bytes())
        assert docs.sha(n, PUB) == h
    assert stager.website_size() < 850_000_000 and all(docs.sha(n) == h for n, h in held.items())
    for base in [ROOT, PUB]:
        with docs.safe(base, DEST).open('xb') as f:
            f.write(data)
    print(json.dumps({'status': plan['status'], 'plan': docs.ref(DEST), 'supplementary_paths': len(extra)}))

if __name__ == '__main__':
    main()

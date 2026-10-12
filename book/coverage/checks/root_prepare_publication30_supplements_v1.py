"""Build a bounded explicit publication map from closed current30 evidence."""
from pathlib import Path
import hashlib, json, re, shutil

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT / 'reports/book/publication-repo'
OUT = ROOT / 'reports/full-coverage/publication30-extra-inputs-v1.json'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(n):
    return json.loads((ROOT / n).read_bytes())


def safe(n):
    assert type(n) is str and n and Path(n).as_posix() == n
    assert not Path(n).is_absolute() and '..' not in Path(n).parts
    assert not any(p in {'.git', '.lake', '__pycache__'} or re.fullmatch(r'checkpoint-\d+', p) for p in Path(n).parts[:-1])
    p = ROOT / n
    assert p.is_file() and not p.is_symlink() and p.resolve().is_relative_to(ROOT)
    return p


assert not OUT.exists()
manifest = read('reports/full-coverage/checkpoint-30-manifest.json')
frozen = manifest['frozen_inputs_sha256']
assert manifest['status'] == 'formal_verification_passed_partial_coverage'
binding_name = 'book/coverage/checks/future30-core/owner30-integration-binding-v1/actual-root30-reviewed-candidates-bindings-v1.json'
assert sha(ROOT / binding_name) == 'fee2a388e29823ada29058993dfe74ef196161bfbda28ce404adace4708467d4'
binding = read(binding_name)
closure = {}


def add(n, h=None):
    p = safe(n)
    actual = sha(p)
    assert h is None or actual == h, n
    assert n not in closure or closure[n] == actual
    closure[n] = actual


def ref(r):
    add(r['file'], r['sha256'])


def table(d):
    for n, h in d.items():
        add(n, h)


def pointer(d, keys):
    for k in keys:
        d = d[k]
    return d


add(binding_name)
ref(binding['independent_helper_review'])
ref(binding['helper_review_actual_native'])
for r in binding['helper_review_original_TMP_aliases'].values():
    ref(r)
for r in binding['additional_immutable_inputs']:
    ref(r)
for s in binding['owners'].values():
    for k in ['candidate', 'reviewed_offer', 'final_mapping_peer', 'actual_mapping_native']:
        ref(s[k])
    offer = read(s['reviewed_offer']['file'])
    table(pointer(offer, s['offer_evidence_sha256_pointer']))
    peer = read(s['final_mapping_peer']['file'])
    table(peer.get('required_evidence_artifacts_sha256', {}))
    for r in s['mapping_original_TMP_aliases'].values():
        ref(r)
    for r in s['additional_exact_original_evidence']:
        ref(r)
    for c in s['companion_candidates']:
        ref(c['candidate'])
contract = read('book/coverage/checks/future30-core/source66-79-contract-v3/source66-79-fourteen-step-application-contract-v3.json')
for k, v in contract.items():
    if isinstance(v, dict) and k.endswith('sha256'):
        for n, h in v.items():
            if isinstance(h, str) and re.fullmatch('[0-9a-f]{64}', h) and (ROOT / n).is_file():
                add(n, h)
# Copy specific fresh evidence trees only. None is an earlier checkpoint tree.
directories = [
    'reports/full-coverage/lean-checkpoint-30',
    'reports/full-coverage/lean-checkpoint-30-final-css-v1',
    'reports/full-coverage/browser-artifacts-30',
    'reports/full-coverage/browser-artifacts-30-final',
    'reports/full-coverage/owner29-originals-before-owner30-integration-v2',
    'reports/full-coverage/source-history/approved-corrections66-79-20261012',
    'reports/full-coverage/source-history/source79-three-authoring-fragment-sync-v1',
    'reports/full-coverage/source-history/cmdp-mobile-inline-formula-style30-v1',
    'reports/full-coverage/source-history/documentation-before-checkpoint30-v1',
]
for d in directories:
    for p in (ROOT / d).rglob('*'):
        if p.is_file():
            add(p.relative_to(ROOT).as_posix())
for n in [
    'book/README.md', 'book/coverage/progress.json', 'verification/lean/README.md',
    'reports/full-coverage/README.md', 'reports/full-coverage/CLEANUP-2026-10-12.md',
    'reports/full-coverage/checkpoint-30-selection.json',
    'reports/full-coverage/checkpoint30-runtime-preparation-v1.json',
    'reports/full-coverage/checkpoint30-runtime-final-css-preparation-v1.json',
    'reports/full-coverage/owner30-reviewed-candidate-integration-v2.json',
    'reports/full-coverage/owner30-reviewed-candidate-isolated-preflight-v1.json',
    'reports/full-coverage/owner30-reviewed-candidate-isolated-apply-preflight-v1.json',
    'reports/full-coverage/source66-79-corrections-application-v3.json',
    'reports/full-coverage/source79-authoring-fragments-sync-v1.json',
    'reports/full-coverage/cmdp-mobile-inline-formula-style30-application-v1.json',
    'reports/full-coverage/checkpoint30-documentation-preparation-v1.json',
    'reports/full-coverage/integration-30-source79-v1.json',
    'reports/full-coverage/integration-30-source79-v2.json',
    'reports/full-coverage/integration-30-final-css-v1.json',
    'reports/full-coverage/browser-checkpoint-30-changed6-v1.json',
    'reports/full-coverage/browser-checkpoint-30-changed6-v2.json',
    'reports/full-coverage/cmdp-mobile-math30-v1.json',
    'qa/learning_review.mjs', 'qa/book_browser_checks.mjs', 'qa/cmdp_mobile_math30_v1.mjs',
    'book/coverage/prepare_publication30_source_only_v1.py',
    'book/coverage/prepare_publication30_source_only_v2.py',
    'book/coverage/prepare_publication30_source_only_v3.py',
    'book/coverage/freeze_checkpoint30_source_only_v1.py',
    'book/coverage/freeze_checkpoint30_source_only_v2.py',
    'book/coverage/export_runtime_audit30_v1.py', 'book/coverage/export_runtime_audit30_v2.py',
    'book/coverage/checks/root_prepare_publication30_supplements_v1.py',
    'book/coverage/checks/root_prepare_checkpoint30_documents_v1.py',
    'book/coverage/checks/root_apply_cmdp_mobile_style30_v1.py',
    'book/coverage/checks/root_record_actual29_v1.py',
    'book/coverage/checks/root_prepare_checkpoint30_runtime_v3.py',
    'book/coverage/checks/root_prepare_checkpoint30_runtime_v4.py',
]:
    add(n)
# Bind both failed and passing primary Root receipts, without changing them.
stems = [
    'current79-canonical-pairs45-application30-execution-v1',
    'current79-canonical-pairs45-readonly30-execution-v1',
    'current79-canonical-plan45-preparation30-execution-v1',
    'current79-canonical-plan45-preparation30-execution-v2',
    'proof-selection30-preparation-execution-v1',
    'source66-79-contract-preparation-execution-v1',
    'source66-79-contract-preparation-execution-v2',
    'source66-79-readonly-preflight-execution-v1',
    'source79-historical-owner29-context-preparation-execution-v1',
    'verify-runtime-checkpoint30-execution-v1', 'verify-runtime-checkpoint30-final-css-execution-v1',
    'export-runtime-checkpoint30-execution-v1', 'export-runtime-checkpoint30-final-css-execution-v1',
    'prepare-owner30-integration-binding-execution-v1', 'owner30-reviewed-candidate-preflight-execution-v1',
    'owner30-reviewed-candidate-application-execution-v1', 'owner30-global-ledger-execution-v1',
    'freeze-checkpoint30-source-only-execution-v1', 'frozen-ledger30-source-only-execution-v1',
    'static30-final-css-execution-v1', 'prepare-documents30-execution-v1',
    'browser30-changed6-execution-v1', 'browser30-changed6-execution-v2', 'cmdp-mobile-math30-execution-v1',
    'cmdp-mobile-style30-application-execution-v1', 'checkpoint30-runtime-preparation-execution-v1',
    'checkpoint30-runtime-final-css-preparation-execution-v1',
    'integration30-source79-static-execution-v1', 'integration30-source79-static-execution-v2',
    'source79-authoring-fragments-sync-execution-v1', 'source66-79-actual-application-execution-v1',
]
for stem in stems:
    for suffix in ['.json', '.log']:
        add('reports/full-coverage/' + stem + suffix)
for directory in [
    'book/coverage/checks/future30-core/browser30-final12-visual-independent-applied30b-v1',
    'book/coverage/checks/future30-core/freeze30-source-only2-independent-modules-v1',
    'book/coverage/checks/future30-core/publisher30-source-only2-independent-modules-v1',
    'book/coverage/checks/future30-core/publisher30-source-only3-independent-modules-v1',
    'book/coverage/checks/future30-core/actual30-first-finalCSS-audit-independent-foundations-v1',
]:
    for p in (ROOT / directory).rglob('*'):
        if p.is_file():
            add(p.relative_to(ROOT).as_posix())
config = PUB / '_config.yml'
archive = ROOT / 'reports/full-coverage/source-history/pages30-original-configuration-v1.yml'
assert not archive.exists() and not (ROOT / '_config.yml').exists()
shutil.copyfile(config, archive)
old_exclusions = [l[4:] for l in config.read_text().splitlines() if l.startswith('  - ')]
exclusions = set(old_exclusions) | {
    'reports/full-coverage/checkpoint-29-manifest.json', 'reports/full-coverage/checkpoint-29-selection.json',
    'reports/full-coverage/lean-checkpoint-29', 'reports/full-coverage/owner29-originals-before-owner30-integration-v2',
    'reports/full-coverage/publication30-prepared-exact-files-v1.json',
    'reports/full-coverage/publication30-extra-inputs-v1.json',
}
for n in closure:
    if n.startswith('book/coverage/inventory-') and n.endswith('.json'):
        exclusions.add(n)
new_config = '# Preserve complete audit evidence in Git; publish the current readable site and audit.\nexclude:\n' + ''.join('  - ' + n + '\n' for n in sorted(exclusions))
(ROOT / '_config.yml').write_text(new_config)
add('_config.yml')
add(archive.relative_to(ROOT).as_posix())
copy = {}; existing = {}
for n, h in sorted(closure.items()):
    if n in frozen:
        assert frozen[n] == h, n
    elif (PUB / n).is_file() and sha(PUB / n) == h:
        existing[n] = h
    else:
        copy[n] = h
assert not (set(copy) & set(existing))
assert all(sha(ROOT / n) == h for n, h in closure.items())
report = {'status': 'explicit_source30_publication_supplement_paths_and_existing_historical_references',
          'copy_root_paths_sha256': copy, 'unchanged_existing_publication_paths_sha256': existing,
          'source_only_manifest': {'file': 'reports/full-coverage/checkpoint-30-manifest.json', 'sha256': sha(ROOT / 'reports/full-coverage/checkpoint-30-manifest.json')},
          'exact_current30_evidence_file_count': len(closure), 'new_or_changed_supplement_count': len(copy),
          'unchanged_existing_publication_count': len(existing), 'coverage_complete': False,
          'old_snapshot_or_lake_tree_copied': False, 'commit_push_or_live_success_claimed': False}
with OUT.open('x') as f:
    f.write(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'], 'new_or_changed_files': len(copy),
                  'new_or_changed_bytes': sum((ROOT / n).stat().st_size for n in copy),
                  'existing_files': len(existing), 'supplements_sha256': sha(OUT)}))

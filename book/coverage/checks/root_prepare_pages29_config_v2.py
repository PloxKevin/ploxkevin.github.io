"""Keep current downloads hosted and exact historical audit archives in Git."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, subprocess

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT/'reports/book/publication-repo'
BEFORE = 'dd0800b1b4364dfae50b78ab504e6f669c9784847d041c84289e2474dabf189b'
HEAD = 'fa1e92e55ea0b8fac9ba30ef2b0450b5e5281702'
REPORT = 'reports/full-coverage/pages29-config-preparation-v2.json'
BACKUP = 'reports/full-coverage/pages29-config177-previous-original-v2.yml'
HEADER = '# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'
ADDITIONS = {'reports/full-coverage/publication-prepared-29-files.json'}
REMOVALS = {'book/coverage/checks/future29-foundations'}
LEGACY156 = 'reports/full-coverage/pages29-config-previous-original-v1.yml'
LEGACY156_SHA = '1f8ac723695777fc029ec267efab2141978b11f3c8b0604aebcfb9d9d953e7bd'
BUDGET = 850_000_000

def safe(base, n):
    assert type(n) is str and n and Path(n).as_posix() == n and not Path(n).is_absolute() and '..' not in Path(n).parts
    assert not any(c in n for c in '\0\n\r*?[')
    p = base/n; assert p.resolve().is_relative_to(base) and not p.is_symlink()
    return p
def sha(base, n): return hashlib.sha256(safe(base, n).read_bytes()).hexdigest()
def read(base, n): return json.loads(safe(base, n).read_bytes())
def kept(n, exclusions): return not any(n == e or n.startswith(e+'/') for e in exclusions)
def encoded(d): return (json.dumps(d, ensure_ascii=False, separators=(',', ':'))+'\n').encode()

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--apply', action='store_true'); args = ap.parse_args()
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PUB, text=True).strip() == HEAD
    assert sha(PUB, '_config.yml') == BEFORE
    original = safe(PUB, '_config.yml').read_bytes()
    old = {line[4:] for line in original.decode().splitlines() if line.startswith('  - ')}
    assert len(old) == 177 and original.decode() == HEADER+''.join('  - '+n+'\n' for n in sorted(old))
    assert len(ADDITIONS) == len(REMOVALS) == 1 and not old.intersection(ADDITIONS)
    assert REMOVALS <= old and 'book/coverage/checks' in old
    assert sha(ROOT, LEGACY156) == LEGACY156_SHA
    legacy = {line[4:] for line in safe(ROOT, LEGACY156).read_text().splitlines() if line.startswith('  - ')}
    assert len(legacy) == 156 and legacy <= old
    exclusions = (old - REMOVALS) | ADDITIONS
    assert len(exclusions) == 177 and legacy <= exclusions and 'book/coverage/checks' in exclusions
    assert not kept(next(iter(REMOVALS)), exclusions)
    for n in exclusions: safe(PUB, n)
    after = (HEADER+''.join('  - '+n+'\n' for n in sorted(exclusions))).encode()
    manifest = read(ROOT, 'reports/full-coverage/checkpoint-29-manifest.json')
    selection = read(ROOT, 'reports/full-coverage/checkpoint-29-selection.json')
    audit_name = 'reports/full-coverage/lean-checkpoint-29/verification-original.json'; audit = read(ROOT, audit_name)
    assert manifest['status'] == 'formal_verification_passed_partial_coverage' and audit['status'] == 'passed'
    assert manifest['proof_files'] == selection['proof_files'] and manifest['selection_sha256'] == sha(ROOT, 'reports/full-coverage/checkpoint-29-selection.json')
    assert len(selection['proof_files']) == audit['proof_file_count'] == 1197 and audit['theorem_count'] == 10114
    assert audit['proof_sha256'] == {n: r['sha256'] for n, r in selection['proof_files'].items()}
    assert len(audit['declarations']) == len(audit['axiom_dependencies']) == 10114
    assert all(type(c['exit_code']) is int and c['exit_code'] == 0 for c in audit['checks'])
    assert sum(c.get('evidence_mode') == 'fresh_kernel_replay' for c in audit['checks']) == 11
    assert sum(c.get('evidence_mode') == 'reused_identical_module_and_transitive_local_imports' for c in audit['checks']) == 1186
    assert set(audit['allowed_standard_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
    assert all(set(a) <= set(audit['allowed_standard_axioms']) for a in audit['axiom_dependencies'].values())
    assert manifest['successful_verification']['report_sha256'] == sha(ROOT, audit_name)
    required = {n: h for n, h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in ['book/coverage/inventory.json', 'book/coverage/material-corrections.json', *['book/coverage/'+k+'.json' for k in ['core', 'foundations', 'applied', 'modules', 'applied-promotions']]]}
    assert len([n for n in required if n.startswith('SafeLearning/')]) == 31
    assert required['book/coverage/inventory.json'] == '5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
    for n in ['reports/full-coverage/checkpoint-29-manifest.json', 'reports/full-coverage/checkpoint-29-selection.json', 'reports/full-coverage/checkpoint-29-ledger-manifest.json', 'reports/full-coverage/integration-29.json', 'reports/full-coverage/browser-checkpoint-29.json', 'reports/full-coverage/browser-corrections-29-inputs.json', 'reports/full-coverage/source65-eight-captured-regions-manual-review29-v1.json', 'reports/full-coverage/source65-four-page-math-scroll29-v2.json']:
        required[n] = sha(ROOT, n)
    for directory in ['reports/full-coverage/lean-checkpoint-29', 'reports/full-coverage/browser-artifacts-29']:
        files = {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in safe(ROOT, directory).rglob('*') if p.is_file()}
        assert files; required.update(files)
    for n, h in required.items(): assert kept(n, exclusions) and sha(PUB, n) == h, n
    archived_sources = {n: r['sha256'] for n, r in selection['proof_files'].items()}
    assert 'verification/lean' in old and all(sha(ROOT, n) == sha(PUB, n) == h for n, h in archived_sources.items())
    browser = read(ROOT, 'reports/full-coverage/browser-checkpoint-29.json')
    assert browser['status'] == 'passed_actual_changed_pages_and_exact_unchanged_evidence'
    assert browser['source_sha256'] == {n: h for n, h in required.items() if n.startswith('SafeLearning/')}
    assert (browser['page_count'], browser['verified_viewport_count'], browser['fresh_verified_viewport_count'], browser['retained_verified_viewport_count']) == (29, 145, 20, 125)
    ledger = read(PUB, 'reports/full-coverage/lean-checkpoint-29/ledger-audit.json')
    assert ledger['integrity_status'] == 'passed' and ledger['errors'] == [] and ledger['mathematical_coverage_complete'] is False
    assert ledger['inventory_sha256'] == required['book/coverage/inventory.json']
    assert ledger['counts']['material_review_statuses'] == {'reviewed': 4663, 'pending': 8111}
    for n in [REPORT, BACKUP]: assert not safe(ROOT, n).exists() and not safe(PUB, n).exists()
    included = sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix(), exclusions))
    result = {'status': 'passed_exact_pages29_archival_configuration_requires_actual_pages_and_live_checks', 'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'helper': {'file': Path(__file__).relative_to(ROOT).as_posix(), 'sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
        'previous_configuration': {'file': BACKUP, 'sha256': BEFORE}, 'config_sha256': hashlib.sha256(after).hexdigest(),
        'exclusions': sorted(exclusions), 'excluded_count': len(exclusions), 'new_literal_exclusions': sorted(ADDITIONS),
        'removed_redundant_literal_exclusions': sorted(REMOVALS), 'previous_literal_exclusion_count': len(old),
        'all_original156_literal_exclusions_retained': True, 'removed_child_still_excluded_by_parent': 'book/coverage/checks',
        'exact_generated_file_registry_in_git_archive': {'file': 'reports/full-coverage/publication-prepared-29-files.json', 'sha256': sha(ROOT, 'reports/full-coverage/publication-prepared-29-files.json')},
        'required_publication_files_sha256': required, 'exact_selected_lean_sources_in_git_archive_sha256': archived_sources,
        'website_budget_bytes': BUDGET, 'included_website_bytes_including_configuration_evidence': 0, 'coverage_complete': False,
        'scope': 'Only website inclusion changes. Historical archives remain exact in Git. Current65 pages, ledgers,1197-source/10114-theorem audit and48 captures remain hosted. All1197 Lean sources remain exact in Git under the existing verification/lean website exclusion. Delivery is still pending.'}
    base = included-len(original)+len(after)+len(original)
    for _ in range(20):
        size = base+len(encoded(result))
        if size == result['included_website_bytes_including_configuration_evidence']: break
        result['included_website_bytes_including_configuration_evidence'] = size
    assert result['included_website_bytes_including_configuration_evidence'] == base+len(encoded(result)) <= BUDGET
    if not args.apply:
        print(json.dumps({'status': 'ready_pages29_literal_configuration_no_writes', 'website_bytes': size, 'exclusions': len(exclusions)})); return
    for base_path in [ROOT, PUB]:
        p = safe(base_path, BACKUP); p.parent.mkdir(parents=True, exist_ok=True)
        with p.open('xb') as f: f.write(original)
        p = safe(base_path, REPORT)
        with p.open('xb') as f: f.write(encoded(result))
    safe(PUB, '_config.yml').write_bytes(after)
    assert sha(PUB, '_config.yml') == result['config_sha256']
    print(json.dumps({'status': result['status'], 'website_bytes': size, 'excluded_count': len(exclusions), 'config_sha256': result['config_sha256']}))

if __name__ == '__main__': main()

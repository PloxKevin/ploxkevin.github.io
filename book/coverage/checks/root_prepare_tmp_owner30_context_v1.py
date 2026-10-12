"""Prepare fresh TMP-only guards for actual Source79, final CSS and raw owner30."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]
SELF = 'book/coverage/checks/root_prepare_tmp_owner30_context_v1.py'
CONTEXT = Path('/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json')
RUNNER = Path('/tmp/root_tmp_lean_current79_owner30_finalcss_runner_v1.py')
TEMPLATE = Path('/tmp/root_tmp_lean_current79_historical_owner29_runner_v1.py')
TEMPLATE_SHA = '15a0e14143ea9338dfa6770840b8bee7a36903889418e785c55b2a2fcdbf2c4e'
STATUS = 'actual_source79_final_css_owner30_selected30_audited_TMP_context_only'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def safe(n):
    assert type(n) is str and n and Path(n).as_posix() == n
    assert not Path(n).is_absolute() and '..' not in Path(n).parts
    p = ROOT / n
    assert p.is_file() and not p.is_symlink() and p.resolve().is_relative_to(ROOT)
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(ROOT))
    return p


def checked(n, h):
    assert sha(safe(n)) == h
    return json.loads(safe(n).read_bytes())


def main():
    assert not CONTEXT.exists() and not RUNNER.exists()
    assert sha(TEMPLATE) == TEMPLATE_SHA
    references = {
        'reports/full-coverage/checkpoint-30-selection.json': '21c101dece9c614941e28174a5ff5ad6ead0fb271479f0c65cb732d10acdd196',
        'reports/full-coverage/checkpoint-30-manifest.json': '74b7eb171018a762341ab671a21d2fd730d171eaa455fa2385b8619a6c9c999a',
        'reports/full-coverage/owner30-reviewed-candidate-integration-v2.json': '34dc308f520cb6b866f7e17e17f6426a25df3a3677420be29df4b65794166963',
        'reports/full-coverage/lean-checkpoint-30/ledger-audit-working-v1.json': '72d8282bd39514d784f1af1e31e234efeb1cff67a0814181c5b32360be016f93',
        'reports/full-coverage/lean-checkpoint-30-final-css-v1/verification-original.json': '78915d21ec383430a5abea1c4b3cc9753dcfd5b2f94adb4834471459a3e2b00c',
    }
    data = {n: checked(n, h) for n, h in references.items()}
    selection_name, manifest_name, integration_name, ledger_name, audit_name = references
    selected, manifest, integration, ledger, audit = [data[n] for n in references]
    assert selected['proof_file_count'] == manifest['successful_verification']['proof_files'] == audit['proof_file_count'] == 1242
    assert audit['status'] == 'passed' and audit['theorem_count'] == 11080
    assert ledger['integrity_status'] == 'passed' and ledger['errors'] == [] and ledger['mathematical_coverage_complete'] is False
    assert manifest['status'] == 'formal_verification_passed_partial_coverage' and integration['applied'] is True
    proofs = {n: r['sha256'] for n, r in selected['proof_files'].items()}
    assert proofs == audit['proof_sha256']
    held = audit['source_sha256']; assert len(held) == 31
    owners = {r['destination']: r['candidate']['sha256'] for r in integration['exact_replacements']}
    assert len(owners) == 5
    pins = {**references, **proofs, SELF: sha(safe(SELF))}
    for n in ['book/coverage/inventory.json', 'book/coverage/material-corrections.json',
              'book/coverage/lean_names.py', 'verification/lean/verify.py',
              'verification/lean/lean-toolchain', 'verification/lean/lakefile.toml',
              'verification/lean/lake-manifest.json']:
        pins[n] = sha(safe(n))
    assert pins['book/coverage/inventory.json'] == '9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de'
    for owner in owners:
        for n, h in json.loads(safe(owner).read_bytes()).get('chapter_fragment_sha256', {}).items():
            pins[n] = h
    for n, h in {**pins, **held, **owners}.items():
        assert sha(safe(n)) == h, n
    def ref(n):
        return {'file': n, 'sha256': references[n]}
    context = {'status': STATUS, 'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'pins_sha256': pins, 'held_current_source_sha256': held, 'owners_sha256': owners,
        'selection': ref(selection_name), 'manifest': ref(manifest_name), 'actual_audit': ref(audit_name),
        'actual_owner30_integration': ref(integration_name), 'actual_global_ledger': ref(ledger_name),
        'protected_selected30_proof_sources': 1242, 'held_current79_final_css_book_assets': 31,
        'held_current_source79_raw_owner30_files': 5, 'original_runner_template_sha256': TEMPLATE_SHA,
        'scope': 'Future TMP trials hold the actual current source, compiled selected proof sources and installed raw owner30 records. Their compiler outcome alone does not promote source coverage, install canonical proofs, or claim a new aggregate audit.',
        'canonical_installation_or_new_aggregate_claimed': False, 'coverage_complete': False}
    payload = (json.dumps(context, indent=2) + '\n').encode()
    context_sha = hashlib.sha256(payload).hexdigest()
    runner = TEMPLATE.read_text()
    replacements = {
        'current Source79 and unchanged historical Source65 owner29 context': 'actual Source79 final CSS and raw owner30 context',
        '/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json': str(CONTEXT),
        'd06f4ef21178b787db693df28ca5ae01386728915e0596cba5fd17f000db0737': context_sha,
        'current_source79_with_unchanged_historical_source65_owner29_for_tmp_trials_only': STATUS,
        'actual_source79_historical_source65_owner29_context': 'actual_source79_final_css_owner30_context',
        'actual_installed29_selection': 'actual_installed30_selection',
        'actual_frozen29_original_audit': 'actual_runtime30_final_css_original_audit',
        "'protected_selected29_proof_sources':1197": "'protected_selected30_proof_sources':1242",
        'unchanged_current79_book_assets': 'unchanged_current79_final_css_book_assets',
        'unchanged_historical_source65_owner29_files': 'unchanged_current_source79_raw_owner30_files',
        'installed29_owner_sha256': 'installed30_raw_owner_sha256',
    }
    for old, new in replacements.items():
        assert old in runner, old
        runner = runner.replace(old, new)
    assert 'historical_source65' not in runner and 'protected_selected29' not in runner
    with CONTEXT.open('xb') as f:
        f.write(payload)
    with RUNNER.open('x') as f:
        f.write(runner)
    assert sha(CONTEXT) == context_sha and sha(TEMPLATE) == TEMPLATE_SHA
    for n, h in {**pins, **held, **owners}.items():
        assert sha(safe(n)) == h, n
    print(json.dumps({'status': STATUS, 'context': {'file': str(CONTEXT), 'sha256': context_sha},
        'runner': {'file': str(RUNNER), 'sha256': sha(RUNNER)}, 'protected_proofs': 1242,
        'compiler_invoked': False, 'coverage_complete': False}))


if __name__ == '__main__':
    main()

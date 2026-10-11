from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, copy

R = Path('/home/oxrexkevin/SafetyBased')
S = Path('/tmp/pages27-config5-actual-output-independent-modules-review-v1.json')
OUT = Path('/tmp/pages27-config5-output-closure-corrected-independent-modules-review-v1.json')
assert not OUT.exists()
def H(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
assert H(S) == '483e94bcd85ea62d7a536e56856b8cee07f8439e9961647352e00860ce51677c'
v = json.loads(S.read_bytes())
assert v['status'] == 'passed_independent_actual_checkpoint27_pages_configuration' and v['errors'] == []
observed = []
for n, h in v['closed_evidence_sha256'].items():
    p = Path(n) if n.startswith('/') else R / n
    if H(p) != h:
        observed.append((n, h, H(p)))
assert len(observed) == 1 and observed[0][0] == 'book/coverage/applied.json'
n, old, new = observed[0]
assert old == v['published_frozen_ledger_sha256'][n] == v['required_publication_files_sha256'][n]
assert new == v['working_ledger_sha256'][n]
assert H(R / 'reports/book/publication-repo' / n) == old
out = copy.deepcopy(v)
out['closed_evidence_sha256'][n] = new
inverse = copy.deepcopy(out)
inverse['closed_evidence_sha256'][n] = old
assert inverse == v
out['closed_evidence_scope_correction'] = {
    'kind': 'single_closed_evidence_root_vs_published_scope_correction',
    'corrected_at_utc': datetime.now(timezone.utc).isoformat(),
    'file': n,
    'original_pruned_published_sha256': old,
    'correct_working_root_sha256': new,
    'original_passed_output': {'file': str(S), 'sha256': H(S)},
    'entire_original_passed_output_body_and_time': v,
    'entire_original_recovered_by_one_digest_inverse': True,
    'published_required_map_and_all_configuration_decisions_unchanged': True,
    'actual_producer_or_owner_write_claimed': False
}
out['closed_evidence_sha256'][str(S)] = H(S)
obs = Path('/tmp/pages27-config5-output-closure-native-tool-observations-v1.json')
out['closed_evidence_sha256'][str(obs)] = H(obs)
prior_outer = Path('/tmp/run-pages27-config5-output-closure-correction-independent-modules-v1.py')
out['closed_evidence_sha256'][str(prior_outer)] = H(prior_outer)
for n, h in out['closed_evidence_sha256'].items():
    assert H(Path(n) if n.startswith('/') else R / n) == h, n
OUT.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({'status': 'passed', 'corrected_peer': str(OUT), 'sha256': H(OUT), 'remaining_hash_conflicts': 0}))

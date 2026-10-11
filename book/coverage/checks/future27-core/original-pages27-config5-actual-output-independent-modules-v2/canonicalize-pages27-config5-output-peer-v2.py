from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

R = Path('/home/oxrexkevin/SafetyBased')
S = Path('/tmp/pages27-config5-output-closure-final-independent-modules-review-v1.json')
def H(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
assert H(S) == 'f1010b09452f80a0a6c7ef8a45473a8188438e71abff4acdb0c8503204537c7a'
v = json.loads(S.read_bytes())
B = R / 'book/coverage/checks/future27-core/original-pages27-config5-actual-output-independent-modules-v2'
B.mkdir(parents=True, exist_ok=False)
aliases, closed = {}, {}
refs = dict(v['closed_evidence_sha256'])
refs[str(S)] = H(S)
refs[__file__] = H(Path(__file__))
for n, digest in refs.items():
    p = Path(n) if n.startswith('/') else R / n
    assert H(p) == digest, n
    if n.startswith('/'):
        q = B / p.name
        assert not q.exists(), p.name
        q.write_bytes(p.read_bytes())
        assert H(q) == digest
        relative = q.relative_to(R).as_posix()
        aliases[n] = {'file': relative, 'sha256': digest}
        closed[relative] = digest
    else:
        closed[n] = digest
C = B / 'original-closed-byte-aliases-v1.json'
C.write_text(json.dumps({
    'status': 'passed_exact_original_closed_byte_aliases',
    'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
    'original_closed_byte_aliases': aliases,
    'original_body_status_time_preserved': True
}, indent=2) + '\n')
closed[C.relative_to(R).as_posix()] = H(C)
P = R / 'book/coverage/checks/future27-core/pages27-config-independent-modules-output-v5.json'
assert not P.exists()
out = dict(v)
for key in ['actual_independent_output_review', 'independent_output_checker', 'independent_output_runner',
            'actual_independent_closure_correction', 'independent_closure_checker', 'independent_closure_runner']:
    out[key] = aliases[v[key]['file']]
out['original_review'] = aliases[str(S)]
out['entire_original_review_body_and_time'] = v
out['original_closed_byte_aliases'] = aliases
out['closed_evidence_sha256'] = closed
P.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({'peer': P.relative_to(R).as_posix(), 'sha256': H(P),
                  'actual_execution': out['actual_execution'],
                  'native_preparation_report': out['native_preparation_report'],
                  'original_count': len(aliases), 'catalog_sha256': H(C),
                  'config_sha256': out['config_sha256']}))

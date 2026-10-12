from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time

ROOT = Path('/home/oxrexkevin/SafetyBased')
CONTEXT = Path('/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json')
CHECK = Path('/tmp/review-modules30-current79-real30-independent-foundations-v4.py')
OUT = Path('/tmp/modules30-current79-real30-independent-foundations-actual-v4.json')
LOG = OUT.with_suffix('.log')
assert not OUT.exists() and not LOG.exists()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(CONTEXT) == 'd06f4ef21178b787db693df28ca5ae01386728915e0596cba5fd17f000db0737'
context = json.loads(CONTEXT.read_bytes())
protected = {**context['pins_sha256'], **context['held_current_source_sha256'], **context['owners_sha256']}
readiness = json.loads((ROOT/'book/coverage/checks/future30-core/current79-canonical-pairs45-v1/actual-reviewed30-canonical-paired-readiness-v1.json').read_bytes())
for row in readiness['sources']: protected[row['canonical_source']] = row['original_tmp_source']['sha256']
assert len([n for n in protected if n.startswith('verification/lean/SafeLearning/')]) == 1242
fragment_offer=json.loads((ROOT/'book/coverage/checks/modules-future30/current79-three-fragments-final-v1/modules30-current79-real30-three-fragments-offer-draft-v2.json').read_bytes())
fragment_candidate=json.loads((ROOT/fragment_offer['candidate']['file']).read_bytes())
protected.update(fragment_candidate['chapter_fragment_sha256'])
assert all(sha(ROOT/n) == h for n, h in protected.items())
before = {str(CHECK): sha(CHECK), str(CONTEXT): sha(CONTEXT)}
started = datetime.now(timezone.utc).isoformat()
t = time.monotonic()
command = ['python3', str(CHECK)]
native = subprocess.run(command, cwd=ROOT, capture_output=True)
LOG.write_bytes(native.stdout+native.stderr)
after = {str(CHECK): sha(CHECK), str(CONTEXT): sha(CONTEXT)}
protection_errors = [n for n, h in protected.items() if sha(ROOT/n) != h]
d = {
    'status': 'passed' if native.returncode == 0 and not protection_errors and before == after else 'failed',
    'actual_command': command, 'actual_workdir': str(ROOT),
    'actual_exit_code': native.returncode,
    'started_at_utc': started, 'finished_at_utc': datetime.now(timezone.utc).isoformat(),
    'elapsed_seconds': time.monotonic()-t,
    'helper_sha256_before': before, 'helper_sha256_after': after,
    'log': str(LOG), 'log_sha256': sha(LOG),
    'protected_inputs_sha256_before': protected,
    'protected_inputs_sha256_after': {n: sha(ROOT/n) for n in protected},
    'protection_errors': protection_errors,
    'scope': 'Source79 guarded independent full Module owner30 current79 real15-source30 canonical-pair forward/inverse/history/whole and component mapping review. No compiler/parser or live Source/owner/selection/publication writes; all original semantic scopes/times retained. No compiler, parser, source, owner, canonical or publication mutation.',
}
OUT.write_text(json.dumps(d, indent=2)+'\n')
print(json.dumps({k: d[k] for k in ['status', 'actual_exit_code', 'elapsed_seconds', 'protection_errors']}))
raise SystemExit(0 if d['status'] == 'passed' else 1)

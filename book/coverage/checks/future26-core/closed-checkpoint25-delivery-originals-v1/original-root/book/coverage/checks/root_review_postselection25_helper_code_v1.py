"""Record Root's full-code review of four Module-authored checkpoint25 helpers."""
from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json

ROOT = Path(__file__).resolve().parents[3]
OUT = 'book/coverage/checks/future25-core/postselection25-four-helpers-independent-root-code-review-v1.json'
HELPERS = {
    'book/coverage/checks/root_check_checkpoint25_selection_output_v1.py': 'c74be596e483857ff2cabf0c33782e2a169928790d30c890e891b4a55c64b39a',
    'book/coverage/checks/root_prepare_checkpoint25_cache_v1.py': 'de90e277ae91ea71b65b5ba4e62b1dc17d789bb43b95ad57b187c55c849c36e9',
    'book/coverage/checks/root_check_export25_integrity_v1.py': '0ef265696bff690f7059f1934cf5804fe175003fc5113c2449135c6a7720d353',
    'book/coverage/checks/root_prepare_checkpoint25_documentation_v1.py': 'a9d6db82c57fb3a31c994fe9afba891f47c0f940ab44d999b47124c27d586fcd'}

def sha(name): return hashlib.sha256((ROOT / name).read_bytes()).hexdigest()

assert not (ROOT / OUT).exists()
for name, digest in HELPERS.items():
    assert sha(name) == digest
    ast.parse((ROOT / name).read_text(), filename=name)
protected = {name: sha(name) for name in ['book/coverage/' + owner + '.json' for owner in ('core', 'foundations', 'applied', 'modules', 'applied-promotions')]}
out = {
    'status': 'passed_independent_root_full_code_review_requires_actual_checkpoint25_outputs',
    'reviewer': '/root', 'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
    'helpers_sha256': HELPERS,
    'review_findings': [
        'The selection reader checks the genuine selector execution and hashes; all1156 sources and9369 unique public names; all1144 old rows, four typed owner archives and40485 original frozen content bindings. It separately checks the one reviewed preparation-code update and its provenance.',
        'The cache helper accepts only the1156 selected sources, each identical to its actual frozen25 source. Old1144 source hashes must match selection24. It copies only matching selected module artifacts; no aggregate, compiler or kernel success is inferred.',
        'The export reader compares the untouched original report and every output byte. Its only permitted report transformation relocates exported output/report paths. All checks must have integer exit0, and12 fresh plus1144 unchanged kernel replays must agree; axiom sets remain explicitly restricted.',
        'The documentation helper requires actual25 audit, exported original report, frozen-ledger integrity and static checks. It derives coverage counts from the actual ledger. Browser24 evidence is retained only when all31 asset hashes and QA helper hashes still match; it explicitly does not claim a fresh browser or Pages run.',
        'Documentation preserves the previous progress and README bytes before updating them. Its state explicitly awaits actual publication, Pages and live checks and leaves coverage_complete false.'
    ],
    'syntax_parsed_complete_helper_count': 4,
    'actual_checkpoint25_outputs_reviewed': False,
    'actual_helper_execution_inferred': False,
    'fixture_execution_inferred': False,
    'live_owner_sha256_unchanged': protected,
    'errors': [],
    'scope': 'Independent full-code reading and actual AST syntax parsing only. Production selection, cache copy, export and documentation need their own genuine executions and actual-output checks. No mathematical correspondence decision or Lean success is supplied by this report.'
}
assert all(sha(name) == digest for name, digest in protected.items())
with (ROOT / OUT).open('x') as stream: stream.write(json.dumps(out, indent=2) + '\n')
print(json.dumps({'status': 'passed', 'helpers_reviewed': 4, 'code_peer': {'file': OUT, 'sha256': sha(OUT)}, 'actual25_output_or_execution_claimed': False}))

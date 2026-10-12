"""Add a bounded mobile scroll container without changing mathematical text."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]
CSS = ROOT / 'SafeLearning/style.css'
CONTEXT = Path('/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json')
ARCHIVE = ROOT / 'reports/full-coverage/source-history/cmdp-mobile-inline-formula-style30-v1'
RESULT = ROOT / 'reports/full-coverage/cmdp-mobile-inline-formula-style30-application-v1.json'
SELECTION = ROOT / 'reports/full-coverage/checkpoint-30-selection.json'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


assert not ARCHIVE.exists() and not RESULT.exists()
selection = json.loads(SELECTION.read_bytes())
assert sha(SELECTION) == '21c101dece9c614941e28174a5ff5ad6ead0fb271479f0c65cb732d10acdd196'
proofs = {n: r['sha256'] for n, r in selection['proof_files'].items()}
assert len(proofs) == 1242
assets = {p.relative_to(ROOT).as_posix(): sha(p) for p in (ROOT / 'SafeLearning').iterdir() if p.suffix in {'.html', '.css', '.js'}}
assert len(assets) == 31
context = json.loads(CONTEXT.read_bytes())
old = CSS.read_bytes()
# The earlier genuine browser audit and source-only Lean runtime preserve this
# exact original CSS. No existing native/audit/peer record is rewritten.
assert sha(CSS) == sha(ROOT / 'reports/full-coverage/runtime-checkpoint-30/SafeLearning/style.css')
assert all(sha(ROOT / n) == h for n, h in proofs.items())
block = '''
/* Long inline guarantees in the CMDP state-augmentation theorem remain
   readable on small phones; each formula scrolls inside the text column. */
@media screen and (max-width: 360px) {
  #state-augmentation ~ .definition-box .katex:not(.katex-display .katex) {
    display: inline-block;
    max-width: 100%;
    overflow-x: auto;
    overflow-y: hidden;
    vertical-align: middle;
    position: relative;
    padding: 4px 2px;
  }
}
'''.encode()
assert b'#state-augmentation ~ .definition-box .katex' not in old
assert sum(b'id="state-augmentation"' in (ROOT / n).read_bytes() for n in assets if n.endswith('.html')) == 1
ARCHIVE.mkdir(parents=True)
with (ARCHIVE / 'style-before.css').open('xb') as f:
    f.write(old)
assert sha(ARCHIVE / 'style-before.css') == assets['SafeLearning/style.css']
CSS.write_bytes(old + block)
assert CSS.read_bytes()[:-len(block)] == old
assert all(sha(ROOT / n) == h for n, h in proofs.items())
assert all(sha(ROOT / n) == h for n, h in assets.items() if n != 'SafeLearning/style.css')
record = {'status': 'targeted_CMDP_mobile_formula_style_applied_pending_fresh_browser_and_final_asset_audit',
          'applied_at_utc': datetime.now(timezone.utc).isoformat(),
          'old_css_sha256': assets['SafeLearning/style.css'], 'new_css_sha256': sha(CSS),
          'original_css': {'file': (ARCHIVE / 'style-before.css').relative_to(ROOT).as_posix(), 'sha256': sha(ARCHIVE / 'style-before.css')},
          'exact_append_utf8': block.decode(), 'inverse_recovers_original_css_bytes': True,
          'unchanged_HTML_and_component_assets_sha256': {n: h for n, h in assets.items() if n != 'SafeLearning/style.css'},
          'unchanged_selected_proof_count': 1242, 'inventory_sha256': sha(ROOT / 'book/coverage/inventory.json'),
          'mathematical_source_text_changed': False, 'prior_original_audits_or_native_records_modified': False,
          'browser_or_new_asset_audit_success_claimed': False, 'coverage_complete': False}
with RESULT.open('x') as f:
    f.write(json.dumps(record, indent=2) + '\n')
print(json.dumps({'status': record['status'], 'new_css_sha256': record['new_css_sha256'], 'unchanged_proof_files': 1242}))

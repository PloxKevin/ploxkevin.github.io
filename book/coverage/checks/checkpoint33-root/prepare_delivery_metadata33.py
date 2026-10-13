"""Prepare the bounded metadata commit after genuine content33 delivery."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil
ROOT = Path(__file__).resolve().parents[4]
PREFIX = 'reports/full-coverage/'
OUT = PREFIX + 'publication33-delivery-metadata-plan-v1.json'
HISTORY = PREFIX + 'source-history/checkpoint33-before-metadata-document-wording-v1'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(n): return dict(file=n,sha256=sha(ROOT/n))
def read(n): return json.loads((ROOT/n).read_bytes())
assert not (ROOT/OUT).exists() and not (ROOT/HISTORY).exists()
delivery=read(PREFIX+'publication33-content-delivery-v1.json')
assert delivery['status']=='passed_actual_checkpoint33_content_push_Pages_and_all31_live_hashes'
assert delivery['metadata_push_and_metadata_live_check_pending'] is True
progress=read('book/coverage/progress.json')
assert progress['verified_checkpoint']['checkpoint']==33
assert progress['verified_checkpoint']['theorems']==11345
assert progress['last_published_content_commit']==delivery['content_commit']
assert progress['working_next_checkpoint_preparation']['material_review_units']=={'reviewed':4851,'pending':7923}
readme=ROOT/PREFIX/'README.md'
text=readme.read_text()
old='preserves the commit, push and served-byte evidence. The later delivery-metadata\ncommit, push and live check remain pending. Full mathematical coverage remains unfinished.'
assert text.count(old)==1
original=ROOT/HISTORY/PREFIX/'README.md';original.parent.mkdir(parents=True)
shutil.copyfile(readme,original)
assert sha(readme)==sha(original)
# Current metadata stays explicitly pending in progress until its own actual
# deployment passes. This paragraph describes where its receipts are stored.
text=text.replace(old,'preserves the commit, push and served-byte evidence. Delivery metadata and\nits execution receipts are recorded separately. Full mathematical coverage remains unfinished.')
readme.write_text(text)
files={ROOT/n for n in ['README.md','book/coverage/progress.json','book/coverage/CONTINUATION.md','reports/full-coverage/README.md']}
for p in (ROOT/PREFIX).glob('*33*'):
 if p.is_file() and not p.is_symlink(): files.add(p)
for directory in [PREFIX+'source-history/checkpoint33-before-content-delivery-v1',HISTORY]:
 files.update(p for p in (ROOT/directory).rglob('*') if p.is_file() and not p.is_symlink())
files.add(Path(__file__).resolve())
hashes={}
for p in sorted(files):
 n=p.relative_to(ROOT).as_posix()
 assert n.startswith(('README.md','book/coverage/','reports/full-coverage/'))
 assert not {'.lake','.git','__pycache__'}.intersection(p.parts) and not p.suffix=='.lean'
 assert p.stat().st_size<100_000_000
 hashes[n]=sha(p)
plan=dict(status='exact_verified_content33_delivery_metadata_plan',content_commit=delivery['content_commit'],created_at_utc=datetime.now(timezone.utc).isoformat(),paths_sha256=hashes,preserved_preparation_readme=ref(original.relative_to(ROOT).as_posix()),coverage_complete=False,metadata_commit_push_Pages_or_live_success_claimed=False)
with (ROOT/OUT).open('x') as f: f.write(json.dumps(plan,indent=2)+'\n')
print(json.dumps(dict(status=plan['status'],files=len(hashes),metadata_delivery_pending=True,coverage_complete=False)))

"""Prepare literal Pages exclusions while retaining the exact current book/audits."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path(__file__).resolve().parents[3];PUB=ROOT/'reports/book/publication-repo';REPORTS=ROOT/'reports/full-coverage'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
config=PUB/'_config.yml';report=REPORTS/'pages21-config-preparation-v1.json';previous=REPORTS/'pages21-config-previous-original-v1.yml'
assert not report.exists() and not previous.exists()
assert sha(config)=='5240887696b71ede4f92468c459116dcd874de7ba3e870ef300bd4ad1d30ae82'
manifest=read(REPORTS/'checkpoint-21-manifest.json');assert manifest['status']=='formal_verification_passed_partial_coverage'
audit=read(REPORTS/'lean-checkpoint-21/verification-original.json');assert audit['status']=='passed' and audit['proof_file_count']==1089
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
for n,h in assets.items():assert sha(PUB/n)==h,n
before=config.read_bytes();previous.write_bytes(before)
excluded={line[4:] for line in before.decode().splitlines() if line.startswith('  - ')}
excluded.add('reports/full-coverage/checkpoint-21')
excluded.update(str(p.relative_to(PUB)) for p in (PUB/'book/coverage').glob('inventory*.json') if p.name!='inventory.json')
assert all(n and not n.startswith('/') and '..' not in Path(n).parts and not any(c in n for c in '*?[{') for n in excluded)
config.write_text('# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'+''.join('  - '+n+'\n' for n in sorted(excluded)))
def kept(n):return not any(n==x or n.startswith(x+'/') for x in excluded)
required=set(assets)|{'book/coverage/inventory.json','reports/full-coverage/README.md','reports/full-coverage/integration-21.json','reports/full-coverage/browser-checkpoint-21.json','reports/full-coverage/checkpoint-21-manifest.json','reports/full-coverage/checkpoint-21-selection.json','reports/full-coverage/lean-checkpoint-21/verification-original.json','reports/full-coverage/lean-checkpoint-21/verification.json','reports/full-coverage/lean-checkpoint-21/ledger-audit.json'}|{'book/coverage/'+owner+'.json' for owner in ['foundations','applied','modules','core']}
for n in required:assert (PUB/n).is_file() and kept(n),n
included=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(str(p.relative_to(PUB))))
assert included<900_000_000
report.write_text(json.dumps(dict(status='literal_archive_exclusions_prepared_requires_independent_review_and_actual_pages_build',prepared_at_utc=datetime.now(timezone.utc).isoformat(),config_sha256=sha(config),previous_config=str(previous.relative_to(ROOT)),previous_config_sha256=hashlib.sha256(before).hexdigest(),exclusions=sorted(excluded),excluded_count=len(excluded),included_file_bytes=included,exact_frozen_assets=assets,required_published_paths=sorted(required),scope='Only site build exclusions changed. Current31 assets, inventory, four partial ledgers and actual21 audit reports remain published; archives remain in Git. Actual Pages workflow and live hashes are separate.'),indent=2)+'\n')
print(json.dumps(dict(status='prepared',included_bytes=included,excluded=len(excluded),config_sha256=sha(config))))

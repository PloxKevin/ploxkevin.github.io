"""Preserve Pages23 bytes and add exact archival exclusions for audited24."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess

ROOT=Path(__file__).resolve().parents[3]
PUB=ROOT/'reports/book/publication-repo'
CFG=PUB/'_config.yml'
REPORT='reports/full-coverage/pages24-config-preparation-v1.json'
BACKUP='reports/full-coverage/pages24-config-previous-original-v1.yml'
BEFORE='278d5b40954704026471c5589d8869af8b9a5e5111c5cb070a28e35876ab09e3'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def ref(n):return {'file':n,'sha256':sha(ROOT/n)}
assert not (ROOT/REPORT).exists() and not (ROOT/BACKUP).exists()
assert sha(CFG)==BEFORE
old=CFG.read_bytes()
exclusions={line[4:] for line in old.decode().splitlines() if line.startswith('  - ')}
assert len(exclusions)==66
assert old.decode()=='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'+''.join('  - '+n+'\n' for n in sorted(exclusions))
assert sha(ROOT/'reports/full-coverage/checkpoint-23-manifest.json')=='e21eac7bfafd8002d75966240e5c3ea940ebec3dba4066fb1e9a767627d7fb06'
manifest=read('reports/full-coverage/checkpoint-24-manifest.json')
selection=read('reports/full-coverage/checkpoint-24-selection.json')
audit=read('reports/full-coverage/lean-checkpoint-24/verification-original.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert manifest['selection_sha256']==sha(ROOT/'reports/full-coverage/checkpoint-24-selection.json')
assert len(manifest['proof_files'])==selection['proof_file_count']==audit['proof_file_count']==1144
assert selection['new_file_count']==13 and audit['status']=='passed' and audit['theorem_count']==9279
assert all(c['exit_code']==0 for c in audit['checks'])
assert sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])==13
assert sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])==1131
for stem in ['verify-checkpoint24','export-checkpoint24','prepare-publication24']:
    actual=read('reports/full-coverage/'+stem+'-execution-v1.json')
    assert actual['actual_exit_code']==0 and sha(ROOT/actual['log'])==actual['log_sha256']
assets={n:s for n,s in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets)==31 and assets['SafeLearning/nn-in-the-loop.html']=='1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'
required=dict(assets)
for n,s in assets.items():assert sha(ROOT/n)==sha(PUB/n)==s
for n in ['book/coverage/inventory.json','book/coverage/material-corrections.json']+['book/coverage/'+o+'.json' for o in ['core','foundations','applied','modules']]:
    s=manifest['frozen_inputs_sha256'][n]
    assert sha(PUB/n)==sha(ROOT/manifest['snapshot']/n)==s
    required[n]=s
assert required['book/coverage/inventory.json']=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
for n in ['reports/full-coverage/integration-24.json','reports/full-coverage/browser-checkpoint-24.json',
    'reports/full-coverage/checkpoint-24-manifest.json','reports/full-coverage/checkpoint-24-selection.json',
    'reports/full-coverage/lean-checkpoint-24/verification-original.json','reports/full-coverage/lean-checkpoint-24/verification.json',
    'reports/full-coverage/lean-checkpoint-24/ledger-audit.json','reports/full-coverage/lean-checkpoint-23/verification-original.json']:
    assert sha(ROOT/n)==sha(PUB/n)
    required[n]=sha(PUB/n)
retired='reports/full-coverage/lean-checkpoint-22'
retired_bytes={p.relative_to(ROOT).as_posix():sha(p) for p in (ROOT/retired).rglob('*') if p.is_file()}
assert retired_bytes and retired+'/verification-original.json' in retired_bytes
assert {p.relative_to(PUB).as_posix():sha(p) for p in (PUB/retired).rglob('*') if p.is_file()}==retired_bytes
tracked=subprocess.run(['git','ls-files','-z','--',retired],cwd=PUB,check=True,capture_output=True)
assert {n for n in tracked.stdout.decode().split('\0') if n}==set(retired_bytes)
subprocess.run(['git','diff','--quiet','HEAD','--',retired],cwd=PUB,check=True)
added={retired,'reports/full-coverage/checkpoint-24',
    'reports/full-coverage/owner23-originals-before-owner24-integration-v1',
    'book/coverage/inventory-after-correction52.json'}
assert not added&exclusions
exclusions.update(added)
assert all(n and not Path(n).is_absolute() and '..' not in Path(n).parts and not any(c in n for c in '*?[{') for n in exclusions)
def kept(n):return not any(n==e or n.startswith(e+'/') for e in exclusions)
assert all(kept(n) for n in required)
assert all(not kept(n) for n in retired_bytes)
assert kept('reports/full-coverage/lean-checkpoint-23/verification-original.json')
after='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'+''.join('  - '+n+'\n' for n in sorted(exclusions))
included=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix()))-len(old)+len(after.encode())
assert included<900_000_000, included
with (ROOT/BACKUP).open('xb') as f:f.write(old)
assert sha(ROOT/BACKUP)==BEFORE
CFG.write_text(after)
report={'status':'passed_exact_pages24_archival_configuration_preparation_requires_actual_pages_build',
    'prepared_at_utc':datetime.now(timezone.utc).isoformat(),
    'helper':ref(str(Path(__file__).relative_to(ROOT))),
    'previous_configuration':ref(BACKUP),'config_sha256':sha(CFG),
    'exclusions':sorted(exclusions),'excluded_count':len(exclusions),'new_literal_exclusions':sorted(added),
    'retired_older_audit_original_sha256':retired_bytes,'retired_older_audit_exact_in_root_publication_and_tracked_HEAD':True,
    'required_publication_files_sha256':required,'prospective_included_website_bytes':included,
    'selected_sources':1144,'public_theorems':9279,'all31_source52_assets_exact':True,
    'coverage_complete':False,'scope':'Exact old Pages23 config and old audit22 files remain preserved. Only literal archival website exclusions change; both current24 and baseline23 audits remain included. No Pages24 build or live delivery is inferred.'}
with (ROOT/REPORT).open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['retired_older_audit_original_sha256','required_publication_files_sha256']}))

from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,subprocess
ROOT=Path('/home/oxrexkevin/SafetyBased');PUB=ROOT/'reports/book/publication-repo'
OUTPUT=Path('/tmp/pages24-config-independent-modules-original-output-review-v1.json')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ref=lambda p:{'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':H(p)}
J=lambda n:json.loads((ROOT/n).read_text())
assert not OUTPUT.exists()
reportpath=ROOT/'reports/full-coverage/pages24-config-preparation-v1.json';native=J(str(reportpath.relative_to(ROOT)))
actualpath=ROOT/'reports/full-coverage/pages24-config-execution-v1.json';actual=J(str(actualpath.relative_to(ROOT)))
assert actual['actual_exit_code']==0
logname=actual.get('log',actual.get('raw_log'));loghash=actual.get('log_sha256',actual.get('raw_log_sha256'));assert H(ROOT/logname)==loghash
helper=ROOT/'book/coverage/checks/root_prepare_pages24_config_v1.py';assert H(helper)==native['helper']['sha256']
codepeer=J('book/coverage/checks/pages24-config-helper-independent-foundations-review-v1.json')
assert codepeer['errors']==[] and 'passed' in codepeer['status']
assert H(ROOT/'reports/full-coverage/checkpoint-23-manifest.json')=='e21eac7bfafd8002d75966240e5c3ea940ebec3dba4066fb1e9a767627d7fb06'
manifest=J('reports/full-coverage/checkpoint-24-manifest.json');selection=J('reports/full-coverage/checkpoint-24-selection.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert H(ROOT/'reports/full-coverage/checkpoint-24-selection.json')==manifest['selection_sha256']=='9dd0a0cb80c54b728c09fc12e4327efdae621f94b5710e7a97c0d13fe92d6314'
assert selection['proof_file_count']==len(manifest['proof_files'])==1144 and selection['new_file_count']==13
verification=J('reports/full-coverage/lean-checkpoint-24/verification-original.json')
assert verification['status']=='passed' and verification['proof_file_count']==1144 and verification['theorem_count']==9279
assert all(c['exit_code']==0 for c in verification['checks'])
assert sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in verification['checks'])==13
assert sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in verification['checks'])==1131
closed={str(reportpath.relative_to(ROOT)):H(reportpath),str(actualpath.relative_to(ROOT)):H(actualpath),logname:loghash,str(helper.relative_to(ROOT)):H(helper)}
for stem in ['verify-checkpoint24','export-checkpoint24','prepare-publication24']:
 n='reports/full-coverage/'+stem+'-execution-v1.json';body=J(n);assert body['actual_exit_code']==0
 ln=body.get('log',body.get('raw_log'));lh=body.get('log_sha256',body.get('raw_log_sha256'));assert H(ROOT/ln)==lh
 closed[n]=H(ROOT/n);closed[ln]=lh
backup=ROOT/native['previous_configuration']['file'];old=backup.read_bytes()
assert H(backup)==native['previous_configuration']['sha256']=='278d5b40954704026471c5589d8869af8b9a5e5111c5cb070a28e35876ab09e3'
oldset={line[4:] for line in old.decode().splitlines() if line.startswith('  - ')};assert len(oldset)==66
header='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'
assert old.decode()==header+''.join('  - '+n+'\n' for n in sorted(oldset))
added={'reports/full-coverage/lean-checkpoint-22','reports/full-coverage/checkpoint-24','reports/full-coverage/owner23-originals-before-owner24-integration-v1','book/coverage/inventory-after-correction52.json'}
assert not oldset&added
newset=oldset|added;assert len(newset)==70
config=PUB/'_config.yml';text=config.read_text();assert text==header+''.join('  - '+n+'\n' for n in sorted(newset))
assert H(config)==native['config_sha256']
assert native['exclusions']==sorted(newset) and native['new_literal_exclusions']==sorted(added) and native['excluded_count']==70
assert all(n and not Path(n).is_absolute() and '..' not in Path(n).parts and not any(c in n for c in '*?[{') for n in newset)
def kept(n):return not any(n==e or n.startswith(e+'/') for e in newset)
assets={n:s for n,s in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets)==31 and assets['SafeLearning/nn-in-the-loop.html']=='1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'
for n,s in assets.items():assert H(ROOT/n)==H(PUB/n)==s and kept(n)
required=native['required_publication_files_sha256'];assert set(assets)<=set(required)
for n,s in required.items():assert H(PUB/n)==s and kept(n)
ledger_names=['book/coverage/'+name+'.json' for name in ['core','foundations','applied','modules']]
for n in ledger_names+['book/coverage/inventory.json','book/coverage/material-corrections.json']:
 s=manifest['frozen_inputs_sha256'][n];assert required[n]==s==H(PUB/n)==H(ROOT/manifest['snapshot']/n)
assert required['book/coverage/inventory.json']=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
for n in ['reports/full-coverage/integration-24.json','reports/full-coverage/browser-checkpoint-24.json','reports/full-coverage/checkpoint-24-manifest.json','reports/full-coverage/checkpoint-24-selection.json','reports/full-coverage/lean-checkpoint-24/verification-original.json','reports/full-coverage/lean-checkpoint-24/verification.json','reports/full-coverage/lean-checkpoint-24/ledger-audit.json','reports/full-coverage/lean-checkpoint-23/verification-original.json']:
 assert H(ROOT/n)==H(PUB/n)==required[n]
retired='reports/full-coverage/lean-checkpoint-22'
rootretired={p.relative_to(ROOT).as_posix():H(p) for p in (ROOT/retired).rglob('*') if p.is_file()}
pubretired={p.relative_to(PUB).as_posix():H(p) for p in (PUB/retired).rglob('*') if p.is_file()}
assert rootretired==pubretired==native['retired_older_audit_original_sha256'] and retired+'/verification-original.json' in rootretired
tracked=subprocess.run(['git','ls-files','-z','--',retired],cwd=PUB,check=True,capture_output=True)
assert {n for n in tracked.stdout.decode().split('\0') if n}==set(rootretired)
subprocess.run(['git','diff','--quiet','HEAD','--',retired],cwd=PUB,check=True)
assert all(not kept(n) for n in rootretired)
assert kept('reports/full-coverage/lean-checkpoint-23/verification-original.json') and kept('reports/full-coverage/lean-checkpoint-24/verification-original.json')
size=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix()))
assert size<900_000_000
assert size==native['prospective_included_website_bytes'],(size,native['prospective_included_website_bytes'])
assert native['selected_sources']==1144 and native['public_theorems']==9279 and native['all31_source52_assets_exact'] is True
assert native['coverage_complete'] is False
closed[str(backup.relative_to(ROOT))]=H(backup)
closed[str(Path(__file__))]=H(Path(__file__))
result={'status':'passed_independent_actual_pages24_configuration_output_review','errors':[],'reviewer':'/root/modules_resume','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'config_sha256':H(config),'actual_config_preparation':ref(reportpath),'entire_original_config_preparation_body_and_time':native,'actual_config_execution':ref(actualpath),'entire_original_actual_config_execution_body_and_time':actual,'previous_configuration':ref(backup),'exact66_original_exclusions_preserved':True,'exact4_new_literal_exclusions':sorted(added),'excluded_count':70,'independently_recomputed_included_website_bytes':size,'publication_budget_bytes':900_000_000,'all31_current52_assets_exact_in_root_publication_and_frozen24':True,'required_frozen_ledger_and_audit_inputs_checked_sha256':required,'retired22_root_publication_git_tracked_HEAD_bytes_exact':True,'current24_and_baseline23_audits_remain_published':True,'selected_sources':1144,'public_theorems':9279,'actual_fresh_kernel_replay_files':13,'actual_identical_reused_files':1131,'closed_evidence_sha256':closed,'scope':'Actual Pages24 configuration output and existing audit/provenance checks only. No new Lean/compiler/global execution, Pages build, push, deployment or live-delivery result is inferred. Native configuration scope distinguishes ROOT working owner bytes from exact frozen/publication ledger bytes.'}
OUTPUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'output':str(OUTPUT),'sha256':H(OUTPUT),'included_website_bytes':size,'config_sha256':H(config)}))

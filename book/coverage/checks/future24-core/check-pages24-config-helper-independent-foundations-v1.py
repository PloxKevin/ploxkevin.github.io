"""Read-only Pages24 preparer review. Never execute the preparer module."""
from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, subprocess
ROOT=Path('/home/oxrexkevin/SafetyBased');PUB=ROOT/'reports/book/publication-repo'
HELPER=ROOT/'book/coverage/checks/root_prepare_pages24_config_v1.py'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
src=HELPER.read_text();tree=ast.parse(src)
before='278d5b40954704026471c5589d8869af8b9a5e5111c5cb070a28e35876ab09e3'
old=(PUB/'_config.yml').read_bytes();assert H(PUB/'_config.yml')==before
exclusions={line[4:]for line in old.decode().splitlines()if line.startswith('  - ')}
assert len(exclusions)==66 and old.decode()=='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'+''.join('  - '+n+'\n'for n in sorted(exclusions))
added={'reports/full-coverage/lean-checkpoint-22','reports/full-coverage/checkpoint-24','reports/full-coverage/owner23-originals-before-owner24-integration-v1','book/coverage/inventory-after-correction52.json'}
assert not added&exclusions
all_exclusions=exclusions|added
assert len(all_exclusions)==70 and all(n and not Path(n).is_absolute()and '..'not in Path(n).parts and not any(c in n for c in '*?[{')for n in all_exclusions)
kept=lambda n:not any(n==e or n.startswith(e+'/')for e in all_exclusions)
manifest=json.loads((ROOT/'reports/full-coverage/checkpoint-23-manifest.json').read_text())
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31 and all(kept(n)for n in assets)
required=['book/coverage/inventory.json','book/coverage/material-corrections.json']+['book/coverage/'+o+'.json'for o in ['core','foundations','applied','modules']]+['reports/full-coverage/integration-24.json','reports/full-coverage/browser-checkpoint-24.json','reports/full-coverage/checkpoint-24-manifest.json','reports/full-coverage/checkpoint-24-selection.json']+['reports/full-coverage/lean-checkpoint-24/'+n for n in ['verification-original.json','verification.json','ledger-audit.json']]+['reports/full-coverage/lean-checkpoint-23/verification-original.json']
assert all(kept(n)for n in required)
for e in added:assert not kept(e)and not kept(e+'/fixture')and kept(e+'-sibling')
retired='reports/full-coverage/lean-checkpoint-22'
archive={p.relative_to(ROOT).as_posix():H(p)for p in (ROOT/retired).rglob('*')if p.is_file()}
assert archive and retired+'/verification-original.json'in archive
assert {p.relative_to(PUB).as_posix():H(p)for p in (PUB/retired).rglob('*')if p.is_file()}==archive
tracked=subprocess.run(['git','ls-files','-z','--',retired],cwd=PUB,check=True,capture_output=True)
assert {n for n in tracked.stdout.decode().split('\0')if n}==set(archive)
subprocess.run(['git','diff','--quiet','HEAD','--',retired],cwd=PUB,check=True)
assert all(not kept(n)for n in archive)
# The reviewed top-level guards must all precede the first backup/config write.
budget_index=next(i for i,n in enumerate(tree.body)if isinstance(n,ast.Assert)and ast.unparse(n.test)=='included < 900000000')
backup_index=next(i for i,n in enumerate(tree.body)if isinstance(n,ast.With))
config_index=next(i for i,n in enumerate(tree.body)if isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and ast.unparse(n.value.func)=='CFG.write_text')
assert budget_index<backup_index<config_index
assert len([n for n in tree.body if isinstance(n,ast.With)])==2
assert "assert selection['new_file_count']==13"in src and "audit['theorem_count']==9279"in src
assert "sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])==13"in src
assert "sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])==1131"in src
assert "assert sha(PUB/n)==sha(ROOT/manifest['snapshot']/n)==s"in src
assert "sha(ROOT/n)==sha(PUB/n)==s"in src
assert '38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'in src
assert '1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'in src
assert "all(c['exit_code']==0 for c in audit['checks'])"in src
assert "'verify-checkpoint24','export-checkpoint24','prepare-publication24'"in src
for stem in ['pages24-config-preparation-v1.json','pages24-config-previous-original-v1.yml']:
    assert not (ROOT/'reports/full-coverage'/stem).exists()
assert (PUB/'_config.yml').read_bytes()==old
ref=lambda p:{'file':str(Path(p).relative_to(ROOT)),'sha256':H(p)}
report={'status':'independent_pages24_config_helper_code_and_literal_exclusion_review_passed','errors':[],'checked_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/config21_next','helper':ref(HELPER),'helper_sha256':H(HELPER),'checker':ref(Path(__file__)),'baseline_configuration_sha256':before,'baseline_literal_exclusion_count':66,'new_literal_exclusions':sorted(added),'prospective_literal_exclusion_count':70,'all31_asset_paths_current_owner_inventory_and_audit_paths_remain_included':True,'old22_archive_original_sha256':archive,'old22_archive_actual_root_publication_and_tracked_HEAD_readonly_check_passed':True,'prewrite_budget_and_actual_evidence_guard_order_checked':True,'expected_future_actual_proof_count':1144,'expected_future_actual_public_export_count':9279,'expected_future_actual_new_kernel_count':13,'expected_future_actual_reused_identical_kernel_count':1131,'required_current24_and_baseline23_audit_paths':required,'scope':'Code-only and read-only literal/archive fixtures. The preparer module was never executed, no config or publication file was written. Real checkpoint24 audit/export/publication-preparation execution and snapshot/current-asset equality, the final measured prospective<900MB budget and independent prepared-config output remain future required guards. No Pages build or live delivery is inferred.'}
out=ROOT/'book/coverage/checks/pages24-config-helper-independent-foundations-review-v1.json'
with out.open('x')as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':report['status'],'report':ref(out),'helper_sha256':H(HELPER)}))

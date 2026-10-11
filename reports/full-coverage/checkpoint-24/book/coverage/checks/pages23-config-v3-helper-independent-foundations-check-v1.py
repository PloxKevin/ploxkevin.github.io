from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,subprocess,difflib,copy
ROOT=Path(__file__).resolve().parents[3];PUB=ROOT/'reports/book/publication-repo'
HELPER=ROOT/'book/coverage/checks/root_prepare_pages23_config_v3.py'
OLD=ROOT/'book/coverage/checks/root_prepare_pages23_config_v2.py'
OUT=ROOT/'book/coverage/checks/pages23-config-v3-helper-independent-foundations-review-v1.json'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();R=lambda p:json.loads(p.read_text())
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':H(p)}
assert not OUT.exists()
assert H(HELPER)=='efb1d71313f940a531c98af69900482ba71713dd4d7cca35a01a1dcca0f0c1c4'
assert H(OLD)=='7256ceed8c875961e8ecc097caf070c9727be2b9099a1c07e112d0e90af97331'
text=HELPER.read_text();tree=ast.parse(text);constants={}
for n in tree.body:
 if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Name):
  try:constants[n.targets[0].id]=ast.literal_eval(n.value)
  except (ValueError,TypeError):pass
pins=constants['OLD_REPORT_INVENTORY_ARCHIVES_SHA256'];assert len(pins)==8
assert all(str(Path(n).parent)=='reports/full-coverage'and Path(n).name.startswith('inventory-')and Path(n).suffix=='.json'for n in pins)
assert all(not any(c in n for c in '*?[{')and'..'not in Path(n).parts and not Path(n).is_absolute()for n in pins)
assert set(pins)=={p.relative_to(PUB).as_posix()for p in (PUB/'reports/full-coverage').glob('inventory*.json')}
assert constants['PREVIOUS22_SHA']=='443a2c117d1caf7d3d0236235b15af1cafc48cfd60ab8f9b60ef5a9c7909e41a'
config=PUB/'_config.yml';before=config.read_bytes();assert H(config)==constants['PREVIOUS22_SHA']
failedp=ROOT/constants['FAILED_CONFIG_V2'];assert H(failedp)==constants['FAILED_CONFIG_V2_SHA'];failed=R(failedp)
assert failed['status']=='failed'and failed['actual_exit_code']==1 and failed['actual_command']==['python3',ref(OLD)['file']]
assert failed['helper_sha256_before']==failed['helper_sha256_after']=={ref(OLD)['file']:H(OLD)}
failedlog=ROOT/failed['log'];assert H(failedlog)==failed['log_sha256']==constants['FAILED_CONFIG_V2_LOG_SHA']
assert 'included_bytes < 900_000_000'in failedlog.read_text()
for version in [2,3]:
 for stem,suffix in [('pages23-config-previous-original','yml'),('pages23-config-previous-original','json'),('pages23-config-preparation','json')]:assert not(ROOT/f'reports/full-coverage/{stem}-v{version}.{suffix}').exists()
oldpeerp=ROOT/'book/coverage/checks/future23-core/original-pages-config-code-peer/pages23-config-v2-independent-modules-code-review-v1.json'
if not oldpeerp.exists():oldpeerp=Path('/tmp/pages23-config-v2-independent-modules-code-review-v1.json')
oldpeer=R(oldpeerp);assert'passed'in oldpeer['status']and oldpeer['errors']==[]and oldpeer['helper']==ref(OLD)
for n,h in pins.items():assert H(ROOT/n)==H(PUB/n)==h,n
tracked=subprocess.run(['git','ls-files','-z','--',*sorted(pins)],cwd=PUB,check=True,stdout=subprocess.PIPE).stdout
assert set(tracked.decode().split('\0'))-{''}==set(pins)
subprocess.run(['git','diff','--quiet','HEAD','--',*sorted(pins)],cwd=PUB,check=True)
archivebytes=sum((PUB/n).stat().st_size for n in pins);assert archivebytes==88304107
manifestp=ROOT/'reports/full-coverage/checkpoint-23-manifest.json';manifest=R(manifestp);selectionp=ROOT/'reports/full-coverage/checkpoint-23-selection.json';selection=R(selectionp)
auditp=ROOT/'reports/full-coverage/lean-checkpoint-23/verification-original.json';audit=R(auditp)
oldmanifest=R(ROOT/'reports/full-coverage/checkpoint-22-manifest.json');oldprep=R(ROOT/'reports/full-coverage/pages22-config-preparation-v2.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'and manifest['selection_sha256']==H(selectionp)
assert len(manifest['proof_files'])==selection['proof_file_count']==audit['proof_file_count']==1131 and audit['theorem_count']==9193 and audit['status']=='passed'
assert len(audit['declarations'])==9193 and all(r['exit_code']==0 for r in audit['checks'])
assert len(oldmanifest['proof_files'])==1113 and set(oldmanifest['proof_files'])<=set(manifest['proof_files'])and len(set(manifest['proof_files'])-set(oldmanifest['proof_files']))==18
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')};oldassets={n:h for n,h in oldmanifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')}
assert len(assets)==31 and assets=={**oldassets,**constants['SOURCE51_REVISIONS']}
for n,h in assets.items():assert H(ROOT/n)==H(PUB/n)==H(ROOT/'reports/full-coverage/checkpoint-23'/n)==h
for n,h in oldassets.items():assert H(ROOT/'reports/full-coverage/checkpoint-22'/n)==h
inv='book/coverage/inventory.json';assert H(ROOT/inv)==H(PUB/inv)==constants['INVENTORY_SHA']==H(ROOT/'book/coverage/inventory-after-correction51.json')
ownerresults={}
for owner in constants['OWNERS']:
 n='book/coverage/'+owner+'.json';working=R(ROOT/n);frozen=R(PUB/n);beforeworking=copy.deepcopy(working)
 assert H(ROOT/n)==manifest['working_inputs_sha256'][n]and H(PUB/n)==H(ROOT/'reports/full-coverage/checkpoint-23'/n)==manifest['frozen_inputs_sha256'][n]
 removed=manifest['excluded_unreferenced_ledger_metadata'][owner]
 assert removed==(constants['APPLIED_UNSELECTED_METADATA']if owner=='applied'else[])
 assert set(working['proof_files'])-set(manifest['proof_files'])==set(removed)
 if isinstance(working['proof_files'],dict):working['proof_files']={k:v for k,v in working['proof_files'].items()if k in manifest['proof_files']}
 else:working['proof_files']=[k for k in working['proof_files']if k in manifest['proof_files']]
 if'proof_sha256'in working:working['proof_sha256']={k:v for k,v in working['proof_sha256'].items()if k in manifest['proof_files']}
 assert working==frozen
 ownerresults[n]={'working_sha256':H(ROOT/n),'frozen_publication_sha256':H(PUB/n),'exact_removed_unused_metadata':removed,'all_claims_and_exercises_full_JSON_equal':True}
oldexclude={line[4:]for line in before.decode().splitlines()if line.startswith('  - ')};assert len(oldexclude)==52 and oldexclude==set(oldprep['exclusions'])
excluded=oldexclude|{'reports/full-coverage/checkpoint-23','reports/full-coverage/lean-checkpoint-21','reports/full-coverage/owner22-originals-before-owner23-integration-v1'}
excluded|={p.relative_to(PUB).as_posix()for p in (PUB/'book/coverage').glob('inventory*.json')if p.name!='inventory.json'}
excluded|=set(pins)
assert all(not any(c in n for c in '*?[{')and'..'not in Path(n).parts and not Path(n).is_absolute()for n in excluded)
def kept(name):return all(name!=x and not name.startswith(x+'/')for x in excluded)
pure=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='kept');scope={'excluded':excluded}
exec(compile(ast.Module(body=[pure],type_ignores=[]),'<reviewed-pure-path-function>','exec'),scope)
fixtures={inv:True,'SafeLearning/cmdp.html':True,'SafeLearning/lyapunov-mpc.html':True,'reports/full-coverage/lean-checkpoint-23/verification-original.json':True,'reports/full-coverage/lean-checkpoint-22/verification-original.json':True,'reports/full-coverage/lean-checkpoint-21/verification-original.json':False,'reports/full-coverage/lean-checkpoint-210/verification-original.json':True,'reports/full-coverage/checkpoint-23/file':False,'reports/full-coverage/checkpoint-230/file':True,'book/coverage/inventory-after-correction51.json':False,'reports/full-coverage/inventory-after-correction16.json.extra':True,'reports/full-coverage/inventory-after-correction160.json':True,**{n:False for n in pins},**{n:True for n in ownerresults}}
for n,v in fixtures.items():assert kept(n)is v and scope['kept'](n)is v,n
required=set(assets)|set(ownerresults)|{inv,'reports/full-coverage/README.md','reports/full-coverage/integration-23.json','reports/full-coverage/browser-checkpoint-23.json','reports/full-coverage/checkpoint-23-manifest.json','reports/full-coverage/checkpoint-23-selection.json','reports/full-coverage/lean-checkpoint-23/verification-original.json','reports/full-coverage/lean-checkpoint-23/verification.json','reports/full-coverage/lean-checkpoint-23/ledger-audit.json','reports/full-coverage/owner23-reviewed-candidate-integration-v1.json'}
for n in required:
 assert kept(n)and(ROOT/n).is_file()and(PUB/n).is_file(),n
 if n not in ownerresults and n!='reports/full-coverage/README.md':assert H(ROOT/n)==H(PUB/n),n
archival={n:h for n,h in R(ROOT/'reports/full-coverage/checkpoint-21-manifest.json')['frozen_inputs_sha256'].items()if n.startswith('book/coverage/checks/future22-monitoring/')};assert len(archival)==32
for n,h in archival.items():assert H(ROOT/n)==H(PUB/n)==h and not kept(n)and n not in manifest['proof_files']
older='reports/full-coverage/lean-checkpoint-21';olderfiles={p.relative_to(ROOT).as_posix():H(p)for p in(ROOT/older).rglob('*')if p.is_file()}
assert olderfiles=={p.relative_to(PUB).as_posix():H(p)for p in(PUB/older).rglob('*')if p.is_file()}
trackolder=subprocess.run(['git','ls-files','-z','--',older],cwd=PUB,check=True,stdout=subprocess.PIPE).stdout
assert set(trackolder.decode().split('\0'))-{''}==set(olderfiles)
subprocess.run(['git','diff','--quiet','HEAD','--',older],cwd=PUB,check=True)
configbytes=('# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'+''.join('  - '+n+'\n'for n in sorted(excluded))).encode()
included=sum(p.stat().st_size for p in PUB.rglob('*')if p.is_file()and'.git'not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix()))-len(before)+len(configbytes)
assert included<900000000
writes=[]
for n in ast.walk(tree):
 if isinstance(n,ast.Call)and isinstance(n.func,ast.Attribute)and n.func.attr in ['open','write_text','write_bytes']:
  if n.func.attr!='open'or(n.args and isinstance(n.args[0],ast.Constant)and isinstance(n.args[0].value,str)and any(c in n.args[0].value for c in 'wax')):writes.append(ast.unparse(n.func.value))
assert set(writes)=={'PREVIOUS','PREVIOUS_RECORD','CONFIG','REPORT'}
assert text.index('assert included_bytes < 900_000_000')<text.index('with PREVIOUS.open("xb")')<text.index('CONFIG.write_text(new_config)')
assert text.index('tracked_old_inventories =')<text.index('with PREVIOUS.open("xb")')
for fragment in ['assert sha(ROOT / name) == sha(PUB / name) == digest, name','failed_config_v2["status"] == "failed" and failed_config_v2["actual_exit_code"] == 1','working_ledger == frozen_ledger','assert all(not kept(name) for name in OLD_REPORT_INVENTORY_ARCHIVES_SHA256)'] :assert fragment in text
assert H(config)==constants['PREVIOUS22_SHA']and H(HELPER)=='efb1d71313f940a531c98af69900482ba71713dd4d7cca35a01a1dcca0f0c1c4'
report={'status':'passed_independent_new_pages23_config_v3_code_and_readonly_prospective_budget_review_requires_actual_execution_and_output_peer','reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(HELPER),'helper_sha256':H(HELPER),'checker':ref(Path(__file__)),'original_executed_v2_helper':ref(OLD),'original_independent_v2_code_review':{'file':str(oldpeerp),'sha256':H(oldpeerp)},'entire_original_v2_code_review_body_and_time':oldpeer,'genuine_failed_config_v2_execution':ref(failedp),'entire_original_failed_config_v2_record_and_time':failed,'genuine_failed_config_v2_raw_log':ref(failedlog),'newly_excluded_exact_old_report_inventory_paths_sha256':pins,'old_report_inventory_bytes':archivebytes,'original52_literal_exclusions_retained':True,'prospective_literal_exclusions':sorted(excluded),'prospective_excluded_count':len(excluded),'independently_computed_prospective_included_bytes':included,'budget_limit_bytes':900000000,'pure_boundary_fixture_count':len(fixtures),'exact_all31_current51_assets':assets,'exact_working_frozen_owner_normalization':ownerresults,'original32_archival_trials_retained_unselected':archival,'all_old_report_inventory_and_older21_audit_bytes_equal_ROOT_PUB_tracked_HEAD':True,'required_current23_and_baseline22_paths_still_included':sorted(required),'original_v2_and_new_v3_preparation_outputs_absent_at_review':True,'complete_new_helper_source_read':text,'exact_unified_delta_from_executed_v2':''.join(difflib.unified_diff(OLD.read_text().splitlines(keepends=True),text.splitlines(keepends=True),fromfile=ref(OLD)['file'],tofile=ref(HELPER)['file'])),'errors':[],'coverage_complete':False,'scope':['Author-independent new version3 delta and whole new code mechanics review only. The reviewer authored version2; its complete prior author-independent Module peer is retained separately.','Only eight pinned old immediate report inventory files are newly excluded, after exact original/PUB/tracked clean HEAD checks; no wildcard YAML exclusion or current audit, inventory, owner or asset exclusion.','Prospective budget is measured read-only from the current publication tree and proposed literal YAML; the production helper was not executed, no configuration/PUB/Git mutation, and no actual Pages build/live claim. Root must run newversion3 and Modules must independently review its real output.']}
with OUT.open('x')as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'report':ref(OUT),'prospective_included_bytes':included,'excluded_count':len(excluded),'new_archive_bytes':archivebytes}))

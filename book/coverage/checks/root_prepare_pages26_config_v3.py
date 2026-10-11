"""Prepare exact Pages26 archive exclusions after actual audit and publication copy."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, subprocess
ROOT=Path(__file__).resolve().parents[3]
PUB=ROOT/'reports/book/publication-repo';CFG=PUB/'_config.yml'
BEFORE='7cbf6c4a7aa5c2f349b83025018e6a27898e567e1822f3aeab4d064fbfecb0af'
REPORT='reports/full-coverage/pages26-config-preparation-v1.json'
BACKUP='reports/full-coverage/pages26-config-previous-original-v1.yml'
BACKUP_RECORD='reports/full-coverage/pages26-config-previous-original-v1.json'
BASE_MANIFEST_SHA='0329596719e09459730f34c9c84e9bacf4f3698a7c1699c4f848cef975ee5363'
RETIRED_DIR='reports/full-coverage/lean-checkpoint-24'
RETIRED_FILES={'reports/full-coverage/checkpoint-24-manifest.json':'5e0a58f71b685edbd3bbf7c965a2fda3ffd18f8edfde75c5bf810c7bb63d18e0',
    'reports/full-coverage/checkpoint-24-selection.json':'9dd0a0cb80c54b728c09fc12e4327efdae621f94b5710e7a97c0d13fe92d6314',
    'reports/full-coverage/checkpoint-25-manifest.json':'0329596719e09459730f34c9c84e9bacf4f3698a7c1699c4f848cef975ee5363',
    'reports/full-coverage/checkpoint-25-selection.json':'3559445215b6b5b9bd176363ded8d307a93724b2b68c1ba9845dc709a3b4ddff'}
NEW_DUPLICATE_OR_SNAPSHOT_EXCLUSIONS={'book/coverage/inventory-after-correction53.json',
    'book/coverage/inventory-before-correction53.json','reports/full-coverage/checkpoint-26',
    'reports/full-coverage/owner25-originals-before-owner26-integration-v1'}

RETIRED_SCREENSHOT_DIRS={
    'reports/full-coverage/browser-artifacts-19',
    'reports/full-coverage/browser-artifacts-20',
    'reports/full-coverage/browser-artifacts-21',
    'reports/full-coverage/browser-artifacts-22',
    'reports/full-coverage/browser-artifacts-23',
    'reports/full-coverage/browser-artifacts-24',
}
SCREENSHOT_ARCHIVE_OBSERVATION='book/coverage/checks/future26-core/pages26-six-older-screenshot-archives-readonly-observation-v1.json'
SCREENSHOT_ARCHIVE_OBSERVATION_SHA='d06fcb35ef030e2ef97c530777ea0d6dce21f755ae12e6d77e775028841b8ed7'
REAL_PREPARED_BUDGET_OBSERVATION='book/coverage/checks/future26-core/pages26-real-prepared-budget-original-v1.json'
REAL_PREPARED_BUDGET_OBSERVATION_SHA='84b9040cbbd42cc071aaffc2167d4e91a6d087a3d7bc5fc6f63cc224b2ef12b5'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def ref(n):return {'file':n,'sha256':sha(ROOT/n)}
def zero(d):
    values=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
    assert values and all(type(x) is int and x==0 for x in values)
def actual(stem):
    d=read('reports/full-coverage/'+stem+'-execution-v1.json');zero(d)
    assert sha(ROOT/d['log'])==d['log_sha256'];return d
def tracked_exact(name,files):
    d=subprocess.run(['git','ls-files','-z','--',name],cwd=PUB,check=True,capture_output=True)
    assert {n for n in d.stdout.decode().split('\0') if n}==set(files)
    subprocess.run(['git','diff','--quiet','HEAD','--',name],cwd=PUB,check=True)
    for n,h in files.items():assert sha(ROOT/n)==sha(PUB/n)==h
assert sha(ROOT/'book/coverage/checks/root_prepare_pages26_config_v1.py')=='b482976580808d3c4114d34bc97c585144ab70fa592335badaf999a5cf6e331b'
assert sha(ROOT/'book/coverage/checks/pages26-config-helper-independent-foundations-review-v1.json')=='12afd00cd1a195801261e377ec61c98c7fdef9c78bedaea25c98dfc8970fec45'
assert sha(ROOT/'book/coverage/checks/root_prepare_pages26_config_v2.py')=='7beca7f7261101b5adb8ba9b7f0603a31d7343c94ddf2057a231a45fa53b5d73'
assert sha(ROOT/'book/coverage/checks/pages26-config-helper-independent-modules-review-v2.json')=='11df6187967d961da129f74a9d2a19204d64da822b2d8e513003f27a568d55c7'
assert sha(ROOT/SCREENSHOT_ARCHIVE_OBSERVATION)==SCREENSHOT_ARCHIVE_OBSERVATION_SHA
assert sha(ROOT/REAL_PREPARED_BUDGET_OBSERVATION)==REAL_PREPARED_BUDGET_OBSERVATION_SHA
archive_observation=read(SCREENSHOT_ARCHIVE_OBSERVATION)
assert archive_observation['status']=='read_only_exact_six_older_screenshot_archives_root_pub_tracked_HEAD_observed'
assert set(archive_observation['archival_directories'])==RETIRED_SCREENSHOT_DIRS
budget_observation=read(REAL_PREPARED_BUDGET_OBSERVATION)
assert budget_observation['status']=='read_only_real_prepared_publication26_byte_measurement'
assert budget_observation['mode']=='prepared' and budget_observation['literal_exclusion_count']==110
assert budget_observation['config_helper']==ref('book/coverage/checks/root_prepare_pages26_config_v2.py')
assert budget_observation['currently_observed_prospective_website_bytes']==987112720
assert budget_observation['explicit_reserve_for_future_missing_records_and_changes_bytes']==5000000
assert budget_observation['needed_freed_bytes_including_reserve']==142112721
assert all(not (ROOT/n).exists() for n in (REPORT,BACKUP,BACKUP_RECORD))
assert sha(CFG)==BEFORE
old=CFG.read_bytes();header='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'
exclusions={line[4:] for line in old.decode().splitlines() if line.startswith('  - ')}
assert len(exclusions)==101 and old.decode()==header+''.join('  - '+n+'\n' for n in sorted(exclusions))
assert sha(ROOT/'reports/full-coverage/checkpoint-25-manifest.json')==BASE_MANIFEST_SHA
manifest=read('reports/full-coverage/checkpoint-26-manifest.json')
selection=read('reports/full-coverage/checkpoint-26-selection.json')
audit=read('reports/full-coverage/lean-checkpoint-26/verification-original.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert manifest['selection_sha256']==sha(ROOT/'reports/full-coverage/checkpoint-26-selection.json')
assert manifest['proof_files']==selection['proof_files'] and len(manifest['proof_files'])==selection['proof_file_count']==audit['proof_file_count']==1167
assert selection['new_file_count']==11 and audit['status']=='passed' and audit['theorem_count']==9503
assert len(audit['declarations'])==len(audit['axiom_dependencies'])==9503
assert all(type(c['exit_code']) is int and c['exit_code']==0 for c in audit['checks'])
assert sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])==11
assert sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])==1156
for stem in ('verify-checkpoint26','export-checkpoint26','prepare-publication26'):actual(stem)
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets)==31 and assets['SafeLearning/lyapunov-mpc.html']=='5e21c5319d41968468781ee0bf9b18aec5147666f764827f3a96e9e73d0138af'
required=dict(assets);working_ledgers={};published_ledgers={}
for n,h in assets.items():assert sha(ROOT/n)==sha(PUB/n)==h
for n in ('book/coverage/inventory.json','book/coverage/material-corrections.json'):
    h=manifest['frozen_inputs_sha256'][n]
    assert sha(ROOT/n)==sha(PUB/n)==sha(ROOT/manifest['snapshot']/n)==h;required[n]=h
assert required['book/coverage/inventory.json']=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
for owner in ('core','foundations','applied','modules'):
    n='book/coverage/'+owner+'.json';working=manifest['working_inputs_sha256'][n];frozen=manifest['frozen_inputs_sha256'][n]
    assert sha(ROOT/n)==working and sha(PUB/n)==sha(ROOT/manifest['snapshot']/n)==frozen
    normalized=copy.deepcopy(read(n));removed=manifest['excluded_unreferenced_ledger_metadata'][owner]
    assert removed==read('reports/full-coverage/checkpoint-25-manifest.json')['excluded_unreferenced_ledger_metadata'][owner]
    assert len(removed)==(3 if owner=='applied' else 0)
    for source in removed:
        assert source in normalized['proof_files'] and source not in manifest['proof_files'];normalized['proof_files'].pop(source)
    assert normalized==json.loads((PUB/n).read_text())
    required[n]=frozen;working_ledgers[n]=working;published_ledgers[n]=frozen
for n in ('reports/full-coverage/integration-26.json','reports/full-coverage/browser-checkpoint-26.json',
    'reports/full-coverage/checkpoint-26-manifest.json','reports/full-coverage/checkpoint-26-selection.json',
    'reports/full-coverage/lean-checkpoint-26/verification-original.json','reports/full-coverage/lean-checkpoint-26/verification.json',
    'reports/full-coverage/lean-checkpoint-26/ledger-audit.json','reports/full-coverage/lean-checkpoint-25/verification-original.json'):
    assert sha(ROOT/n)==sha(PUB/n);required[n]=sha(PUB/n)
retired={p.relative_to(ROOT).as_posix():sha(p) for p in (ROOT/RETIRED_DIR).rglob('*') if p.is_file()}
assert retired and RETIRED_DIR+'/verification-original.json' in retired
assert {p.relative_to(PUB).as_posix():sha(p) for p in (PUB/RETIRED_DIR).rglob('*') if p.is_file()}==retired
tracked_exact(RETIRED_DIR,retired)
for n,h in RETIRED_FILES.items():tracked_exact(n,{n:h})
retired_screenshots={};retired_screenshot_bytes=0
for directory in sorted(RETIRED_SCREENSHOT_DIRS):
    observed=archive_observation['archival_directories'][directory]
    expected=observed['exact_files_sha256']
    assert expected and all(n.startswith(directory+'/') and Path(n).suffix=='.png' for n in expected)
    assert all(str(Path(n))==n and not Path(n).is_absolute() and '..' not in Path(n).parts for n in expected)
    for base in (ROOT,PUB):
        paths=list((base/directory).rglob('*'))
        assert not any(p.is_symlink() for p in paths)
        assert {p.relative_to(base).as_posix():sha(p) for p in paths if p.is_file()}==expected
    assert len(expected)==observed['file_count']==48
    assert hashlib.sha256(json.dumps(expected,sort_keys=True,separators=(',',':')).encode()).hexdigest()==observed['sorted_exact_path_sha256_map_fingerprint']
    size=sum((ROOT/n).stat().st_size for n in expected)
    assert size==observed['byte_count'] and size==sum((PUB/n).stat().st_size for n in expected)
    tracked_exact(directory,expected)
    retired_screenshots.update(expected);retired_screenshot_bytes+=size
assert len(retired_screenshots)==archive_observation['total_files']==288
assert retired_screenshot_bytes==archive_observation['total_bytes']==169960594
assert retired_screenshot_bytes>budget_observation['needed_freed_bytes_including_reserve']
current_browser_inputs=read('reports/full-coverage/browser-corrections-26-inputs.json')
assert len(current_browser_inputs['screenshot_aliases'])==48
for row in current_browser_inputs['screenshot_aliases']:
    n,h=row['file'],row['sha256']
    assert n.startswith('reports/full-coverage/browser-artifacts-26/')
    assert sha(ROOT/n)==sha(PUB/n)==h;required[n]=h

for n in ('book/coverage/inventory-after-correction53.json','book/coverage/inventory-before-correction53.json'):
    assert sha(ROOT/n)==sha(PUB/n)==manifest['frozen_inputs_sha256'][n]
added=set(RETIRED_FILES)|{RETIRED_DIR}|NEW_DUPLICATE_OR_SNAPSHOT_EXCLUSIONS|RETIRED_SCREENSHOT_DIRS
assert len(added)==15 and not added&exclusions
exclusions.update(added);assert len(exclusions)==116
assert all(n and not Path(n).is_absolute() and '..' not in Path(n).parts and not any(c in n for c in '*?[{') for n in exclusions)
def kept(n):return not any(n==e or n.startswith(e+'/') for e in exclusions)
assert all(kept(n) for n in required)
assert all(not kept(n) for n in retired) and all(not kept(n) for n in RETIRED_FILES)
assert all(not kept(n) for n in retired_screenshots)
assert kept('reports/full-coverage/browser-artifacts-25/example.png') and kept('reports/full-coverage/browser-artifacts-26/example.png')
assert kept('reports/full-coverage/browser-artifacts-source53-26-v1/example.png')
after=(header+''.join('  - '+n+'\n' for n in sorted(exclusions))).encode()
included=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and kept(p.relative_to(PUB).as_posix()))-len(old)+len(after)
report={'status':'passed_exact_pages26_archival_configuration_preparation_requires_actual_pages_build',
    'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(str(Path(__file__).relative_to(ROOT))),
    'previous_configuration':{'file':BACKUP,'sha256':BEFORE},'config_sha256':hashlib.sha256(after).hexdigest(),
    'exclusions':sorted(exclusions),'excluded_count':116,'new_literal_exclusions':sorted(added),
    'retired_older_audit_dir':RETIRED_DIR,'retired_older_audit_file_count':len(retired),
    'retired_older_audit_sorted_exact_path_sha256_map_fingerprint':hashlib.sha256(json.dumps(retired,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
    'retired_older_manifest_selection_exact_sha256':RETIRED_FILES,
    'retired_baseline25_direct_archives_exact_bytes':{'reports/full-coverage/checkpoint-25-manifest.json': 56004385, 'reports/full-coverage/checkpoint-25-selection.json': 41605130},
    'original_unexecuted_config_helper':ref('book/coverage/checks/root_prepare_pages26_config_v1.py'),
    'original_config_helper_independent_code_review':ref('book/coverage/checks/pages26-config-helper-independent-foundations-review-v1.json'),'retired_older_archives_exact_in_root_publication_and_tracked_HEAD':True,
    'new_current53_duplicate_and_snapshot_exclusions':sorted(NEW_DUPLICATE_OR_SNAPSHOT_EXCLUSIONS),
    'original_unexecuted_config2_helper':ref('book/coverage/checks/root_prepare_pages26_config_v2.py'),
    'original_config2_independent_code_review':ref('book/coverage/checks/pages26-config-helper-independent-modules-review-v2.json'),
    'original_real_prepared_budget_observation':ref(REAL_PREPARED_BUDGET_OBSERVATION),
    'exact_older_screenshot_archive_observation':ref(SCREENSHOT_ARCHIVE_OBSERVATION),
    'retired_older_screenshot_directories':sorted(RETIRED_SCREENSHOT_DIRS),
    'retired_older_screenshot_file_count':len(retired_screenshots),
    'retired_older_screenshot_archive_bytes':retired_screenshot_bytes,
    'retired_older_screenshot_sorted_exact_path_sha256_map_fingerprint':hashlib.sha256(json.dumps(retired_screenshots,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
    'current26_screenshot_aliases48_remain_public_exact':True,

    'required_publication_files_sha256':required,'working_ledger_sha256':working_ledgers,
    'published_frozen_ledger_sha256':published_ledgers,'exact_original_metadata_removals':manifest['excluded_unreferenced_ledger_metadata'],
    'prospective_included_website_bytes_before_new_native_records':included,'website_budget_bytes':850000000,'coverage_complete':False,
    'scope':'Literal website exclusions only. Completed24 audit archives and older24/25 direct manifest/selection files remain exact in Root, publication and tracked Git HEAD. Current26 audit/manifest/selection, baseline25 Lean audit, current53 inventory, site assets and owner ledgers stay included. The original108/110-exclusion helpers remain unexecuted and exact. Six literal older19–24 screenshot directories (288 exact originals) remain in Root, publication and tracked Git HEAD; only their website inclusion changes. Current25/26 browser audits, current26 screenshots, source53 fresh-capture originals and all current53 book assets remain included. Actual Pages and live checks remain required.'}
assert included<850000000
record={'status':'previous_exact_pages_configuration_preserved','original_publication_path':'_config.yml',
    'original_sha256':BEFORE,'immutable_original_byte_copy':BACKUP}
for n,b in ((BACKUP,old),(BACKUP_RECORD,(json.dumps(record,indent=2)+'\n').encode()),(REPORT,(json.dumps(report,indent=2)+'\n').encode())):
    with (ROOT/n).open('xb') as f:f.write(b)
assert sha(CFG)==BEFORE;CFG.write_bytes(after);assert sha(CFG)==report['config_sha256']
print(json.dumps({'status':'passed','native_report':ref(REPORT),'exclusions':116,'projected_bytes':included,'config_sha256':sha(CFG)}))

#!/usr/bin/env python3
"""Draft: literal Pages27 archival exclusions after real audit/publication preparation.

Importing this module performs no filesystem mutation. Root must install the exact
reviewed helper and execute --apply only after all genuine prerequisites exist.
"""
from pathlib import Path
from datetime import datetime,timezone
import argparse,copy,hashlib,json,subprocess
ROOT=Path('/home/oxrexkevin/SafetyBased')
PUB=ROOT/'reports/book/publication-repo'
HELPER='book/coverage/checks/root_prepare_pages27_config_v2.py'
REPORT='reports/full-coverage/pages27-config-preparation-v1.json'
BACKUP='reports/full-coverage/pages27-config-previous-original-v1.yml'
BACKUP_RECORD='reports/full-coverage/pages27-config-previous-original-v1.json'
BEFORE='1c14f454e5645b9eab1b68ccadf7ea4420cd66b739072c48f65316f6b2bd6bc6'
INVENTORY55='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
CORRECTIONS55='21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'
BUDGET=850000000
HEADER='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'
RETIRED_COMPLETED26_FILES={
 'reports/full-coverage/checkpoint-26-manifest.json':'ef777b585d9654e5dd784160dd4e9502eaae230d1f4fefcd9bdb2458c347f896',
 'reports/full-coverage/checkpoint-26-selection.json':'12527ed93a283e1b37a491f7f799ac04e6217b1d7e20aee74116b312e580e23f',
}
DUPLICATE_INVENTORIES={
 'book/coverage/inventory-before-correction54.json':'4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be',
 'book/coverage/inventory-after-correction54.json':'5b7540b2b62cc0a51d2604ce24c170cd6a228f42f4f13ba34f0b695836be8862',
 'book/coverage/inventory-before-correction55.json':'5b7540b2b62cc0a51d2604ce24c170cd6a228f42f4f13ba34f0b695836be8862',
 'book/coverage/inventory-after-correction55.json':INVENTORY55,
}
NEW_LITERAL_EXCLUSIONS=set(RETIRED_COMPLETED26_FILES)|set(DUPLICATE_INVENTORIES)|{
 'reports/full-coverage/checkpoint-27',
 'reports/full-coverage/owner26-originals-before-owner27-integration-v1',
}
assert len(NEW_LITERAL_EXCLUSIONS)==8

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def canonical_name(n):
 assert type(n) is str and n and str(Path(n))==n and not Path(n).is_absolute()
 assert '..' not in Path(n).parts and not any(c in n for c in '*?[{\x00')
 return n

def safe(root,n):
 n=canonical_name(n);p=root/n
 assert p.resolve().is_relative_to(root.resolve()) and not p.is_symlink(),n
 return p

def read(root,n):return json.loads(safe(root,n).read_text())
def ref(root,n):return {'file':n,'sha256':sha(safe(root,n))}
def zero(d):
 keys=[k for k in ('actual_exit_code','exit_code') if k in d]
 assert keys and all(type(d[k]) is int and d[k]==0 for k in keys)
def actual(root,name,command):
 d=read(root,name);zero(d)
 cmds=[d[k] for k in ('actual_command','command') if k in d]
 assert cmds and all(v==command for v in cmds)
 work=[d[k] for k in ('actual_workdir','working_directory','cwd') if k in d]
 assert work and all(v==str(root) for v in work)
 logs=[d[k] for k in ('log','raw_log') if k in d]
 assert logs and all(v==logs[0] for v in logs)
 digests=[d[k] for k in ('log_sha256','raw_log_sha256') if k in d]
 assert digests and all(v==digests[0] for v in digests)
 assert sha(safe(root,logs[0]))==digests[0]
 return d

def same(root,pub,n,h):
 assert sha(safe(root,n))==sha(safe(pub,n))==h,n

def tracked_exact(root,pub,n,h):
 same(root,pub,n,h)
 tracked=subprocess.run(['git','ls-files','-z','--',n],cwd=pub,check=True,capture_output=True).stdout.decode().split('\0')
 assert [v for v in tracked if v]==[n]
 head=subprocess.run(['git','show','HEAD:'+n],cwd=pub,check=True,capture_output=True).stdout
 assert hashlib.sha256(head).hexdigest()==h,n
 subprocess.run(['git','diff','--quiet','HEAD','--',n],cwd=pub,check=True)

def included_tree_bytes(pub,exclusions):
 total=0
 for p in pub.rglob('*'):
  rel=p.relative_to(pub)
  if '.git' in rel.parts:continue
  assert not p.is_symlink(),str(rel)
  if p.is_file() and kept(rel.as_posix(),exclusions):total+=p.stat().st_size
 return total

def kept(n,exclusions):return not any(n==e or n.startswith(e+'/') for e in exclusions)
def encoded(d):return (json.dumps(d,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n').encode()

def prepare(root=ROOT,pub=PUB):
 # Read-only preparation: every gate and actual-byte budget check precedes writes.
 for n in (REPORT,BACKUP,BACKUP_RECORD):
  assert not (root/n).exists() and not (pub/n).exists(),n
 cfg=safe(pub,'_config.yml');old=cfg.read_bytes();assert sha(cfg)==BEFORE
 exclusions={line[4:] for line in old.decode().splitlines() if line.startswith('  - ')}
 assert len(exclusions)==116 and old.decode()==HEADER+''.join('  - '+n+'\n' for n in sorted(exclusions))
 for n in exclusions|NEW_LITERAL_EXCLUSIONS:canonical_name(n)
 assert not exclusions&NEW_LITERAL_EXCLUSIONS
 exclusions|=NEW_LITERAL_EXCLUSIONS;assert len(exclusions)==124
 after=(HEADER+''.join('  - '+n+'\n' for n in sorted(exclusions))).encode()
 manifest_name='reports/full-coverage/checkpoint-27-manifest.json'
 selection_name='reports/full-coverage/checkpoint-27-selection.json'
 audit_name='reports/full-coverage/lean-checkpoint-27/verification-original.json'
 manifest=read(root,manifest_name);selection=read(root,selection_name);audit=read(root,audit_name)
 assert manifest['status']=='formal_verification_passed_partial_coverage'
 assert manifest['selection_sha256']==sha(safe(root,selection_name))
 assert manifest['proof_files']==selection['proof_files']
 assert len(manifest['proof_files'])==selection['proof_file_count']==audit['proof_file_count']==1175
 assert selection['new_file_count']==8 and audit['status']=='passed' and audit['theorem_count']==9644
 assert len(audit['declarations'])==len(audit['axiom_dependencies'])==9644
 assert all(type(v['exit_code']) is int and v['exit_code']==0 for v in audit['checks'])
 assert sum(v.get('evidence_mode')=='fresh_kernel_replay' for v in audit['checks'])==8
 assert sum(v.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for v in audit['checks'])==1167
 actual_refs={}
 for stem,cmd in (
  ('verify-checkpoint27',['python3','reports/full-coverage/checkpoint-27/verification/lean/verify.py','--reuse-kernel-from',str(root/'reports/full-coverage/checkpoint-26')]),
  ('export-checkpoint27',['python3','book/coverage/export_audit.py','--snapshot','reports/full-coverage/checkpoint-27','--output','reports/full-coverage/lean-checkpoint-27']),
  ('prepare-publication27',['python3','book/coverage/prepare_publication.py','27']),
 ):
  n='reports/full-coverage/'+stem+'-execution-v1.json';actual(root,n,cmd);actual_refs[stem]=ref(root,n)
 assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
 assert len(assets)==31
 assert assets['SafeLearning/lyapunov-mpc.html']=='63a1ac8be7f5cf8b490dd1dd872d416affee95f6de0d5ba3c1c618f4b86cd79f'
 assert assets['SafeLearning/verification.html']=='d01ce44636cd6100bef100a0f466539d61ab6d6c3e8ab64b0d39c7dbdf740f53'
 required=dict(assets)
 for n,h in assets.items():same(root,pub,n,h)
 for n,h in {'book/coverage/inventory.json':INVENTORY55,'book/coverage/material-corrections.json':CORRECTIONS55}.items():
  assert manifest['frozen_inputs_sha256'][n]==h
  same(root,pub,n,h);assert sha(safe(root,manifest['snapshot']+'/'+n))==h;required[n]=h
 old_manifest=read(root,'reports/full-coverage/checkpoint-26-manifest.json')
 working={};published={}
 for owner in ('core','foundations','applied','modules'):
  n='book/coverage/'+owner+'.json';w=manifest['working_inputs_sha256'][n];f=manifest['frozen_inputs_sha256'][n]
  assert sha(safe(root,n))==w and sha(safe(pub,n))==sha(safe(root,manifest['snapshot']+'/'+n))==f
  removed=manifest['excluded_unreferenced_ledger_metadata'][owner]
  assert removed==old_manifest['excluded_unreferenced_ledger_metadata'][owner]
  assert len(removed)==(3 if owner=='applied' else 0)
  body=copy.deepcopy(read(root,n))
  for source in removed:
   assert source in body['proof_files'] and source not in manifest['proof_files'];body['proof_files'].pop(source)
  assert body==read(pub,n)
  required[n]=f;working[n]=w;published[n]=f
 n='book/coverage/applied-promotions.json';h=manifest['working_inputs_sha256'][n]
 assert h==manifest['frozen_inputs_sha256'][n];same(root,pub,n,h);required[n]=h
 for n in (manifest_name,selection_name,audit_name,'reports/full-coverage/integration-27.json',
           'reports/full-coverage/lean-checkpoint-26/verification-original.json',
           'reports/full-coverage/browser-checkpoint-27.json','reports/full-coverage/browser-corrections-27-inputs.json'):
  h=sha(safe(root,n));same(root,pub,n,h);required[n]=h
 # Every current audit download remains included, without guessing a partial list.
 audit_dir='reports/full-coverage/lean-checkpoint-27'
 root_audit={p.relative_to(root).as_posix():sha(p) for p in (root/audit_dir).rglob('*') if p.is_file()}
 pub_audit={p.relative_to(pub).as_posix():sha(p) for p in (pub/audit_dir).rglob('*') if p.is_file()}
 assert root_audit and root_audit==pub_audit
 for n,h in root_audit.items():same(root,pub,n,h);required[n]=h
 browser=read(root,'reports/full-coverage/browser-checkpoint-27.json')
 assert browser['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence'
 assert browser['page_count']==29 and browser['requested_viewport_count']==browser['verified_viewport_count']==145
 assert browser['fresh_verified_viewport_count']==10 and browser['retained_verified_viewport_count']==135
 assert browser['screenshot_count']==48 and browser['skipped_capture_target_count']==10
 assert browser['source_sha256']==assets
 binput=read(root,'reports/full-coverage/browser-corrections-27-inputs.json')
 assert binput['actual_execution']=={'file':browser['actual_execution'],'sha256':browser['actual_execution_sha256']}
 fresh_name=browser['actual_execution'];assert sha(safe(root,fresh_name))==browser['actual_execution_sha256']
 fresh=actual(root,fresh_name,['node','qa/learning_review.mjs','--report','reports/full-coverage/browser-source55-27-v1.json','--artifacts','reports/full-coverage/browser-artifacts-source55-27-v1','lyapunov-mpc.html','verification.html'])
 assert fresh['source_sha256_before']==fresh['source_sha256_after']==assets
 assert fresh['qa_source_sha256']==browser['qa_source_sha256']
 assert all(sha(safe(root,n))==h for n,h in browser['qa_source_sha256'].items())
 assert sha(safe(root,fresh['report']))==fresh['report_sha256']
 same(root,pub,fresh_name,sha(safe(root,fresh_name)));required[fresh_name]=sha(safe(root,fresh_name))
 same(root,pub,fresh['report'],fresh['report_sha256']);required[fresh['report']]=fresh['report_sha256']
 assert len(binput['screenshot_aliases'])==48
 assert len({r['file'] for r in binput['screenshot_aliases']})==48
 for r in binput['screenshot_aliases']:
  n,h=r['file'],r['sha256'];assert n.startswith('reports/full-coverage/browser-artifacts-27/')
  same(root,pub,n,h);required[n]=h
  if r['evidence_mode']=='fresh_actual_source55_browser_execution':
   original=r['original'];assert original.startswith('reports/full-coverage/browser-artifacts-source55-27-v1/')
   same(root,pub,original,h);required[original]=h
 for n,h in RETIRED_COMPLETED26_FILES.items():tracked_exact(root,pub,n,h)
 for n,h in DUPLICATE_INVENTORIES.items():
  assert manifest['frozen_inputs_sha256'][n]==h
  same(root,pub,n,h);assert sha(safe(root,manifest['snapshot']+'/'+n))==h
 assert all(kept(n,exclusions) for n in required)
 assert kept('reports/full-coverage/lean-checkpoint-26/verification-original.json',exclusions)
 assert kept('reports/full-coverage/browser-artifacts-25/example.png',exclusions)
 assert kept('reports/full-coverage/browser-artifacts-26/example.png',exclusions)
 assert all(not kept(n,exclusions) for n in NEW_LITERAL_EXCLUSIONS)
 pre=included_tree_bytes(pub,exclusions)-len(old)+len(after)
 record={'status':'previous_exact_pages_configuration_preserved','original_publication_path':'_config.yml','original_sha256':BEFORE,'immutable_original_byte_copy':BACKUP}
 report={'status':'passed_exact_pages27_archival_configuration_preparation_requires_actual_pages_build','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(root,HELPER),'previous_configuration':{'file':BACKUP,'sha256':BEFORE},'config_sha256':hashlib.sha256(after).hexdigest(),'exclusions':sorted(exclusions),'excluded_count':124,'new_literal_exclusions':sorted(NEW_LITERAL_EXCLUSIONS),'retired_completed26_direct_manifest_selection_sha256':RETIRED_COMPLETED26_FILES,'retired_completed26_direct_archives_root_pub_tracked_HEAD_exact':True,'duplicate_source54_55_inventory_sha256':DUPLICATE_INVENTORIES,'duplicate_inventory_bytes_exact_in_root_publication_and_frozen27':True,'required_publication_files_sha256':required,'working_ledger_sha256':working,'published_frozen_ledger_sha256':published,'exact_original_metadata_removals':manifest['excluded_unreferenced_ledger_metadata'],'actual_prerequisite_executions':actual_refs,'selected_sources':1175,'theorem_exports':9644,'new_kernel_replays':8,'reused_identical_sources':1167,'current_book_asset_count':31,'screenshot_downloads':48,'prospective_included_website_bytes_before_new_native_records':pre,'website_budget_bytes':BUDGET,'coverage_complete':False,'scope':'Eight literal website archival exclusions only. Completed26 direct manifest/selection stay exact in Root, publication and tracked Git HEAD. All original source54/55 inventory bytes remain in Root, publication, frozen27 and the explicit content stage; only website inclusion changes. Current27 audit/manifest/selection/source55 assets, current inventory/corrections/frozen owner views, browser27 report and48 capture downloads remain included. Baseline26 Lean audit and older25/26 screenshot directories stay included. Actual Pages and live checks remain required.'}
 # Include the exact serialized report and both backups before any write.
 outputs={BACKUP:old,BACKUP_RECORD:encoded(record)}
 total=pre+sum(len(b) for n,b in outputs.items() if kept(n,exclusions))
 report['prospective_included_website_bytes_including_native_records']=0
 for _ in range(16):
  candidate=total+len(encoded(report))
  if report['prospective_included_website_bytes_including_native_records']==candidate:break
  report['prospective_included_website_bytes_including_native_records']=candidate
 else:raise AssertionError('serialized native byte-budget fixed point did not converge')
 assert report['prospective_included_website_bytes_including_native_records']<BUDGET
 outputs[REPORT]=encoded(report)
 return old,after,report,outputs

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--apply',action='store_true');args=parser.parse_args()
 assert args.apply,'Root-authorized explicit --apply is required'
 assert Path(__file__).resolve()==ROOT/HELPER,'execute only the reviewed canonical helper'
 old,after,report,outputs=prepare()
 assert sha(PUB/'_config.yml')==BEFORE
 for n,b in outputs.items():
  with safe(ROOT,n).open('xb') as f:f.write(b)
 assert sha(PUB/'_config.yml')==BEFORE
 (PUB/'_config.yml').write_bytes(after)
 assert sha(PUB/'_config.yml')==report['config_sha256']
 print(json.dumps({'status':'passed','native_report':ref(ROOT,REPORT),'literal_exclusions':124,'prospective_website_bytes':report['prospective_included_website_bytes_including_native_records'],'config_sha256':report['config_sha256']}))
if __name__=='__main__':main()

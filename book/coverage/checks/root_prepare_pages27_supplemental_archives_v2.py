"""Retain exact supplemental review originals in Git and limit website inclusion."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,runpy
ROOT=Path('/home/oxrexkevin/SafetyBased');PUB=ROOT/'reports/book/publication-repo'
SELF='book/coverage/checks/root_prepare_pages27_supplemental_archives_v2.py'
INPUTS='book/coverage/checks/future27-core/checkpoint27-supplemental-archive-inputs-v1.json'
REPORT='reports/full-coverage/pages27-supplemental-archive-configuration-v1.json'
BACKUP='reports/full-coverage/pages27-supplemental-archive-previous-original-v1.yml'
BEFORE='37afb173e76aee80569b4903ca88b39c5e12d4729a65627f447d2060842db1ea'
BUDGET=850000000
ADDED={'book/coverage/checks/future27-core/original-documentation27-foundations-review-v1','book/coverage/checks/future27-core/original-pages27-config5-actual-output-independent-modules-v2','reports/full-coverage/working-inventory55-timestamp-regeneration-before-restoration28-v1.json'}
GENERATED_METADATA_EXCLUSION='reports/full-coverage/publication27-prestage-v1.json'
HEADER='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def safe(root,n):
 assert type(n) is str and n and str(Path(n))==n and not Path(n).is_absolute() and '..' not in Path(n).parts
 assert not any(c in n for c in '\0\n\r*?[')
 p=root/n;assert p.resolve().is_relative_to(root.resolve()) and not p.is_symlink();return p

def read(n):return json.loads(safe(ROOT,n).read_bytes())
def kept(n,exclusions):return not any(n==e or n.startswith(e+'/') for e in exclusions)
def prepare():
 assert Path(__file__).resolve()==ROOT/SELF
 assert not safe(ROOT,REPORT).exists() and not safe(ROOT,BACKUP).exists()
 for n in (REPORT,BACKUP):assert not safe(PUB,n).exists()
 old=safe(PUB,'_config.yml').read_bytes();assert sha(PUB/'_config.yml')==BEFORE
 prior=read('reports/full-coverage/pages27-config-preparation-v1.json')
 assert prior['status']=='passed_exact_pages27_archival_configuration_preparation_requires_actual_pages_build' and prior['config_sha256']==BEFORE and prior['excluded_count']==129
 actual=read('reports/full-coverage/pages27-config-execution-v2.json')
 assert actual['status']=='passed' and type(actual['actual_exit_code']) is int and actual['actual_exit_code']==0
 assert actual['actual_command']==['python3','book/coverage/checks/root_prepare_pages27_config_v5.py','--apply'] and actual['actual_workdir']==str(ROOT)
 assert actual['helper_sha256_before']==actual['helper_sha256_after']=={prior['helper']['file']:prior['helper']['sha256']}
 assert sha(safe(ROOT,prior['helper']['file']))==prior['helper']['sha256']
 assert sha(safe(ROOT,actual['log']))==actual['log_sha256']
 inputs=read(INPUTS);assert inputs['unresolved_references']==[]
 expected=inputs['supplemental_inputs_sha256'];assert expected
 for n,h in expected.items():assert sha(safe(ROOT,n))==h,n
 excluded=set(prior['exclusions']);assert len(excluded)==129 and not excluded&ADDED
 assert old.decode()==HEADER+''.join('  - '+n+'\n' for n in sorted(excluded))
 assert GENERATED_METADATA_EXCLUSION not in excluded and GENERATED_METADATA_EXCLUSION not in ADDED
 excluded|=ADDED|{GENERATED_METADATA_EXCLUSION};assert len(excluded)==133
 after=(HEADER+''.join('  - '+n+'\n' for n in sorted(excluded))).encode()
 required=prior['required_publication_files_sha256'];assert len(required)==1284
 for n,h in required.items():assert kept(n,excluded) and sha(safe(PUB,n))==h,n
 manifest=read('reports/full-coverage/checkpoint-27-manifest.json')
 for n,h in manifest['frozen_inputs_sha256'].items():
  assert sha(safe(ROOT,manifest['snapshot']+'/'+n))==h,n
  if n not in {'book/coverage/progress.json','reports/full-coverage/README.md'}:assert sha(safe(PUB,n))==h,n
 for n,h in manifest['working_inputs_sha256'].items():
  if n.startswith('book/coverage/') and Path(n).name in {'core.json','foundations.json','applied.json','modules.json','applied-promotions.json','inventory.json','material-corrections.json'}:assert sha(safe(ROOT,n))==h,n
 retired={n:h for n,h in expected.items() if any(n==e or n.startswith(e+'/') for e in ADDED)}
 assert retired and all(any(n==e or n.startswith(e+'/') for n in retired) for e in ADDED)
 for n,h in retired.items():
  assert sha(safe(ROOT,n))==h
  if safe(PUB,n).exists():assert sha(safe(PUB,n))==h
 included=0
 for p in PUB.rglob('*'):
  n=p.relative_to(PUB).as_posix()
  if '.git' in p.relative_to(PUB).parts or not kept(n,excluded):continue
  if p.is_file():assert not p.is_symlink();included+=p.stat().st_size
 delta=sum(safe(ROOT,n).stat().st_size-(safe(PUB,n).stat().st_size if safe(PUB,n).is_file() else 0) for n in expected if kept(n,excluded))
 total=included+delta-len(old)+len(after)
 body={'status':'passed_exact_checkpoint27_supplemental_archive_configuration_requires_actual_stage_and_pages','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':SELF,'sha256':sha(ROOT/SELF)},'input_plan':{'file':INPUTS,'sha256':sha(ROOT/INPUTS)},'previous_configuration':{'file':BACKUP,'sha256':BEFORE},'previous_configuration_report':{'file':'reports/full-coverage/pages27-config-preparation-v1.json','sha256':sha(ROOT/'reports/full-coverage/pages27-config-preparation-v1.json')},'previous_actual_execution':{'file':'reports/full-coverage/pages27-config-execution-v2.json','sha256':sha(ROOT/'reports/full-coverage/pages27-config-execution-v2.json')},'config_sha256':hashlib.sha256(after).hexdigest(),'exclusions':sorted(excluded),'excluded_count':133,'new_literal_exclusions':sorted(ADDED|{GENERATED_METADATA_EXCLUSION}),'generated_whitelist_metadata_exclusion':GENERATED_METADATA_EXCLUSION,'retained_supplemental_originals_sha256':retired,'required_publication_files_sha256':required,'required_download_count':1284,'selected_sources':1175,'public_theorems':9644,'prospective_website_bytes_with_explicit_supplemental_copy':total,'website_budget_bytes':BUDGET,'coverage_complete':False,'scope':'Three exact supplemental review archive exclusions plus the generated Git whitelist record. All original bytes remain in the explicit Git stage inputs. Current selected27 and baseline26 audit downloads, source55 assets and all48 current screenshot downloads remain public. No Git HEAD retention is claimed for these new original files. Actual stage, Pages and live checks still required.'}
 payload=(json.dumps(body,indent=2)+'\n').encode();assert 0<=total+len(payload)+131072<BUDGET
 return after,payload,old

def main():
 p=argparse.ArgumentParser();p.add_argument('--apply',action='store_true');a=p.parse_args();after,payload,old=prepare()
 if a.apply:
  safe(ROOT,BACKUP).write_bytes(old);safe(ROOT,REPORT).write_bytes(payload)
  for n,b in ((BACKUP,old),(REPORT,payload)):
   q=safe(PUB,n);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
  safe(PUB,'_config.yml').write_bytes(after)
 print(json.dumps({'status':'passed','applied':a.apply,'excluded_count':133,'config_sha256':hashlib.sha256(after).hexdigest(),'prospective_website_bytes':json.loads(payload)['prospective_website_bytes_with_explicit_supplemental_copy']}))
if __name__=='__main__':main()

"""Install only four fully reviewed current55 owner candidates and one companion.

An exact final binding and explicit --apply are required. Before owner writes,
the unchanged proof sources, native canonical pairs and independent mapping
peers are checked, and the combined candidate inventory is validated in isolation.
"""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,importlib.util,json,os,sys,tempfile
ROOT=Path(__file__).resolve().parents[3]
INV_SHA='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
SELECTION='reports/full-coverage/checkpoint-26-selection.json'
SELECTION_SHA='12527ed93a283e1b37a491f7f799ac04e6217b1d7e20aee74116b312e580e23f'
PAIRS='book/coverage/checks/future27-core/eight-source141-canonical-v1/eight-source141-actual-canonical-paired-readiness27-v1.json'
PAIRS_SHA='74f6e5413cb390698e6090b798d6f0eed0b667082bd24681f7b2e82c49deef1f'
ACTUAL='reports/full-coverage/eight-source141-canonical-pairs27-execution-v1.json'
ACTUAL_SHA='9ee7428bc5d16d6b65ec0fd88877d85e3ba38cb879f11951eca72ddd0b6df384'
OWNERS={k:'book/coverage/'+k+'.json' for k in ['core','foundations','applied','modules']}
ARCHIVE='reports/full-coverage/owner26-originals-before-owner27-integration-v1'
RESULT='reports/full-coverage/owner27-reviewed-candidate-integration-v1.json'
def safe(n):
 p=Path(n);assert isinstance(n,str) and n and not p.is_absolute() and '..' not in p.parts and p.as_posix()==n
 p=ROOT/p;assert p.resolve().is_relative_to(ROOT);return p
def sha(n):return hashlib.sha256(safe(n).read_bytes()).hexdigest()
def read(n):return json.loads(safe(n).read_bytes())
def checked(r):
 assert set(r)=={'file','sha256'} and sha(r['file'])==r['sha256'];return read(r['file'])
def pointer(d,keys):
 assert isinstance(keys,list) and keys
 for key in keys:d=d[key]
 return d
def zero(d):
 codes=[d[k] for k in ['actual_exit_code','exit_code'] if k in d]
 assert codes and all(type(c) is int and c==0 for c in codes)
parser=argparse.ArgumentParser();parser.add_argument('binding');parser.add_argument('--apply',action='store_true');args=parser.parse_args()
binding=read(args.binding)
assert binding['status']=='all_four_reviewed_current55_owner_candidates_bound_ready_for_root_execution'
assert binding['helper']=={'file':Path(__file__).relative_to(ROOT).as_posix(),'sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
helper_peer=checked(binding['independent_helper_review'])
assert 'passed' in helper_peer['status'] and helper_peer.get('errors',[])==[] and helper_peer['helper']==binding['helper']
assert sha('book/coverage/inventory.json')==sha('book/coverage/inventory-after-correction55.json')==binding['inventory_sha256']==INV_SHA
assert binding['baseline26_selection']=={'file':SELECTION,'sha256':SELECTION_SHA}
selection=checked(binding['baseline26_selection']);assert len(selection['proof_files'])==1167
assert binding['actual_canonical_readiness']=={'file':PAIRS,'sha256':PAIRS_SHA}
assert binding['actual_canonical_pair_execution']=={'file':ACTUAL,'sha256':ACTUAL_SHA}
pairs=checked(binding['actual_canonical_readiness']);actual=checked(binding['actual_canonical_pair_execution']);zero(actual)
assert pairs['errors']==[] and pairs['source_count']==8 and pairs['public_theorem_count']==141
assert pairs['actual_compiler_command_count']==len(pairs['actual_paired_records'])==16
assert actual['actual_command']==['python3','book/coverage/checks/run_root27_eight_source141_canonical_pairs_v2.py','--apply']
assert actual['actual_workdir']==str(ROOT) and actual['helper_sha256_before']==actual['helper_sha256_after']
assert sha(actual['log'])==actual['log_sha256']
for n,h in actual['helper_sha256_after'].items():assert sha(n)==h
protected={n:r['sha256'] for n,r in selection['proof_files'].items()}
new_sources={r['canonical_source']:r['source']['sha256'] for r in pairs['sources']}
assert len(new_sources)==8 and not set(new_sources).intersection(protected)
protected.update(new_sources)
assets=binding['exact_current55_safelearning_assets_sha256'];assert len(assets)==31
assert read('book/coverage/inventory.json')['source_sha256']=={n:h for n,h in assets.items() if n.endswith('.html')}
protected.update(assets);protected['book/coverage/inventory.json']=INV_SHA
protected['book/coverage/inventory-after-correction55.json']=INV_SHA
for name in [SELECTION,PAIRS,ACTUAL,'book/coverage/material-corrections.json','book/coverage/validate.py']:
 protected[name]=sha(name)
assert len(read('book/coverage/material-corrections.json')['corrections'])==55
def guard():
 for n,h in protected.items():assert sha(n)==h,n
guard()
assert set(binding['owners'])==set(OWNERS)
replacements=[];offered=set()
for owner,dest in OWNERS.items():
 row=binding['owners'][owner];assert row['destination']==dest and sha(dest)==row['installed26_sha256']
 candidate=checked(row['candidate']);offer=checked(row['reviewed_offer']);peer=checked(row['final_mapping_peer'])
 assert 'passed' in peer['status'] and peer.get('errors',[])==[]
 assert pointer(peer,row['peer_candidate_pointer'])==row['candidate']
 assert pointer(offer,row['offer_candidate_pointer'])==row['candidate']['file']
 assert pointer(offer,row['offer_candidate_sha256_pointer'])==row['candidate']['sha256']
 assert offer.get('inventory_sha256',offer.get('current_inventory_sha256'))==INV_SHA
 finalizer=checked(row['actual_finalizer']);zero(finalizer)
 assert finalizer['helper_sha256_before']==finalizer['helper_sha256_after'] and finalizer['actual_workdir']==str(ROOT)
 assert sha(finalizer['log'])==finalizer['log_sha256']
 for n,h in finalizer['helper_sha256_after'].items():assert sha(n)==h
 old=read(dest);assert candidate['scope_pages']==old['scope_pages']
 for n,h in candidate['source_sha256'].items():
  assert sha(n)==h
  if n.startswith('SafeLearning/'):assert assets[n]==h
  else:assert old['source_sha256'][n]==h
 proofs=offer['proof_files'];assert set(proofs)==set(row['new_sources'])
 for n,r in proofs.items():
  assert n in new_sources and r['sha256']==new_sources[n] and n not in offered;offered.add(n)
  original_pairs=[p for p in pairs['actual_paired_records'] if p['source']['file']==n]
  assert len(original_pairs)==2
  for p in original_pairs:
   native=checked(p['actual_record']);zero(native)
   assert native['source']==n and native['source_sha256_before']==native['source_sha256_after']==r['sha256']
   stem=Path(n).stem
   expected=['lake','env','lean','SafeLearning/'+stem+'.lean'] if p['kind']=='standalone' else ['lake','build','SafeLearning.'+stem]
   assert p['kind'] in {'standalone','named'} and native['command']==expected and native['actual_workdir']==str(ROOT/'verification/lean')
   assert p['source_snapshot']['sha256']==r['sha256'] and sha(p['source_snapshot']['file'])==r['sha256']
   assert p['raw_log']=={'file':native['log'],'sha256':native['log_sha256']} and sha(p['raw_log']['file'])==p['raw_log']['sha256']
 replacements.append({'destination':dest,'before_sha256':row['installed26_sha256'],'candidate':row['candidate']})
 companions=row.get('companion_candidates',[]);assert len(companions)==(1 if owner=='applied' else 0)
 for c in companions:
  assert c['destination']=='book/coverage/applied-promotions.json' and sha(c['destination'])==c['installed26_sha256'];checked(c['candidate'])
  replacements.append({'destination':c['destination'],'before_sha256':c['installed26_sha256'],'candidate':c['candidate']})
assert offered==set(new_sources) and len(replacements)==5
assert not safe(RESULT).exists() and not safe(ARCHIVE).exists()
guard()
# Run the existing comprehensive validator against exact candidate byte aliases.
# Its generated report is an isolated preflight, never installed-owner approval.
with tempfile.TemporaryDirectory(prefix='root-owner27-preflight-') as tmp:
 ctx=Path(tmp);(ctx/'book/coverage').mkdir(parents=True);(ctx/'verification').mkdir()
 (ctx/'SafeLearning').symlink_to(ROOT/'SafeLearning',target_is_directory=True)
 (ctx/'verification/lean').symlink_to(ROOT/'verification/lean',target_is_directory=True)
 (ctx/'book/coverage/inventory.json').symlink_to(ROOT/'book/coverage/inventory.json')
 for row in replacements:(ctx/row['destination']).symlink_to(safe(row['candidate']['file']))
 sys.path.insert(0,str(ROOT/'book/coverage'))
 spec=importlib.util.spec_from_file_location('candidate27_integrity',ROOT/'book/coverage/validate.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);module.ROOT=ctx
 report=module.validate()
 assert report['integrity_status']=='passed' and report['errors']==[]
 assert report['counts']['exercises']==556 and report['counts']['material_source_units']==12774
 assert report['mathematical_coverage_complete'] is False
guard()
if not args.apply:
 print(json.dumps({'status':'passed_isolated_preflight_only','counts':report['counts'],'candidate_count':5,'new_sources':8,'owner_writes':0}));raise SystemExit(0)
safe(ARCHIVE).mkdir(parents=True)
for row in replacements:
 archive=ARCHIVE+'/'+Path(row['destination']).name
 with safe(archive).open('xb') as stream:stream.write(safe(row['destination']).read_bytes())
 assert sha(archive)==row['before_sha256'];row['original26_byte_copy']=archive
for row in replacements:
 assert sha(row['destination'])==row['before_sha256']
 with safe(row['destination']).open('wb') as stream:stream.write(safe(row['candidate']['file']).read_bytes())
 assert sha(row['destination'])==row['candidate']['sha256']
guard()
result={'status':'four_exact_reviewed_owner27_candidate_bytes_integrated_pending_fresh_current55_global_integrity_and_aggregate27_audit','applied':True,'installed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_helper':binding['helper'],'binding_manifest':args.binding,'binding_manifest_sha256':sha(args.binding),'inventory_sha256':INV_SHA,'exact_replacements':replacements,'protected_proof_source_count':1175,'new_canonical_source_count':8,'exact_current55_asset_count':31,'isolated_candidate_preflight_counts':report['counts'],'coverage_complete':False,'selection_or_aggregate_or_publication_claimed':False}
with safe(RESULT).open('x') as stream:stream.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'owners':5,'new_sources':8,'result':RESULT,'sha256':sha(RESULT),'isolated_counts':report['counts']}))

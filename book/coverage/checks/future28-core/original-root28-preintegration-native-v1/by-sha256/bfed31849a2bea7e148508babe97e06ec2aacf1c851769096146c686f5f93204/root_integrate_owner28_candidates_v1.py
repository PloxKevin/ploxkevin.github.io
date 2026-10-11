"""Install five exact current60 candidates after independent review and preflight."""
from pathlib import Path
from datetime import datetime, timezone
import argparse,hashlib,importlib.util,json,re,sys,tempfile

ROOT=Path(__file__).resolve().parents[3]
INVENTORY_SHA='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
SELECTION='reports/full-coverage/checkpoint-27-selection.json'
SELECTION_SHA='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
OLD={
 'core':'0bf99e01c47c7b9fa18488fdc3104c189e3977597c15f1c7e20253afad1245c0',
 'foundations':'b3de5e813f882355cd90e46d27adc4ce56351ddd51d9038a1b8c79511b365b55',
 'applied':'31b6af21c8ba9d214380ba5c116046bf7587eba3d736e1a536266c5fbfe61e68',
 'modules':'7baccb56f8563b52c18d3e90c2df46ca946271d886332ec9e97a4cf805af9487',
 'applied-promotions':'72ee23132c02823bc13fa513d2892e79d748b6617b0d3fe52b3de7e29735a5a2'}
EXPECTED_NEW={'core':0,'foundations':6,'applied':0,'modules':5}
ARCHIVE='reports/full-coverage/owner27-originals-before-owner28-integration-v1'
RESULT='reports/full-coverage/owner28-reviewed-candidate-integration-v1.json'

def safe(n):
 assert type(n) is str and n
 p=Path(n);assert not p.is_absolute() and '..' not in p.parts and p.as_posix()==n
 p=ROOT/p;assert p.resolve().is_relative_to(ROOT) and not p.is_symlink();return p
def sha(n):return hashlib.sha256(safe(n).read_bytes()).hexdigest()
def read(n):return json.loads(safe(n).read_bytes())
def checked(r):
 assert set(r)=={'file','sha256'} and re.fullmatch('[0-9a-f]{64}',r['sha256'])
 assert sha(r['file'])==r['sha256'];return read(r['file'])
def pointer(data,keys):
 assert type(keys) is list and keys
 for key in keys:data=data[key]
 return data
def zero(d):
 codes=[d[k] for k in ('actual_exit_code','exit_code','actual_runner_exit_code') if k in d]
 assert codes and all(type(c) is int and c==0 for c in codes)
def exact(mapping):
 for n,h in mapping.items():assert sha(n)==h,n
def native_actual(r,command,helpers,log_fields):
 d=checked(r);zero(d)
 assert d['actual_command']==command and d['actual_workdir']==str(ROOT)
 assert d['helper_sha256_before']==d['helper_sha256_after']==helpers
 exact(helpers)
 assert len(log_fields)==2 and sha(d[log_fields[0]])==d[log_fields[1]]
 return d
def new(n,data):
 p=safe(n);assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb') as f:f.write(data)

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--binding',required=True);parser.add_argument('--binding-sha256',required=True);parser.add_argument('--apply',action='store_true');args=parser.parse_args()
 binding=checked({'file':args.binding,'sha256':args.binding_sha256})
 assert binding['status']=='all_four_reviewed_current60_owner28_candidates_bound_ready_for_root_execution'
 helper={'file':Path(__file__).relative_to(ROOT).as_posix(),'sha256':sha(Path(__file__).relative_to(ROOT).as_posix())}
 assert binding['helper']==helper
 code_peer=checked(binding['independent_helper_review'])
 assert code_peer['status']==binding['expected_independent_helper_review_status'] and code_peer['errors']==[] and code_peer['helper']==helper
 assert sha('book/coverage/inventory.json')==sha('book/coverage/inventory-after-correction60.json')==INVENTORY_SHA
 assert binding['inventory']=={'file':'book/coverage/inventory-after-correction60.json','sha256':INVENTORY_SHA}
 assert binding['baseline27_selection']=={'file':SELECTION,'sha256':SELECTION_SHA}
 baseline=checked(binding['baseline27_selection']);assert len(baseline['proof_files'])==1175
 protected={n:r['sha256'] for n,r in baseline['proof_files'].items()}
 assets=binding['exact_current60_safelearning_assets_sha256'];assert len(assets)==31
 assert read('book/coverage/inventory.json')['source_sha256']=={n:h for n,h in assets.items() if n.endswith('.html')}
 protected.update(assets)
 for n in ['book/coverage/inventory.json','book/coverage/inventory-after-correction60.json','book/coverage/material-corrections.json',SELECTION,'book/coverage/validate.py',args.binding]:protected[n]=sha(n)
 assert len(read('book/coverage/material-corrections.json')['corrections'])==60
 immutable={binding['independent_helper_review']['file']:binding['independent_helper_review']['sha256']}
 for r in binding['additional_immutable_inputs']:
  assert set(r)=={'file','sha256'} and sha(r['file'])==r['sha256']
  assert r['file'] not in immutable or immutable[r['file']]==r['sha256']
  immutable[r['file']]=r['sha256']
 batches=binding['canonical_pair_batches'];assert len(batches)==2
 sources={};all_pairs=[]
 for batch in batches:
  pairs=checked(batch['readiness']);actual=native_actual(batch['actual_execution'],batch['expected_command'],batch['expected_helper_sha256'],['log','log_sha256'])
  assert pairs['status']==batch['expected_readiness_status'] and pairs['errors']==[]
  assert pairs['source_count']==batch['source_count'] and pairs['public_theorem_count']==batch['public_theorem_count']
  assert pairs['actual_compiler_command_count']==len(pairs['actual_paired_records'])==2*batch['source_count']
  for r in [batch['readiness'],batch['actual_execution']]:immutable[r['file']]=r['sha256']
  immutable[actual['log']]=actual['log_sha256'];immutable.update(actual['helper_sha256_after'])
  for row in pairs['sources']:
   n=row['canonical_source'];h=row['original_tmp_source']['sha256'];assert n not in sources and n not in protected
   sources[n]=h;protected[n]=h
  for row in pairs['actual_paired_records']:
   n=row['source']['file'];h=row['source']['sha256'];assert sources[n]==h
   assert type(row['actual_exit_code']) is int and row['actual_exit_code']==0
   native=checked(row['actual_record']);zero(native);stem=Path(n).stem
   assert row['kind'] in {'standalone','named'}
   command=['lake','env','lean','SafeLearning/'+stem+'.lean'] if row['kind']=='standalone' else ['lake','build','SafeLearning.'+stem]
   assert native['command']==command and native['actual_workdir']==str(ROOT/'verification/lean')
   assert native['source']==n and native['source_sha256_before']==native['source_sha256_after']==h
   assert row['raw_log']=={'file':native['log'],'sha256':native['log_sha256']}
   assert row['source_snapshot']['sha256']==h
   for key in ('actual_record','raw_log','source_snapshot'):
    ref=row[key];assert sha(ref['file'])==ref['sha256'];immutable[ref['file']]=ref['sha256']
   all_pairs.append(row)
 assert len(sources)==11 and len(all_pairs)==22 and sum(b['public_theorem_count'] for b in batches)==252
 assert set(binding['owners'])==set(EXPECTED_NEW)
 replacements=[];offered=set()
 for owner,new_count in EXPECTED_NEW.items():
  row=binding['owners'][owner];dest='book/coverage/'+owner+'.json'
  assert row['destination']==dest and row['installed27_sha256']==OLD[owner] and sha(dest)==OLD[owner]
  candidate=checked(row['candidate']);offer=checked(row['reviewed_offer']);peer=checked(row['final_mapping_peer'])
  assert peer['status']==row['expected_final_mapping_peer_status'] and peer['errors']==[]
  assert pointer(peer,row['peer_candidate_pointer'])==row['candidate']
  assert pointer(offer,row['offer_candidate_pointer'])==row['candidate']
  assert offer['inventory_sha256']==INVENTORY_SHA
  assert pointer(peer,row['peer_actual_finalizer_pointer'])==row['actual_finalizer']
  native_actual(row['actual_finalizer'],row['expected_actual_finalizer_command'],row['expected_actual_finalizer_helpers_sha256'],row['actual_finalizer_log_fields'])
  for r in [row['candidate'],row['reviewed_offer'],row['final_mapping_peer'],row['actual_finalizer']]:immutable[r['file']]=r['sha256']
  old=read(dest);assert candidate['scope_pages']==old['scope_pages']
  for n,h in candidate['source_sha256'].items():
   assert sha(n)==h
   if n.startswith('SafeLearning/'):assert assets[n]==h
   else:assert old['source_sha256'][n]==h
  proofs=offer['proof_files'];assert len(proofs)==new_count and set(proofs)==set(row['new_sources'])
  old_proofs=old['proof_files'];new_proofs=candidate['proof_files']
  assert type(new_proofs) is type(old_proofs) and set(new_proofs)==set(old_proofs)|set(proofs)
  if isinstance(old_proofs,dict):assert all(new_proofs[n]==r for n,r in old_proofs.items())
  else:assert new_proofs[:len(old_proofs)]==old_proofs
  for n,proof in proofs.items():
   assert n in sources and n not in offered and proof['sha256']==sources[n];offered.add(n)
   assert proof['theorem_count']==len(proof['public_theorem_names'])==len(set(proof['public_theorem_names']))
   assert proof['mapped_named_declarations']==proof['public_theorem_names']
   exact(proof['evidence_sha256']);immutable.update(proof['evidence_sha256'])
   pair=[p for p in all_pairs if p['source']['file']==n]
   assert len(pair)==2 and {p['kind'] for p in pair}=={'standalone','named'} and proof['actual_pair']==pair
   for p in pair:
    for key in ('actual_record','raw_log','source_snapshot'):assert proof['evidence_sha256'][p[key]['file']]==p[key]['sha256']
  replacements.append({'destination':dest,'before_sha256':OLD[owner],'candidate':row['candidate']})
  companions=row.get('companion_candidates',[]);assert len(companions)==(1 if owner=='applied' else 0)
  for c in companions:
   assert c['destination']=='book/coverage/applied-promotions.json' and sha(c['destination'])==OLD['applied-promotions'];checked(c['candidate'])
   assert pointer(offer,c['offer_candidate_pointer'])==pointer(peer,c['peer_candidate_pointer'])==c['candidate']
   immutable[c['candidate']['file']]=c['candidate']['sha256']
   replacements.append({'destination':c['destination'],'before_sha256':OLD['applied-promotions'],'candidate':c['candidate']})
 assert offered==set(sources) and len(replacements)==5
 assert not safe(RESULT).exists() and not safe(ARCHIVE).exists()
 # Old live owner bytes are archived explicitly before replacement. Current
 # evidence must use immutable aliases rather than those five mutable paths.
 assert not set(immutable).intersection(r['destination'] for r in replacements)
 def guard():exact(protected);exact(immutable);assert sha(helper['file'])==helper['sha256']
 guard()
 with tempfile.TemporaryDirectory(prefix='root-owner28-preflight-') as tmp:
  ctx=Path(tmp);(ctx/'book/coverage').mkdir(parents=True);(ctx/'verification').mkdir()
  (ctx/'SafeLearning').symlink_to(ROOT/'SafeLearning',target_is_directory=True)
  (ctx/'verification/lean').symlink_to(ROOT/'verification/lean',target_is_directory=True)
  (ctx/'book/coverage/inventory.json').symlink_to(ROOT/'book/coverage/inventory.json')
  for r in replacements:(ctx/r['destination']).symlink_to(safe(r['candidate']['file']))
  sys.path.insert(0,str(ROOT/'book/coverage'))
  spec=importlib.util.spec_from_file_location('candidate28_integrity',ROOT/'book/coverage/validate.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);module.ROOT=ctx
  report=module.validate()
  assert report['integrity_status']=='passed' and report['errors']==[] and report['mathematical_coverage_complete'] is False
  assert report['counts']['exercises']==556 and report['counts']['material_source_units']==12774
  assert {k:report['counts']['statuses'][k] for k in ('exercise:complete_math','exercise:partial','exercise:pending')}=={'exercise:complete_math':523,'exercise:partial':14,'exercise:pending':19}
  assert report['counts']['material_review_statuses']=={'reviewed':4621,'pending':8153}
 guard()
 if not args.apply:
  print(json.dumps({'status':'passed_isolated_current60_owner28_preflight_no_owner_writes','counts':report['counts'],'candidate_count':5,'new_sources':11}));return
 for r in replacements:
  assert sha(r['destination'])==r['before_sha256']
  archive=ARCHIVE+'/'+Path(r['destination']).name;new(archive,safe(r['destination']).read_bytes());assert sha(archive)==r['before_sha256'];r['original27_byte_copy']=archive
 guard()
 for r in replacements:
  assert sha(r['destination'])==r['before_sha256']
  with safe(r['destination']).open('wb') as f:f.write(safe(r['candidate']['file']).read_bytes())
  assert sha(r['destination'])==r['candidate']['sha256']
 guard()
 result={'status':'four_exact_reviewed_owner28_candidate_bytes_integrated_pending_fresh_current60_global_integrity_and_aggregate28_audit',
  'applied':True,'installed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_helper':helper,
  'binding_manifest':args.binding,'binding_manifest_sha256':args.binding_sha256,'inventory_sha256':INVENTORY_SHA,
  'exact_replacements':replacements,'protected_proof_source_count':1186,'new_canonical_source_count':11,
  'exact_current60_asset_count':31,'isolated_candidate_preflight_counts':report['counts'],
  'coverage_complete':False,'selection_or_aggregate_or_publication_claimed':False}
 new(RESULT,(json.dumps(result,indent=2)+'\n').encode())
 print(json.dumps({'status':result['status'],'owners':5,'new_sources':11,'result':RESULT,'sha256':sha(RESULT),'counts':report['counts']}))

if __name__=='__main__':main()

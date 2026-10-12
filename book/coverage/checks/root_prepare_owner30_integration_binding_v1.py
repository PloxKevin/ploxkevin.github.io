"""Prepare an exact owner30 integration binding from real closed supplied peers.

This helper only reads existing files and writes one fresh binding under checks.
It never imports or invokes the integration producer, validator, or compiler.
Default/apply integration and their genuine native receipts remain Root work.
"""
from pathlib import Path
import argparse, hashlib, json, re

ROOT = Path(__file__).resolve().parents[3]
SELF = 'book/coverage/checks/root_prepare_owner30_integration_binding_v1.py'
HELPER = 'book/coverage/checks/root_integrate_owner30_candidates_v2.py'
HELPER_SHA = '38eaf901e509305976c78e7ec6bb019a05e91222a26e351f29d4f5ed4abcbfd8'
INVENTORY = 'book/coverage/inventory-after-correction79.json'
INVENTORY_SHA = '9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de'
SELECTION = 'reports/full-coverage/checkpoint-29-selection.json'
SELECTION_SHA = 'ad4eb2940daa6f89dfb52390abc26c8bedb00dae7f97534957f5a4e87ac0d8a9'
READINESS = 'book/coverage/checks/future30-core/current79-canonical-pairs45-v1/actual-reviewed30-canonical-paired-readiness-v1.json'
READINESS_SHA = '4ce14955fe77d0cc9447ff9963e79631ce8dbff3110683d261eb3c89eaa2cf7e'
PRIMARY = 'reports/full-coverage/current79-canonical-pairs45-application30-execution-v1.json'
PRIMARY_SHA = '8e3e384891e52794a493d078350abe282c8d215ff7f883eae6a3861c4eda77ee'
OLD = {
 'core': 'a3db11195cef10593b1e5fc21cf6b6b5a037f106dde09d247efc96277dd249b6',
 'foundations': '67889e85ad190d150ec888b803cfcc4d2c80dc48aa096d1969ddfbf90cda5f07',
 'applied': '75c51c798ec0edf7fada80387e078d5fc6d383bcc76edb203fd9f30df4c52d1d',
 'modules': '13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d',
 'applied-promotions': '03d4343c000b1954a6cb6e0a2e3061ad2b5a585db906a67bcec8122421874b53',
}
SUPPLIED = {
 'independent_helper_review', 'expected_independent_helper_review_status',
 'helper_review_actual_native', 'helper_review_native_specification',
 'helper_review_original_TMP_aliases', 'helper_review_native_pointer',
 'owners', 'additional_immutable_inputs',
}


def safe(n, exists=True):
 assert type(n) is str and n and '\0' not in n and '\n' not in n and '\r' not in n
 p=Path(n); assert not p.is_absolute() and p.as_posix()==n and '..' not in p.parts
 p=ROOT/p; assert p.resolve().is_relative_to(ROOT.resolve())
 for q in [p,*p.parents]:
  if q.is_relative_to(ROOT):
   assert not q.is_symlink()
   if q!=p and q.exists(): assert q.is_dir()
 if exists: assert p.is_file()
 return p


def sha(n): return hashlib.sha256(safe(n).read_bytes()).hexdigest()
def read(n): return json.loads(safe(n).read_bytes())
def ref(n): return {'file':n,'sha256':sha(n)}


def checked(r, pins, parse=True):
 assert type(r) is dict and {'file','sha256'}<=set(r)<={'file','sha256','bytes'}
 assert re.fullmatch('[0-9a-f]{64}',r['sha256']) and sha(r['file'])==r['sha256']
 if 'bytes' in r: assert type(r['bytes']) is int and safe(r['file']).stat().st_size==r['bytes']
 assert r['file'] not in pins or pins[r['file']]==r['sha256']; pins[r['file']]=r['sha256']
 return read(r['file']) if parse else safe(r['file'])


def pointer(d,ks):
 assert type(ks) is list and ks
 for k in ks:
  assert type(k) in (str,int); d=d[k]
 return d


def native(r,spec,aliases,pins):
 d=checked(r,pins)
 codes=[d[k] for k in ['actual_exit_code','exit_code','actual_runner_exit_code'] if k in d]
 assert codes and all(type(c) is int and c==0 for c in codes) and d.get('protection_errors',[])==[]
 assert d['status']==spec['status']
 commands=[d[k] for k in ['actual_command','command'] if k in d]
 locs=[d[k] for k in ['actual_workdir','working_directory','workdir','cwd'] if k in d]
 assert commands and all(c==spec['command'] for c in commands)
 assert locs and all(c==spec['workdir'] for c in locs)
 assert d['helper_sha256_before']==d['helper_sha256_after']==spec['helpers_sha256']
 lf=spec['log_fields']; assert type(lf) is list and len(lf)==2
 originals={**spec['helpers_sha256'],d[lf[0]]:d[lf[1]]}
 assert set(aliases)=={n for n in originals if Path(n).is_absolute()}
 for n,h in originals.items():
  if Path(n).is_absolute():
   p=Path(n); assert p.is_relative_to('/tmp') and '..' not in p.parts and p.as_posix()==n
   assert aliases[n]['sha256']==h; checked(aliases[n],pins,False)
  else: assert sha(n)==h; pins[n]=h


def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--supplies',required=True); ap.add_argument('--supplies-sha256',required=True)
 ap.add_argument('--output',required=True); args=ap.parse_args()
 assert Path(__file__).resolve()==ROOT/SELF
 assert args.output.startswith('book/coverage/checks/') and args.output.endswith('.json')
 out=safe(args.output,False); assert not out.exists()
 pins={SELF:sha(SELF),HELPER:HELPER_SHA,INVENTORY:INVENTORY_SHA,SELECTION:SELECTION_SHA,
       READINESS:READINESS_SHA,PRIMARY:PRIMARY_SHA}
 supply_ref={'file':args.supplies,'sha256':args.supplies_sha256}
 supplies=checked(supply_ref,pins)
 assert supplies['status']=='exact_closed_owner30_peer_and_candidate_supplies_for_binding_preparation_only'
 assert SUPPLIED<=set(supplies)<=SUPPLIED|{'status','expected_isolated_preflight_counts'}
 inv=checked({'file':INVENTORY,'sha256':INVENTORY_SHA},pins)
 assert sha('book/coverage/inventory.json')==INVENTORY_SHA; pins['book/coverage/inventory.json']=INVENTORY_SHA
 assert inv['counts']['exercises']==556 and inv['counts']['material_source_units']==12774
 sel=checked({'file':SELECTION,'sha256':SELECTION_SHA},pins)
 assert len(sel['proof_files'])==1197
 for n,r in sel['proof_files'].items(): checked({'file':n,'sha256':r['sha256']},pins,False)
 ready=checked({'file':READINESS,'sha256':READINESS_SHA},pins)
 assert ready['status']=='passed_actual_reviewed30_canonical_standalone_and_named_pairs_unselected' and ready['errors']==[]
 assert ready['source_count']==len(ready['sources'])==45 and ready['actual_compiler_command_count']==len(ready['actual_paired_records'])==90
 assert ready['public_theorem_count']==966
 for r in ready['sources']: checked({'file':r['canonical_source'],'sha256':r['original_tmp_source']['sha256']},pins,False)
 actual=checked({'file':PRIMARY,'sha256':PRIMARY_SHA},pins)
 assert actual['status']=='passed' and type(actual['actual_exit_code']) is int and actual['actual_exit_code']==0
 assets=dict(inv['source_sha256'])
 assert len(assets)==29 and all(n.startswith('SafeLearning/') and n.endswith('.html') for n in assets)
 for n in ['SafeLearning/style.css','SafeLearning/components.js']: assets[n]=sha(n)
 for n,h in assets.items(): assert sha(n)==h; pins[n]=h
 for o,h in OLD.items():
  n='book/coverage/'+o+'.json'; assert sha(n)==h; pins[n]=h
 helper={'file':HELPER,'sha256':HELPER_SHA}
 peer=checked(supplies['independent_helper_review'],pins)
 assert peer['status']==supplies['expected_independent_helper_review_status'] and peer['errors']==[]
 assert peer['helper']==helper and peer['full_code_read'] is True
 native(supplies['helper_review_actual_native'],supplies['helper_review_native_specification'],supplies['helper_review_original_TMP_aliases'],pins)
 assert pointer(peer,supplies['helper_review_native_pointer'])==supplies['helper_review_actual_native']
 assert set(supplies['owners'])=={'core','foundations','applied','modules'}
 for owner,s in supplies['owners'].items():
  assert s['destination']=='book/coverage/'+owner+'.json' and s['installed29_sha256']==OLD[owner]
  checked(s['candidate'],pins); offer=checked(s['reviewed_offer'],pins); peer=checked(s['final_mapping_peer'],pins)
  assert peer['status']==s['expected_final_mapping_peer_status'] and peer['errors']==[]
  assert pointer(peer,s['peer_candidate_pointer'])==pointer(offer,s['offer_candidate_pointer'])==s['candidate']
  assert s['peer_approved_mapping_pointers'] and all(pointer(peer,p) is True for p in s['peer_approved_mapping_pointers'])
  assert pointer(peer,s['peer_actual_native_pointer'])==s['actual_mapping_native']
  native(s['actual_mapping_native'],s['mapping_native_specification'],s['mapping_original_TMP_aliases'],pins)
  for r in s['additional_exact_original_evidence']: checked(r,pins,False)
  for c in s['companion_candidates']:
   assert c['destination']=='book/coverage/applied-promotions.json' and owner=='applied'
   checked(c['candidate'],pins)
   assert pointer(offer,c['offer_candidate_pointer'])==pointer(peer,c['peer_candidate_pointer'])==c['candidate']
 for r in supplies['additional_immutable_inputs']: checked(r,pins,False)
 assert args.output not in pins
 binding={k:supplies[k] for k in SUPPLIED}
 binding.update({'status':'four_final_Source79_owner30_domains_and_applied_promotions_actual90_and_mapping_peers_bound_for_Root',
  'helper':helper,'inventory':{'file':INVENTORY,'sha256':INVENTORY_SHA},
  'baseline29_selection':{'file':SELECTION,'sha256':SELECTION_SHA},
  'canonical_readiness':{'file':READINESS,'sha256':READINESS_SHA},
  'canonical_actual_execution':{'file':PRIMARY,'sha256':PRIMARY_SHA},
  'exact_current79_safelearning_assets_sha256':assets,
  'expected_isolated_preflight_counts':supplies.get('expected_isolated_preflight_counts')})
 binding['additional_immutable_inputs']=list(binding['additional_immutable_inputs'])+[supply_ref,ref(SELF)]
 for n,h in pins.items(): assert sha(n)==h,n
 out.parent.mkdir(parents=True,exist_ok=True)
 with out.open('xb') as f: f.write((json.dumps(binding,indent=2,ensure_ascii=False)+'\n').encode())
 for n,h in pins.items(): assert sha(n)==h,n
 print(json.dumps({'status':'exact_closed_owner30_binding_prepared_no_integration_execution',
  'binding':ref(args.output),'source_count':1242,'live_owner_writes':False,
  'integration_preflight_or_application_success_claimed':False}))


if __name__=='__main__': main()

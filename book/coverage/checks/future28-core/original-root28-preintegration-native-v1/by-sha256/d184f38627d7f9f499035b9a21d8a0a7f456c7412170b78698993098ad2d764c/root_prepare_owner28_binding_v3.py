"""Bind exact reviewed owner candidates and native executions without installing."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, importlib.util
ROOT=Path(__file__).resolve().parents[3]
DEST='book/coverage/checks/future28-core/current60-owner28-binding-v1.json'
def safe(n):
 p=Path(n);assert type(n) is str and not p.is_absolute() and '..' not in p.parts and p.as_posix()==n
 p=ROOT/p;assert p.resolve().is_relative_to(ROOT) and not p.is_symlink();return p
def sha(n):return hashlib.sha256(safe(n).read_bytes()).hexdigest()
def read(n):return json.loads(safe(n).read_bytes())
def ref(n):return {'file':n,'sha256':sha(n)}
def checked(r):assert set(r)=={'file','sha256'} and sha(r['file'])==r['sha256'];return read(r['file'])
parser=argparse.ArgumentParser();parser.add_argument('--modules-offer',required=True);parser.add_argument('--code-peer',required=True);args=parser.parse_args()
helper='book/coverage/checks/root_integrate_owner28_candidates_v6.py'
assert sha(helper)=='aa4340b7c42baeb3b5dc164d85fbfee936073d448e555f54e42d6e1e856cb37f'
code_peer=read(args.code_peer);assert code_peer['helper']==ref(helper) and code_peer['errors']==[]
spec=importlib.util.spec_from_file_location('reviewed_owner28_installer',safe(helper));installer=importlib.util.module_from_spec(spec);spec.loader.exec_module(installer)
offers={
 'core':'book/coverage/checks/future28-core/current60-identity-v1/core28-current60-identity-offer-canonical-v1.json',
 'foundations':'book/coverage/checks/future28-foundations/current60-owner28-v1/foundations28-current60-final-offer-v1.json',
 'applied':'book/coverage/checks/applied-future28/current60-identity-v1/applied28-current60-identity-offer-canonical-v2.json',
 'modules':args.modules_offer}
owners={}
for owner,n in offers.items():
 offer=read(n);candidate=offer['candidate'];checked(candidate)
 peer_ref=offer.get('final_mapping_peer') or offer['final_independent_candidate_mapping_peer'];peer=checked(peer_ref)
 assert peer['errors']==[] and peer['candidate']==candidate
 actual_ref=offer['actual_finalizer'];actual=checked(actual_ref);assert peer['actual_finalizer']==actual_ref
 assert type(actual['actual_exit_code']) is int and actual['actual_exit_code']==0
 logfields=['log','log_sha256'] if 'log' in actual else ['raw_log','raw_log_sha256']
 aliases=offer['actual_finalizer_original_byte_aliases']
 row={'destination':'book/coverage/'+owner+'.json','installed27_sha256':installer.OLD[owner],
  'candidate':candidate,'reviewed_offer':ref(n),'final_mapping_peer':peer_ref,
  'expected_final_mapping_peer_status':peer['status'],
  'offer_candidate_pointer':['candidate'],'peer_candidate_pointer':['candidate'],'peer_actual_finalizer_pointer':['actual_finalizer'],
  'actual_finalizer':actual_ref,'expected_actual_finalizer_status':actual['status'],
  'expected_actual_finalizer_command':actual['actual_command'],
  'expected_actual_finalizer_helpers_sha256':actual['helper_sha256_before'],
  'actual_finalizer_log_fields':logfields,'actual_finalizer_original_byte_aliases':aliases,
  'new_sources':{p:r['sha256'] for p,r in offer['proof_files'].items()}}
 assert sha(row['destination'])==row['installed27_sha256']
 if owner=='applied':
  assert peer['candidate_promotions']==offer['candidate_promotions']
  row['companion_candidates']=[{'destination':'book/coverage/applied-promotions.json','candidate':offer['candidate_promotions'],'offer_candidate_pointer':['candidate_promotions'],'peer_candidate_pointer':['candidate_promotions']}]
 owners[owner]=row
batches=[]
for readiness,execution,count,theorems in [
 ('book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json','reports/full-coverage/current60-canonical-pairs28-execution-v1.json',10,235),
 ('book/coverage/checks/future28-core/current60-commissioning17-canonical-pair-v1/actual-current60-commissioning17-canonical-paired-readiness28-v1.json','reports/full-coverage/current60-commissioning17-canonical-pair28-execution-v1.json',1,17)]:
 actual=read(execution);native=read(readiness)
 assert type(actual['actual_exit_code']) is int and actual['actual_exit_code']==0
 batches.append({'readiness':ref(readiness),'actual_execution':ref(execution),'expected_command':actual['actual_command'],'expected_helper_sha256':actual['helper_sha256_before'],'expected_readiness_status':native['status'],'source_count':count,'public_theorem_count':theorems})
additional_names=[
 'reports/full-coverage/source56-60-corrections-application-v1.json',
 'reports/full-coverage/source56-60-corrections-application28-execution-v1.json',
 'book/coverage/checks/future28-core/original-root28-execution-infrastructure-v1/original-closed-byte-aliases-v1.json',
 'book/coverage/checks/future28-core/correction59-author-fragment-sync-v1.json',
 'reports/full-coverage/integration-28-source60-static-v3.json',
 'reports/full-coverage/integration28-source60-static-execution-v3.json',
 'book/coverage/checks/future28-core/static-validator28-independent-applied-full-code-review-v1.json',
 'reports/full-coverage/browser-checkpoint-28.json',
 'reports/full-coverage/browser-corrections-28-inputs.json',
 'reports/full-coverage/source60-eight-captured-regions-manual-review28-v1.json',
 'reports/full-coverage/browser28-evidence-merge-execution-v1.json']
additional=[ref(n) for n in additional_names]
for n in ['reports/full-coverage/source56-60-corrections-application28-execution-v1.json','reports/full-coverage/integration28-source60-static-execution-v3.json','reports/full-coverage/browser28-evidence-merge-execution-v1.json']:
 actual=read(n);assert type(actual['actual_exit_code']) is int and actual['actual_exit_code']==0
 additional.append({'file':actual['log'],'sha256':actual['log_sha256']})
 assert sha(actual['log'])==actual['log_sha256']
assets=read('reports/full-coverage/browser-checkpoint-28.json')['source_sha256']
assert len(assets)==31 and all(sha(n)==h for n,h in assets.items())
result={'status':'all_four_reviewed_current60_owner28_candidates_bound_ready_for_root_execution',
 'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(helper),
 'independent_helper_review':ref(args.code_peer),'expected_independent_helper_review_status':code_peer['status'],
 'inventory':ref('book/coverage/inventory-after-correction60.json'),
 'baseline27_selection':ref('reports/full-coverage/checkpoint-27-selection.json'),
 'exact_current60_safelearning_assets_sha256':assets,'additional_immutable_inputs':additional,
 'canonical_pair_batches':batches,'owners':owners,'coverage_complete':False,'owner_installation_or_global_audit_claimed':False}
p=safe(DEST);assert not p.exists()
with p.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'binding':ref(DEST),'owners':4,'candidate_files':5,'new_sources':11}))

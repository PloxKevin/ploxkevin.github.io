"""Bind actual installed28/current60 integrity to the independently reviewed selector."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path(__file__).resolve().parents[3]
DEST='book/coverage/checks/future28-core/checkpoint28-installed-owner-selection-plan-v2.json'
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def ref(n):return {'file':n,'sha256':sha(n)}
def read(n):return json.loads((ROOT/n).read_bytes())
peer_name='book/coverage/checks/future28-foundations/independent-selection28-selector4-retainer3-code-peer-v1/selection28-selector4-retainer3-independent-foundations-closed-v1.json'
peer=read(peer_name);assert peer['errors']==[] and peer['helper']==ref('book/coverage/prepare_checkpoint28_selection_v4.py')
helpers=peer['reviewed_helpers_sha256'];assert len(helpers)==3 and all(sha(n)==h for n,h in helpers.items())
integration_name='reports/full-coverage/owner28-reviewed-candidate-integration-v1.json'
actual_name='reports/full-coverage/owner28-reviewed-candidate-integration-execution-v1.json'
global_name='reports/full-coverage/root-source60-final-owner-integration28-v1.json'
global_execution_name='reports/full-coverage/root-source60-final-owner-integration28-execution-v1.json'
integration=read(integration_name);actual=read(actual_name);global_report=read(global_name);global_actual=read(global_execution_name)
assert integration['applied'] is True and actual['status']=='passed' and type(actual['actual_exit_code']) is int and actual['actual_exit_code']==0
assert global_report['integrity_status']=='passed' and global_report['errors']==[] and global_report['mathematical_coverage_complete'] is False
assert type(global_actual['actual_exit_code']) is int and global_actual['actual_exit_code']==0 and sha(global_actual['log'])==global_actual['log_sha256']
binding=read(integration['binding_manifest']);extras={}
for owner,row in binding['owners'].items():
 offer=read(row['reviewed_offer']['file'])
 for n,r in offer.get('additional_frozen_inputs',{}).items():
  if type(r) is str:
   assert len(r)==64 and all(c in '0123456789abcdef' for c in r)
   r={'sha256':r,'scope':'immutable_audit_or_local_source_evidence'}
  assert type(r) is dict and set(r)=={'sha256','scope'} and r['scope']=='immutable_audit_or_local_source_evidence' and sha(n)==r['sha256']
  p=(ROOT/n).resolve()
  if not any(p.is_relative_to((ROOT/base).resolve()) for base in ['book/coverage','reports/full-coverage/source-history']):
   original=n
   suffix=Path(n).suffix if Path(n).suffix in {'.py','.json','.md','.log','.html','.lean','.js','.cjs','.txt'} else '.txt'
   n='book/coverage/checks/future28-core/selection28-extra-original-byte-aliases-v1/'+r['sha256']+'/'+Path(n).stem+suffix
   target=ROOT/n;target.parent.mkdir(parents=True,exist_ok=True)
   if target.exists():assert sha(n)==r['sha256']
   else:
    with target.open('xb') as f:f.write((ROOT/original).read_bytes())
   assert sha(n)==r['sha256']
  assert n not in extras or extras[n]==r;extras[n]=r
# These exact byte aliases include genuine failed attempts as historical evidence.
closure_name='book/coverage/checks/future28-core/original-root28-preintegration-native-v1/original-closed-byte-aliases-v1.json'
closure=read(closure_name)
for r in closure['aliases'].values():
 n=r['file'];assert sha(n)==r['sha256'];value={'sha256':r['sha256'],'scope':'immutable_audit_or_local_source_evidence'}
 assert n not in extras or extras[n]==value;extras[n]=value
result={'status':'exact_current60_owner28_and_eleven_sources_explicit_selection_plan','prepared_at_utc':datetime.now(timezone.utc).isoformat(),
 'independent_selection_helper_review':ref(peer_name),'expected_independent_selection_helper_review_status':peer['status'],
 'helpers_sha256':helpers,
 'baseline_selection':ref('reports/full-coverage/checkpoint-27-selection.json'),
 'baseline_manifest':ref('reports/full-coverage/checkpoint-27-manifest.json'),
 'baseline_audit':ref('reports/full-coverage/lean-checkpoint-27/verification-original.json'),
 'inventory':ref('book/coverage/inventory-after-correction60.json'),
 'integration_result':ref(integration_name),'actual_integration_execution':ref(actual_name),'global_integrity':ref(global_name),
 'actual_global_integrity_execution':ref(global_execution_name),'additional_frozen_inputs':extras,'coverage_complete':False}
p=ROOT/DEST;assert not p.exists()
with p.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'plan':ref(DEST),'additional_exact_frozen_inputs':len(extras)}))

"""Bind actual final checkpoint28 publication evidence into an explicit staging plan."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path(__file__).resolve().parents[3];PUB=ROOT/'reports/book/publication-repo'
DEST='book/coverage/checks/future28-core/root-explicit-audited28-publication-stage-plan-v1.json'
def safe(base,n):
 assert type(n) is str and n and Path(n).as_posix()==n and not Path(n).is_absolute() and '..' not in Path(n).parts
 p=base/n;assert p.resolve().is_relative_to(base) and not p.is_symlink();return p
def sha(base,n):return hashlib.sha256(safe(base,n).read_bytes()).hexdigest()
def ref(n):return {'file':n,'sha256':sha(ROOT,n)}
def read(n):return json.loads(safe(ROOT,n).read_bytes())
manifest=read('reports/full-coverage/checkpoint-28-manifest.json')
assert manifest['status']=='formal_verification_passed_partial_coverage' and manifest['coverage_complete'] is False
extra=dict(read('reports/full-coverage/publication28-supplementary-copies-v1.json')['paths_sha256'])
actual_names=['verify-checkpoint28-execution-v1','export-checkpoint28-execution-v1','export-integrity28-execution-v1',
 'static-checkpoint28-execution-v1','frozen-ledger-checkpoint28-execution-v1','prepare-publication28-execution-v1',
 'publication28-ledger-check-execution-v1','pages28-config-application-execution-v1','prepare-documents28-execution-v1']
prerequisites={}
for key in [*actual_names,'copy-publication28-supplements-execution-v1','pages28-config-preflight-execution-v1',
            'pages28-config-preflight-execution-v2','pages28-config-preflight-execution-v3']:
 n='reports/full-coverage/'+key+'.json';d=read(n)
 if key in actual_names:
  assert d['status']=='passed' and type(d['actual_exit_code']) is int and d['actual_exit_code']==0
  prerequisites[key]=ref(n)
 assert sha(ROOT,d['log'])==d['log_sha256']
 for p,h in [(n,sha(ROOT,n)),(d['log'],d['log_sha256'])]:
  assert p not in extra or extra[p]==h;extra[p]=h
for n in ['reports/full-coverage/publication28-supplementary-copies-v1.json','reports/full-coverage/publication-checks/ledger-checkpoint-28.json',
          'reports/full-coverage/pages28-config-preparation-v1.json','reports/full-coverage/pages28-config-previous-original-v1.yml',
          'reports/full-coverage/publication-prepared-28-files.json','book/coverage/checks/root_prepare_publication28_stage_plan_v1.py',
          *['book/coverage/checks/root_prepare_pages28_config_v'+str(i)+'.py' for i in [4,5]],
          *['book/coverage/checks/root_stage_publication28_v'+str(i)+'.py' for i in [5,6]]]:
 h=sha(ROOT,n);assert n not in extra or extra[n]==h;extra[n]=h
stage_peer_name='book/coverage/checks/future28-core/publication28-stage-independent-applied-code-review-v6.json'
stage_peer=read(stage_peer_name)
assert stage_peer['errors']==[] and stage_peer['helper']==ref('book/coverage/checks/root_stage_publication28_v6.py')
assert stage_peer['status'].startswith('passed_independent_')
config_peer_name='book/coverage/checks/future28-foundations/independent-pages28-config5-code-peer-v1/pages28-config5-independent-foundations-closed-v1.json'
config_peer=read(config_peer_name)
assert config_peer['errors']==[] and config_peer['helper']==ref('book/coverage/checks/root_prepare_pages28_config_v5.py')
assert config_peer['status'].startswith('passed_')
def collect(value):
 if type(value) is dict:
  if set(value)=={'file','sha256'}:
   n=value['file'];h=value['sha256']
   if type(n) is str and not Path(n).is_absolute():
    assert sha(ROOT,n)==h and (n not in extra or extra[n]==h);extra[n]=h
  for key,child in value.items():
   if key in ['closed_evidence_sha256','required_evidence_artifacts_sha256'] and type(child) is dict:
    for n,h in child.items():
     assert sha(ROOT,n)==h and (n not in extra or extra[n]==h);extra[n]=h
   collect(child)
 elif type(value) is list:
  for child in value:collect(child)
audit_peer_name='book/coverage/checks/future28-core/actual28-export-kernel-provenance-independent-modules-v1/actual28-export-kernel-provenance-independent-modules-peer-v1.json'
audit_peer=read(audit_peer_name)
assert audit_peer['errors']==[] and audit_peer['status'].startswith('passed_')
for n,peer in [(stage_peer_name,stage_peer),(config_peer_name,config_peer),(audit_peer_name,audit_peer)]:
 extra[n]=sha(ROOT,n);collect(peer)
 for key in ['catalog','original_closed_byte_catalog','exact_closed_evidence_catalog']:
  if key in peer:
   directory=Path(peer[key]['file']).parent.as_posix()
   assert directory.startswith(('book/coverage/checks/future28-core/','book/coverage/checks/future28-foundations/'))
   for p in safe(ROOT,directory).rglob('*'):
    if p.is_file():
     path=p.relative_to(ROOT).as_posix();h=sha(ROOT,path)
     assert path not in extra or extra[path]==h;extra[path]=h
n='reports/full-coverage/checkpoint-28/verification/lean/AxiomAudit.lean';extra[n]=sha(ROOT,n)
for n,h in extra.items():
 assert sha(ROOT,n)==h
 target=safe(PUB,n);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(safe(ROOT,n).read_bytes())
 assert sha(PUB,n)==h
plan={'status':'explicit_actual_audited_checkpoint28_publication_plan','prepared_at_utc':datetime.now(timezone.utc).isoformat(),
 'baseline_publication_head':'8fa808699674d13e4297d226ef1530a7ec744ad0',
 'manifest':ref('reports/full-coverage/checkpoint-28-manifest.json'),'selection':ref('reports/full-coverage/checkpoint-28-selection.json'),
 'original_audit':ref('reports/full-coverage/lean-checkpoint-28/verification-original.json'),
 'prepared_file_list':ref('reports/full-coverage/publication-prepared-28-files.json'),
 'actual_prerequisites':prerequisites,'publication_ledger':ref('reports/full-coverage/publication-checks/ledger-checkpoint-28.json'),
 'configuration_preparation':ref('reports/full-coverage/pages28-config-preparation-v1.json'),
 'independent_staging_helper_review':ref(stage_peer_name),'independent_pages_helper_review':ref(config_peer_name),
 'supplementary_paths_sha256':dict(sorted(extra.items())),'coverage_complete':False}
data=(json.dumps(plan,separators=(',',':'))+'\n').encode()
for base in [ROOT,PUB]:
 assert not safe(base,DEST).exists()
 with safe(base,DEST).open('xb') as f:f.write(data)
print(json.dumps({'status':plan['status'],'plan':ref(DEST),'supplementary_paths':len(extra)}))

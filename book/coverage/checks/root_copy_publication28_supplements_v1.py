"""Copy explicit current28 evidence and documentation after actual publication preparation."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT=Path(__file__).resolve().parents[3]; PUB=ROOT/'reports/book/publication-repo'
CLOSURE='book/coverage/checks/future28-core/publication28-supplementary-plan-modules-v1/publication28-supplementary-plan-exact-tmp-original-closure-v2.json'
def safe(base,n):
    assert type(n) is str and n and Path(n).as_posix()==n and not Path(n).is_absolute() and '..' not in Path(n).parts
    p=base/n;assert p.resolve().is_relative_to(base) and not p.is_symlink();return p
def sha(base,n):return hashlib.sha256(safe(base,n).read_bytes()).hexdigest()
def read(n):return json.loads(safe(ROOT,n).read_bytes())
def ref(n):return {'file':n,'sha256':sha(ROOT,n)}
manifest=read('reports/full-coverage/checkpoint-28-manifest.json')
assert manifest['status']=='formal_verification_passed_partial_coverage' and manifest['coverage_complete'] is False
prepared=read('reports/full-coverage/prepare-publication28-execution-v1.json')
assert prepared['status']=='passed' and type(prepared['actual_exit_code']) is int and prepared['actual_exit_code']==0
assert sha(ROOT,prepared['log'])==prepared['log_sha256']
assert sha(ROOT,CLOSURE)=='dbeec2a6365aa4ddd1a4feb90e6d1a7a340bc2b59008f5049800d86bfd99bce9'
closure=read(CLOSURE);paths=dict(closure['true_unique_extra_rootpaths_sha256_after_actual_manifest_deduplication'])
assert len(paths)==277
for key in ['prepare-owner28-binding-execution-v3','owner28-binding-preflight-execution-v2','owner28-reviewed-candidate-integration-execution-v1',
            'root-source60-final-owner-integration28-execution-v1','prepare-selection28-plan-execution-v1','prepare-selection28-plan-execution-v2',
            'prepare-selection28-plan-execution-v3','selection28-production-preflight-execution-v1','selection28-production-preflight-execution-v2',
            'selection28-production-application-execution-v1','freeze-checkpoint28-execution-v1','prepare-cache28-execution-v1',
            'verify-checkpoint28-execution-v1','export-checkpoint28-execution-v1','export-integrity28-execution-v1','static-checkpoint28-execution-v1',
            'frozen-ledger-checkpoint28-execution-v1','prepare-documents28-execution-v1','prepare-publication28-execution-v1']:
    n='reports/full-coverage/'+key+'.json';d=read(n)
    for p,h in [(n,sha(ROOT,n)),(d['log'],d['log_sha256'])]:
        assert p not in paths or paths[p]==h;paths[p]=h
for n in ['book/coverage/progress.json','reports/full-coverage/README.md','reports/full-coverage/checkpoint28-document-preparation-v1.json',
          'reports/full-coverage/progress-checkpoint28-before-preparation-original-v1.json','reports/full-coverage/readme-checkpoint28-before-preparation-original-v1.md',
          'reports/full-coverage/pre-export-ledger28-original-v1.json','reports/full-coverage/pre-export-ledger28-preservation-v1.json',
          'reports/full-coverage/checkpoint28-cache-preparation.json',
          *['book/coverage/checks/root_stage_publication28_v'+str(i)+'.py' for i in range(1,5)],
          'book/coverage/checks/root_prepare_checkpoint28_documents_v2.py',
          'book/coverage/checks/root_copy_publication28_supplements_v1.py']:
    h=sha(ROOT,n);assert n not in paths or paths[n]==h;paths[n]=h
for directory in ['book/coverage/checks/future28-core/publication28-supplementary-plan-modules-v1',
                  'book/coverage/checks/future28-core/original-selection28-freeze-independent-applied-v1',
                  'book/coverage/checks/future28-core/original-publication28-stager-independent-applied-v4']:
    for p in safe(ROOT,directory).rglob('*'):
        if p.is_file():
            n=p.relative_to(ROOT).as_posix();h=sha(ROOT,n);assert n not in paths or paths[n]==h;paths[n]=h
n='book/coverage/checks/future28-core/checkpoint28-selection-freeze-independent-applied-confirmation-v1.json';paths[n]=sha(ROOT,n)
n='book/coverage/checks/future28-core/publication28-stage-independent-applied-code-review-v4.json';paths[n]=sha(ROOT,n)
protected={n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith(('SafeLearning/','verification/lean/')) or n in ['book/coverage/'+d+'.json' for d in ['core','foundations','applied','modules','applied-promotions']]}
assert all(sha(ROOT,n)==h for n,h in protected.items())
out='reports/full-coverage/publication28-supplementary-copies-v1.json'
assert not safe(ROOT,out).exists() and not safe(PUB,out).exists()
for n,h in paths.items():assert sha(ROOT,n)==h and safe(ROOT,n).stat().st_size<100000000
for n,h in paths.items():
    target=safe(PUB,n);target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(safe(ROOT,n).read_bytes());assert sha(PUB,n)==h
assert all(sha(ROOT,n)==h for n,h in protected.items())
result={'status':'exact_explicit_publication28_supplementary_bytes_copied_delivery_pending',
        'copied_at_utc':datetime.now(timezone.utc).isoformat(),'module_plan_closure':ref(CLOSURE),
        'paths_sha256':dict(sorted(paths.items())),'coverage_complete':False,
        'scope':'Bounded current28 native evidence, exact correction56–60 originals, original browser regions, current documents and independent preparation evidence. These late paths remain supplemental; the frozen50797 input manifest is unchanged.'}
data=(json.dumps(result,separators=(',',':'))+'\n').encode()
for base in [ROOT,PUB]:
    with safe(base,out).open('xb') as f:f.write(data)
print(json.dumps({'status':result['status'],'paths':len(paths),'report':ref(out)}))

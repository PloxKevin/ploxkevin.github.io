"""Preserve bounded original execution evidence without retiming any review."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/future28-core/original-root28-execution-infrastructure-v1'
FILES=[
 '/tmp/root_actual_step27_v1.py',
 '/tmp/root_prepare_current60_canonical_plan28_v1.py',
 '/tmp/root28-current60-canonical-pair-plan-v1.json',
 'book/coverage/checks/run_root28_current60_canonical_pairs_v1.py',
 'book/coverage/checks/run_root28_current60_canonical_pairs_v2.py',
 'book/coverage/checks/future28-core/root-current60-canonical-executor-independent-applied-code-review-v2.json',
 '/tmp/root_prepare_commissioning17_canonical28_v1.py',
 '/tmp/root28-current60-commissioning17-canonical-plan-v1.json',
 'book/coverage/checks/run_root28_current60_commissioning17_canonical_pair_v1.py',
 '/tmp/root28-commissioning17-executor-independent-modules28-closed-v1.json',
 '/tmp/root_prepare_static_validator28_v1.py',
 'book/validate.py','book/validate28_v1.py',
 'book/coverage/checks/root_sync_correction59_author_fragment28_v1.py',
 'book/coverage/checks/root_sync_correction59_author_fragment28_v2.py',
 'book/coverage/checks/future28-core/correction59-author-fragment-sync-v1.json',
 'reports/full-coverage/integration-28-source60-static-v2.json',
 'reports/full-coverage/integration-28-source60-static-v3.json',
]
STEPS=[
 'prepare-current60-canonical-plan28-execution-v1',
 'current60-canonical-pairs28-readiness-execution-v1',
 'current60-canonical-pairs28-readiness-execution-v2',
 'current60-canonical-pairs28-execution-v1',
 'prepare-current60-commissioning17-canonical28-execution-v1',
 'current60-commissioning17-canonical-pair28-execution-v1',
 'prepare-static-validator28-execution-v1',
 'integration28-source60-static-execution-v1',
 'integration28-source60-static-execution-v2',
 'integration28-source60-static-execution-v3',
 'correction59-author-fragment-sync28-execution-v1',
 'correction59-author-fragment-sync28-execution-v2',
]
FILES += ['reports/full-coverage/'+n+s for n in STEPS for s in ['.json','.log']]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def locate(n):
 p=Path(n);p=p if p.is_absolute() else ROOT/p
 assert p.is_file() and not p.is_symlink() and p.stat().st_size<20_000_000
 return p
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
def new(p,data):
 assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('xb') as f:f.write(data)
assert not BASE.exists()
held={n:sha(locate(n)) for n in FILES}
selection=json.loads((ROOT/'reports/full-coverage/checkpoint-27-selection.json').read_bytes())
protected={n:r['sha256'] for n,r in selection['proof_files'].items()}
for path in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json','book/coverage/inventory.json','book/coverage/material-corrections.json','book/chapters/lipsdp.html']:
 protected[path]=sha(ROOT/path)
for n,h in json.loads((ROOT/'book/coverage/inventory.json').read_bytes())['source_sha256'].items():protected[n]=h
def guard():
 for n,h in protected.items():assert sha(ROOT/n)==h,n
 for n,h in held.items():assert sha(locate(n))==h,n
guard()
aliases={}
for n,h in held.items():
 p=locate(n);t=BASE/h/p.name
 if t.exists():assert sha(t)==h
 else:new(t,p.read_bytes())
 assert sha(t)==h;aliases[n]=ref(t)
guard()
catalog={'status':'exact_original_execution_infrastructure28_bytes_closed_no_new_review_or_retime',
 'closed_at_utc':datetime.now(timezone.utc).isoformat(),'originals':aliases,
 'original_file_count':len(aliases),'all_selected1175_and_current60_owner27_guards_unchanged':True,
 'preserved_actual_failures':['integration28-source60-static-execution-v1','integration28-source60-static-execution-v2','correction59-author-fragment-sync28-execution-v1'],
 'limits':'Copies retain the exact original commands, exits, helper hashes, raw logs, bodies and times. Successful later runs do not overwrite original failures.'}
p=BASE/'original-closed-byte-aliases-v1.json';new(p,(json.dumps(catalog,indent=2)+'\n').encode())
print(json.dumps({'catalog':ref(p),'originals':len(aliases),'bytes':sum(locate(n).stat().st_size for n in held)}))

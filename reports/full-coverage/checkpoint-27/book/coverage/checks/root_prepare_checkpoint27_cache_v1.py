"""Copy exact selected local artifacts; a fresh normal build must validate them."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil
ROOT=Path(__file__).resolve().parents[3]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
selection_path=ROOT/'reports/full-coverage/checkpoint-27-selection.json'
selection=json.loads(selection_path.read_text())
assert selection['proof_file_count']==len(selection['proof_files'])==1175 and selection['new_file_count']==8
snapshot=ROOT/'reports/full-coverage/checkpoint-27'
baseline=ROOT/'reports/full-coverage/checkpoint-26'
manifest_path=ROOT/'reports/full-coverage/checkpoint-27-manifest.json'
manifest=json.loads(manifest_path.read_text())
assert manifest['selection_sha256']==sha(selection_path) and manifest['proof_files']==selection['proof_files']
assert manifest['snapshot']=='reports/full-coverage/checkpoint-27'
original26=json.loads((ROOT/'reports/full-coverage/checkpoint-26-selection.json').read_text())
assert len(original26['proof_files'])==1167
assert {name:selection['proof_files'][name]['sha256'] for name in original26['proof_files']}=={name:row['sha256'] for name,row in original26['proof_files'].items()}
report_path=ROOT/'reports/full-coverage/checkpoint27-cache-preparation.json'
assert not report_path.exists()
started=datetime.now(timezone.utc).isoformat()
rows=[]
for source, record in selection['proof_files'].items():
    relative=Path(source).relative_to('verification/lean')
    origin=baseline/'verification/lean' if (baseline/source).exists() else ROOT/'verification/lean'
    assert sha(origin/relative)==record['sha256']==sha(snapshot/source)
    for subtree in ('lib/lean','ir'):
        base=origin/'.lake/build'/subtree/relative.parent
        for artifact in sorted(base.glob(relative.stem+'.*')):
            if not artifact.is_file(): continue
            target=snapshot/'verification/lean'/artifact.relative_to(origin)
            expected=sha(artifact)
            target.parent.mkdir(parents=True,exist_ok=True)
            if target.exists(): assert sha(target)==expected
            else: shutil.copyfile(artifact,target)
            assert sha(target)==expected
            rows.append(dict(prior=str(artifact.relative_to(ROOT)),copied=str(target.relative_to(ROOT)),sha256=expected,size_bytes=artifact.stat().st_size))
report=dict(status='exact_selected_artifact_cache_copied_requires_real_build_and_kernel_audit',started_at_utc=started,finished_at_utc=datetime.now(timezone.utc).isoformat(),selection_sha256=sha(selection_path),module_count=len(selection['proof_files']),artifacts=rows,artifact_count=len(rows),bytes=sum(r['size_bytes'] for r in rows),scope='Only source-matched selected module cache artifacts copied. The aggregate is excluded. No compiler, kernel or axiom success inferred.')
report_path.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='artifacts'}))

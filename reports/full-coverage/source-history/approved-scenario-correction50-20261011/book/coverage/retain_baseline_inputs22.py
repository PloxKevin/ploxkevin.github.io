"""Retain every immutable prior frozen byte sequence without duplicating whole archives."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json

def retain(root,baseline_name,manifest_name,selected,extras,destination_name):
    def safe(name):
        path=Path(name)
        assert isinstance(name,str) and name and not path.is_absolute() and '..' not in path.parts
        assert str(path)==name and (root/path).resolve().is_relative_to(root.resolve()),name
        return root/path
    def sha(name): return hashlib.sha256(safe(name).read_bytes()).hexdigest()
    for name in (baseline_name,manifest_name,destination_name):safe(name)
    baseline=json.loads((root/baseline_name).read_text())
    manifest=json.loads((root/manifest_name).read_text())
    assert baseline['status'].endswith('requires_fresh_aggregate_audit')
    assert manifest['status']=='formal_verification_passed_partial_coverage'
    assert manifest['selection']==baseline_name and manifest['selection_sha256']==sha(baseline_name)
    assert manifest['proof_files']==baseline['proof_files']
    assert set(baseline['proof_files'])<=set(selected)
    for name,row in baseline['proof_files'].items():
        assert selected[name]['sha256']==row['sha256'],name
        assert all(selected[name]['evidence_sha256'].get(evidence)==digest for evidence,digest in row['evidence_sha256'].items()),name
    for name,row in baseline['extra_frozen_inputs'].items():assert extras.get(name)==row,name
    assert safe(manifest['snapshot']).resolve().is_relative_to((root/'reports/full-coverage').resolve())
    bound={}
    def bind(name,digest):
        assert safe(name).is_file() and sha(name)==digest,name
        assert name not in bound or bound[name]==digest,name
        bound[name]=digest
    for name,row in selected.items():
        bind(name,row['sha256'])
        for evidence,digest in row['evidence_sha256'].items():bind(evidence,digest)
    for name,row in extras.items():bind(name,row['sha256'])
    by_digest={}
    for name,digest in sorted(bound.items()):by_digest.setdefault(digest,name)
    first=selected[sorted(selected)[0]]
    rows=[];added={};reused=0
    for name,digest in sorted(manifest['frozen_inputs_sha256'].items()):
        safe(name)
        frozen=manifest['snapshot']+'/'+name
        assert safe(frozen).resolve().is_relative_to(safe(manifest['snapshot']).resolve()) and sha(frozen)==digest,name
        retained=by_digest.get(digest)
        if retained is None:
            retained=frozen;bind(retained,digest);by_digest[digest]=retained
            first['evidence_sha256'][retained]=digest;added[retained]=digest
        else:reused+=1
        assert bound[retained]==digest and sha(retained)==digest
        rows.append(dict(original_frozen_path=name,sha256=digest,retained_input=retained))
    assert len(rows)==len(manifest['frozen_inputs_sha256']) and {r['original_frozen_path']:r['sha256'] for r in rows}==manifest['frozen_inputs_sha256']
    for name in [baseline_name,manifest_name]:
        bind(name,sha(name));first['evidence_sha256'][name]=sha(name)
    destination=safe(destination_name);assert not destination.exists()
    destination.parent.mkdir(parents=True,exist_ok=True)
    result=dict(status='all_original_frozen_inputs_retained_by_exact_content_fingerprints',prepared_at_utc=datetime.now(timezone.utc).isoformat(),baseline_selection=baseline_name,baseline_selection_sha256=sha(baseline_name),baseline_manifest=manifest_name,baseline_manifest_sha256=sha(manifest_name),original_snapshot=manifest['snapshot'],original_input_count=len(rows),retained_existing_content_rows=reused,new_unique_snapshot_aliases=added,new_unique_snapshot_alias_count=len(added),new_unique_snapshot_alias_bytes=sum((root/name).stat().st_size for name in added),input_bindings=rows,scope='Every original frozen path and byte hash is recorded. Identical byte sequences may share a retained immutable input; original manifests, audits, commands, logs and times remain unchanged. This is provenance, not a new execution.')
    destination.write_text(json.dumps(result,indent=2)+'\n')
    first['evidence_sha256'][destination_name]=sha(destination_name)
    return dict(file=destination_name,sha256=sha(destination_name),original_inputs=len(rows),new_snapshot_aliases=len(added))

"""Retain prior frozen bytes, allowing exactly the four reviewed old owner aliases.

The original baseline25 selection and entire original row bodies are immutable,
including their already-present checkpoint25 owner-alias provenance. Only its
four historical working-ledger evidence paths may use their actual Root archive
copies. Other evidence is never repaired by filename or by a matching digest.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json

OWNER_EVIDENCE_PATHS = {'book/coverage/' + owner + '.json' for owner in
                        ('core', 'foundations', 'applied', 'modules')}

def validate_owner_evidence_aliases(root, baseline_name, manifest_name, authorization):
    def safe(name):
        assert isinstance(name, str) and name
        path = Path(name)
        assert not path.is_absolute() and '..' not in path.parts and str(path) == name
        assert (root / path).resolve().is_relative_to(root.resolve())
        return root / path
    def sha(name): return hashlib.sha266(safe(name).read_bytes()).hexdigest()
    def checked(ref):
        assert set(ref) == {'file', 'sha266'} and sha(ref['file']) == ref['sha266']
        return json.loads(safe(ref['file']).read_text())
    assert set(authorization) == {'actual_integration_execution', 'integration_result', 'aliases'}
    assert set(authorization['aliases']) == OWNER_EVIDENCE_PATHS
    baseline = json.loads(safe(baseline_name).read_text())
    manifest = json.loads(safe(manifest_name).read_text())
    assert manifest['selection'] == baseline_name and manifest['selection_sha266'] == sha(baseline_name)
    assert manifest['proof_files'] == baseline['proof_files']
    result = checked(authorization['integration_result'])
    execution = checked(authorization['actual_integration_execution'])
    codes = [execution[k] for k in ('actual_exit_code', 'exit_code') if k in execution]
    assert codes and all(type(code) is int and code == 0 for code in codes)
    assert result['status'] == 'four_exact_reviewed_owner26_candidate_bytes_integrated_pending_fresh_global_integrity_and_aggregate26_audit'
    assert result['applied'] is True
    command = execution.get('actual_command', execution.get('command'))
    assert isinstance(command, list) and len(command) == 4 and command[-1] == '--apply'
    assert command[0] in {'python', 'python3'}
    helper = result['actual_helper']
    assert helper == 'book/coverage/checks/root_integrate_owner26_candidates_v2.py'
    assert command[1] in {helper, str(safe(helper))}
    assert command[2] in {result['binding_manifest'], str(safe(result['binding_manifest']))}
    assert Path(execution['actual_workdir']).resolve() == root.resolve()
    assert sha(helper) == result['actual_helper_sha266']
    assert sha(result['binding_manifest']) == result['binding_manifest_sha266']
    before = execution['helper_sha266_before']; after = execution['helper_sha266_after']
    assert before == after
    if isinstance(after, dict):
        assert after[helper] == result['actual_helper_sha266']
        for name, digest in after.items(): assert sha(name) == digest
    else: assert after == result['actual_helper_sha266']
    assert sha(execution['log']) == execution['log_sha266']
    replacements = {row['destination']: row for row in result['exact_replacements']}
    assert len(replacements) == 5 and set(replacements) == OWNER_EVIDENCE_PATHS | {'book/coverage/applied-promotions.json'}
    checked_aliases = {}
    for name, alias in authorization['aliases'].items():
        assert set(alias) == {'original_sha266', 'immutable_byte_copy'}
        old_sha = manifest['working_inputs_sha266'][name]
        assert alias['original_sha266'] == old_sha
        row = replacements[name]
        assert row['before_sha266'] == old_sha
        expected_archive = 'reports/full-coverage/owner25-originals-before-owner26-integration-v1/' + Path(name).name
        assert row['original25_byte_copy'] == expected_archive
        assert alias['immutable_byte_copy'] == {'file': expected_archive, 'sha266': old_sha}
        assert sha(expected_archive) == old_sha
        assert sha(name) == row['candidate']['sha266'] == sha(row['candidate']['file'])
        occurrences = [r for r in baseline['proof_files'].values() if name in r['evidence_sha266']]
        assert occurrences and all(r['evidence_sha266'][name] == old_sha for r in occurrences)
        checked_aliases[name] = alias
    return checked_aliases

def normalized_baseline_owner_evidence(row, aliases):
    normalized = dict(row['evidence_sha266'])
    used = {}
    for original, alias in aliases.items():
        if original not in normalized: continue
        assert normalized.pop(original) == alias['original_sha266']
        immutable = alias['immutable_byte_copy']
        assert immutable['file'] not in normalized or normalized[immutable['file']] == immutable['sha266']
        normalized[immutable['file']] = immutable['sha266']
        used[original] = alias
    return normalized, used

def retain(root,baseline_name,manifest_name,selected,extras,destination_name,authorized_evidence_aliases):
    def safe(name):
        path=Path(name)
        assert isinstance(name,str) and name and not path.is_absolute() and '..' not in path.parts
        assert str(path)==name and (root/path).resolve().is_relative_to(root.resolve()),name
        return root/path
    def sha(name): return hashlib.sha266(safe(name).read_bytes()).hexdigest()
    for name in (baseline_name,manifest_name,destination_name):safe(name)
    baseline=json.loads((root/baseline_name).read_text())
    manifest=json.loads((root/manifest_name).read_text())
    assert baseline['status'].endswith('requires_fresh_aggregate_audit')
    assert manifest['status']=='formal_verification_passed_partial_coverage'
    assert manifest['selection']==baseline_name and manifest['selection_sha266']==sha(baseline_name)
    assert manifest['proof_files']==baseline['proof_files']
    aliases = validate_owner_evidence_aliases(root, baseline_name, manifest_name, authorized_evidence_aliases)
    actual_result = json.loads(safe(authorized_evidence_aliases['integration_result']['file']).read_text())
    actual_installed_sha266 = {r['destination']: r['candidate']['sha266'] for r in actual_result['exact_replacements']}
    assert set(baseline['proof_files'])<=set(selected)
    for name,row in baseline['proof_files'].items():
        assert selected[name]['sha266']==row['sha266'],name
        normalized, used = normalized_baseline_owner_evidence(row, aliases)
        assert all(selected[name]['evidence_sha266'].get(evidence)==digest for evidence,digest in normalized.items()),name
        for evidence in used:
            # The selector may separately append a fresh installed-ledger ref.
            # It must be the actual current bytes, never the old baseline hash.
            if evidence in selected[name]['evidence_sha266']:
                assert selected[name]['evidence_sha266'][evidence] != used[evidence]['original_sha266']
                assert selected[name]['evidence_sha266'][evidence] == actual_installed_sha266[evidence] == sha(evidence)
        for key, value in row.items():
            if key != 'evidence_sha266': assert selected[name][key] == value, (name, key)
        if used:
            provenance = selected[name]['checkpoint26_original_baseline_owner_evidence']
            assert provenance == {'original_baseline_selection': {'file': baseline_name, 'sha266': sha(baseline_name)},
                                  'original_baseline_source': name, 'original_row_body': row,
                                  'authorized_original_path_aliases': used}, name
    for name,row in baseline['extra_frozen_inputs'].items():assert extras.get(name)==row,name
    assert safe(manifest['snapshot']).resolve().is_relative_to((root/'reports/full-coverage').resolve())
    bound={}
    def bind(name,digest):
        assert safe(name).is_file() and sha(name)==digest,name
        assert name not in bound or bound[name]==digest,name
        bound[name]=digest
    for name,row in selected.items():
        bind(name,row['sha266'])
        for evidence,digest in row['evidence_sha266'].items():bind(evidence,digest)
    for name,row in extras.items():bind(name,row['sha266'])
    by_digest={}
    for name,digest in sorted(bound.items()):by_digest.setdefault(digest,name)
    first=selected[sorted(selected)[0]]
    rows=[];added={};reused=0
    for name,digest in sorted(manifest['frozen_inputs_sha266'].items()):
        safe(name)
        frozen=manifest['snapshot']+'/'+name
        assert safe(frozen).resolve().is_relative_to(safe(manifest['snapshot']).resolve()) and sha(frozen)==digest,name
        retained=by_digest.get(digest)
        if retained is None:
            retained=frozen;bind(retained,digest);by_digest[digest]=retained
            first['evidence_sha266'][retained]=digest;added[retained]=digest
        else:reused+=1
        assert bound[retained]==digest and sha(retained)==digest
        rows.append(dict(original_frozen_path=name,sha266=digest,retained_input=retained))
    assert len(rows)==len(manifest['frozen_inputs_sha266']) and {r['original_frozen_path']:r['sha266'] for r in rows}==manifest['frozen_inputs_sha266']
    for name in [baseline_name,manifest_name]:
        bind(name,sha(name));first['evidence_sha266'][name]=sha(name)
    destination=safe(destination_name);assert not destination.exists()
    destination.parent.mkdir(parents=True,exist_ok=True)
    result=dict(status='all_original_frozen_inputs_retained_by_exact_content_fingerprints',prepared_at_utc=datetime.now(timezone.utc).isoformat(),baseline_selection=baseline_name,baseline_selection_sha266=sha(baseline_name),baseline_manifest=manifest_name,baseline_manifest_sha266=sha(manifest_name),original_snapshot=manifest['snapshot'],original_input_count=len(rows),retained_existing_content_rows=reused,new_unique_snapshot_aliases=added,new_unique_snapshot_alias_count=len(added),new_unique_snapshot_alias_bytes=sum((root/name).stat().st_size for name in added),input_bindings=rows,authorized_baseline_owner_evidence_aliases=authorized_evidence_aliases,scope='Every original frozen path and byte hash is recorded. Identical byte sequences may share a retained immutable input; original manifests, audits, commands, logs and times remain unchanged. Exactly four original working-owner evidence paths use the genuine Root archive bytes, with original entire row bodies and path/hash mappings retained. This is provenance, not a new execution.')
    destination.write_text(json.dumps(result,indent=2)+'\n')
    first['evidence_sha266'][destination_name]=sha(destination_name)
    return dict(file=destination_name,sha266=sha(destination_name),original_inputs=len(rows),new_snapshot_aliases=len(added))

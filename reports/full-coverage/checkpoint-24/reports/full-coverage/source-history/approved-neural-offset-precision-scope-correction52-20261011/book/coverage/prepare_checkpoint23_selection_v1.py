"""Prepare checkpoint23 only from an exact, independently reviewed production plan.

The plan pins installed owner23 ledgers, actual builders, independent mapping
peers and the current global integrity report. Importing this helper is read-only.
No production execution is authorized by the mere existence of candidate offers.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import copy
import hashlib
import json
import re

from lean_names import declarations
from retain_baseline_inputs23 import retain

ROOT = Path(__file__).resolve().parents[2]
INVENTORY = 'book/coverage/inventory-after-correction51.json'
INVENTORY_SHA = 'd746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
BASELINE = 'reports/full-coverage/checkpoint-22-selection.json'
BASELINE_SHA = '083fe75e535ebbd37326e34407d13b90357738ea7f4244eb1cfe5da8226f9ff9'
MANIFEST = 'reports/full-coverage/checkpoint-22-manifest.json'
AUDIT = 'reports/full-coverage/lean-checkpoint-22/verification-original.json'
DESTINATION = 'reports/full-coverage/checkpoint-23-selection.json'
CONTENT_MAP = 'book/coverage/checks/frozen22-input-content-bindings23-v1.json'


def safe(name):
    assert isinstance(name, str) and name
    path = Path(name)
    assert not path.is_absolute() and '..' not in path.parts and str(path) == name
    assert (ROOT / path).resolve().is_relative_to(ROOT.resolve())
    return ROOT / path


def sha(name):
    return hashlib.sha256(safe(name).read_bytes()).hexdigest()


def read(name):
    return json.loads(safe(name).read_text())


def exact(mapping):
    assert isinstance(mapping, dict)
    for name, digest in mapping.items():
        assert isinstance(digest, str) and re.fullmatch('[0-9a-f]{64}', digest)
        assert sha(name) == digest, name


def checked(pointer):
    assert set(pointer) == {'file', 'sha256'}
    assert sha(pointer['file']) == pointer['sha256']
    return read(pointer['file'])


def actual_exit_zero(record):
    codes = [record[k] for k in ('actual_exit_code', 'exit_code') if k in record]
    assert codes and all(type(code) is int and code == 0 for code in codes)


def standalone_success(source, digest, evidence):
    """Locate an original actual standalone record, preserving all path aliases.

    Original JSON fields may spell exit_code/actual_exit_code and source/lean_file.
    The canonical evidence paths may differ from the raw original log/snapshot
    names. Every alias is validated by exact bytes, never by filename resemblance.
    A named lake build or lean -o run does not substitute for standalone evidence.
    """
    exact(evidence)
    evidence_hashes = set(evidence.values()) | {digest}
    matches, named_matches = [], []
    for name in evidence:
        if not name.endswith('.json'):
            continue
        record = read(name)
        if not isinstance(record, dict):
            continue
        command = record.get('command', record.get('actual_command'))
        if not isinstance(command, list):
            continue
        standalone = len(command) == 4 and command[:3] == ['lake', 'env', 'lean']
        named_lake = command == ['lake', 'build', 'SafeLearning.' + Path(source).stem]
        named_lean = len(command) == 6 and command[:4] == ['lake', 'env', 'lean', '-o']
        if not (standalone or named_lake or named_lean):
            continue
        recorded_source = record.get('source', record.get('lean_file'))
        if recorded_source not in {source, command[-1]}:
            continue
        if record.get('source_sha256_before') != digest or record.get('source_sha256_after') != digest:
            continue
        actual_exit_zero(record)
        assert record.get('source_unchanged', True) is True
        workdir = record.get('actual_workdir', record.get('actual_cwd', record.get('cwd')))
        assert isinstance(workdir, str) and Path(workdir).resolve() == (ROOT / 'verification/lean').resolve()
        canonical_input = str(Path(source).relative_to('verification/lean'))
        if not named_lake and command[-1] != canonical_input:
            # A historical absolute input needs its exact original source snapshot.
            assert Path(command[-1]).is_absolute()
            assert recorded_source == command[-1] or recorded_source == source
            snapshot_hash = record.get('source_snapshot_sha256', record.get('preserved_source_sha256'))
            assert snapshot_hash == digest and snapshot_hash in evidence_hashes
        log_hash = record.get('log_sha256', record.get('raw_log_sha256'))
        assert isinstance(log_hash, str)
        assert any(Path(path).suffix == '.log' and value == log_hash for path, value in evidence.items())
        snapshot_hash = record.get('source_snapshot_sha256', record.get('preserved_source_sha256'))
        if snapshot_hash is not None:
            assert snapshot_hash == digest and snapshot_hash in evidence_hashes
        (matches if standalone else named_matches).append(name)
    assert matches, 'No exact actual standalone success: ' + source
    assert named_matches, 'No exact actual paired named success: ' + source
    return sorted(matches)[0]


def prepare(plan_name):
    plan = read(plan_name)
    assert plan['status'] == 'independently_reviewed_installed_owner23_selection_plan'
    assert plan['inventory'] == {'file': INVENTORY, 'sha256': INVENTORY_SHA}
    assert sha(INVENTORY) == sha('book/coverage/inventory.json') == INVENTORY_SHA
    assert not safe(DESTINATION).exists() and not safe(CONTENT_MAP).exists()
    assert plan['destination'] == DESTINATION and plan['content_map'] == CONTENT_MAP
    baseline = checked(plan['baseline_selection'])
    assert plan['baseline_selection'] == {'file': BASELINE, 'sha256': BASELINE_SHA}
    audit, manifest = checked(plan['baseline_audit']), checked(plan['baseline_manifest'])
    assert plan['baseline_audit']['file'] == AUDIT and plan['baseline_manifest']['file'] == MANIFEST
    assert audit['status'] == 'passed' and audit['proof_file_count'] == 1113
    assert all(row['exit_code'] == 0 for row in audit['checks'])
    assert len(baseline['proof_files']) == 1113
    assert audit['proof_sha256'] == {name: row['sha256'] for name, row in baseline['proof_files'].items()}
    assert manifest['status'] == 'formal_verification_passed_partial_coverage'
    assert len(manifest['frozen_inputs_sha256']) == 34051
    assert manifest['selection'] == BASELINE and manifest['selection_sha256'] == BASELINE_SHA
    exact(plan['helpers_sha256'])
    assert str(Path(__file__).relative_to(ROOT)) in plan['helpers_sha256']
    assert 'book/coverage/retain_baseline_inputs23.py' in plan['helpers_sha256']
    selection = copy.deepcopy(baseline['proof_files'])
    for source, row in selection.items():
        assert sha(source) == row['sha256']
        exact(row['evidence_sha256'])
    first = selection[sorted(selection)[0]]
    first['evidence_sha256'].update({BASELINE: BASELINE_SHA, MANIFEST: sha(MANIFEST), AUDIT: sha(AUDIT), plan_name: sha(plan_name)})
    for path in (ROOT / 'reports/full-coverage/lean-checkpoint-22').rglob('*'):
        if path.is_file():
            name = str(path.relative_to(ROOT))
            first['evidence_sha256'][name] = sha(name)
    first['checkpoint23_inherited_snapshot_provenance_scope'] = 'Every frozen22 original path and byte hash is retained by the exact content binding map. Original audits, commands and times remain historical.'
    owners = plan['owners']
    assert set(owners) == {'core', 'modules', 'foundations', 'applied'}
    documents, peers, new_sources = {}, {}, set()
    for owner, refs in owners.items():
        offer = checked(refs['offer']); documents[owner] = offer
        ledger_name = 'book/coverage/' + owner + '.json'
        assert refs['ledger']['file'] == ledger_name
        ledger = checked(refs['ledger'])
        assert offer.get('mapped_ledger', offer.get('module_ledger')) == ledger_name
        assert offer.get('mapped_ledger_sha256', offer.get('module_ledger_sha256')) == refs['ledger']['sha256']
        assert offer.get('current_inventory_sha256', offer.get('inventory_sha256')) == INVENTORY_SHA
        exact(offer['source_sha256'])
        actual_builder = checked(refs['actual_builder'])
        actual_exit_zero(actual_builder)
        assert sha(refs['builder']['file']) == refs['builder']['sha256']
        command = actual_builder.get('command', actual_builder.get('actual_command'))
        assert isinstance(command, list) and command[0] in {'python', 'python3'}
        assert command[1] in {refs['builder']['file'], str(safe(refs['builder']['file']))}
        assert Path(actual_builder['actual_workdir']).resolve() == ROOT.resolve()
        recorded_builder_hash = actual_builder.get('actual_checker_sha256', actual_builder.get('helper_sha256_after'))
        assert recorded_builder_hash is not None
        if isinstance(recorded_builder_hash, dict):
            before = actual_builder['helper_sha256_before']
            assert before == recorded_builder_hash
            basename = Path(refs['builder']['file']).name
            assert recorded_builder_hash.get(refs['builder']['file'], recorded_builder_hash.get(basename)) == refs['builder']['sha256']
            exact({name if '/' in name else 'book/coverage/' + name: digest for name, digest in recorded_builder_hash.items()})
        else:
            assert recorded_builder_hash == refs['builder']['sha256']
            if 'helper_sha256_before' in actual_builder:
                assert actual_builder['helper_sha256_before'] == recorded_builder_hash
        builder_log = refs['actual_builder_log']
        assert sha(builder_log['file']) == builder_log['sha256']
        assert actual_builder.get('log_sha256', actual_builder.get('original_log_sha256')) == builder_log['sha256']
        peer = checked(refs['independent_mapping_peer'])
        assert not peer.get('errors', [])
        assert 'passed' in peer['status'] or 'confirmed' in peer['status']
        peers[owner] = refs['independent_mapping_peer']
        first['evidence_sha256'].update({r['file']: r['sha256'] for r in refs.values() if isinstance(r, dict) and set(r) == {'file', 'sha256'}})
        proofs = offer.get('proof_files', {})
        assert set(proofs) == set(refs['expected_owned_proof_sources'])
        for source, row in proofs.items():
            assert sha(source) == row['sha256']
            exact(row['evidence_sha256'])
            if source in selection:
                assert selection[source]['sha256'] == row['sha256']
                for evidence_name, evidence_hash in row['evidence_sha256'].items():
                    assert evidence_name not in selection[source]['evidence_sha256'] or selection[source]['evidence_sha256'][evidence_name] == evidence_hash
                selection[source]['evidence_sha256'].update(row['evidence_sha256'])
            else:
                record = standalone_success(source, row['sha256'], row['evidence_sha256'])
                selection[source] = copy.deepcopy(row)
                selection[source]['original_actual_zero_record'] = record
                new_sources.add(source)
    assert set(new_sources) == set(plan['expected_new_proof_sources'])
    assert len(selection) == 1113 + len(new_sources)
    global_audit = checked(plan['global_integrity'])
    assert global_audit['integrity_status'] == 'passed' and global_audit['errors'] == []
    assert global_audit['inventory_sha256'] == INVENTORY_SHA
    assert {d['domain'] for d in global_audit['domains']} == set(owners)
    for d in global_audit['domains']:
        assert d['ledger_sha256'] == owners[d['domain']]['ledger']['sha256']
    all_names = {d['name'] for source in selection for d in declarations(safe(source).read_text())}
    for owner in owners:
        ledger = read(owners[owner]['ledger']['file'])
        for claim in ledger['material_claims'] + [c for e in ledger['exercises'] for c in e['claims']]:
            assert set(claim['lean_declarations']) <= all_names, (owner, claim['id'])
        imports = documents[owner].get('required_external_import_dependencies', {})
        exact(imports)
        assert set(imports) <= set(selection)
    for source in selection:
        for line in re.findall(r'^import[^\n]*', safe(source).read_text(), re.M):
            for dep in line.split()[1:]:
                if dep.startswith('SafeLearning.'):
                    assert 'verification/lean/' + dep.replace('.', '/') + '.lean' in selection, (source, dep)
    extras = copy.deepcopy(baseline['extra_frozen_inputs'])
    for name, row in extras.items():
        assert sha(name) == row['sha256']
    for name, row in plan['additional_frozen_inputs'].items():
        assert set(row) == {'sha256', 'scope'} and row['scope'] == 'immutable_audit_or_local_source_evidence'
        assert safe(name).resolve().is_relative_to((ROOT / 'book/coverage').resolve()) or safe(name).resolve().is_relative_to((ROOT / 'reports/full-coverage/source-history').resolve())
        assert sha(name) == row['sha256']
        assert row['sha256'] not in set(plan['excluded_full_external_reference_sha256'])
        assert name not in extras or extras[name] == row
        extras[name] = row
    first['evidence_sha256'][plan['global_integrity']['file']] = plan['global_integrity']['sha256']
    provenance = retain(ROOT, BASELINE, MANIFEST, selection, extras, CONTENT_MAP)
    result = dict(status='explicit_current51_source_matched_selection_requires_fresh_aggregate_audit', created_at_utc=datetime.now(timezone.utc).isoformat(), baseline_selection=BASELINE, baseline_selection_sha256=BASELINE_SHA, actual_passing_baseline_audit=AUDIT, actual_passing_baseline_audit_sha256=sha(AUDIT), current_inventory=INVENTORY, current_inventory_sha256=INVENTORY_SHA, offers_sha256={r['offer']['file']:r['offer']['sha256'] for r in owners.values()}, independent_owner_mapping_peers=peers, global_integrity=plan['global_integrity']['file'], global_integrity_sha256=plan['global_integrity']['sha256'], proof_files=dict(sorted(selection.items())), proof_file_count=len(selection), new_file_count=len(new_sources), extra_frozen_inputs=extras, previous_frozen_input_content_binding=provenance, selection_plan=plan_name, selection_plan_sha256=sha(plan_name), deliberate_baseline_source_revisions={}, coverage_complete=False, limits=['All1113 baseline22 proof sources and original evidence remain exact. New source-matched actual standalone evidence requires a fresh frozen23 aggregate build, kernel replay and all-theorem axiom audit.', 'All34051 prior frozen input paths retain their exact original bytes by content fingerprints; retention records are historical provenance, not new executions.', 'Full external references are excluded from additional explicit inputs; any previously inherited audit bytes remain historical.'])
    with safe(DESTINATION).open('x') as output:
        output.write(json.dumps(result, indent=2) + '\n')
    return {'proofs':len(selection),'new':len(new_sources),'selection_sha256':sha(DESTINATION),'extra_inputs':len(extras),'content_map':provenance}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--plan', required=True, help='Immutable independently reviewed installed-owner production plan')
    args = parser.parse_args()
    print(json.dumps(prepare(args.plan)))

"""Prepare checkpoint26 with exact four-owner historical evidence aliases.

Unexecuted draft: actual Source53 and owner26 installation/global/peer evidence
are required by the immutable production plan; existence of drafts is insufficient.

The plan pins installed owner26 ledgers, actual builders, independent mapping
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
from retain_baseline_inputs26_v2 import retain, validate_owner_evidence_aliases, normalized_baseline_owner_evidence

ROOT = Path(__file__).resolve().parents[2]
INVENTORY = 'book/coverage/inventory-after-correction53.json'
BASELINE = 'reports/full-coverage/checkpoint-25-selection.json'
BASELINE_SHA = '3559445215b6b5b9bd176363ded8d307a93724b2b68c1ba9845dc709a3b4ddff'
MANIFEST = 'reports/full-coverage/checkpoint-25-manifest.json'
MANIFEST_SHA = '0329596719e09459730f34c9c84e9bacf4f3698a7c1699c4f848cef975ee5363'
AUDIT = 'reports/full-coverage/lean-checkpoint-25/verification-original.json'
AUDIT_SHA = 'bca548d253c7b0b81eecb271d74a47efb4114bc366225cd54ed59792e2c4d42c'
DESTINATION = 'reports/full-coverage/checkpoint-26-selection.json'
CONTENT_MAP = 'book/coverage/checks/frozen25-input-content-bindings26-v1.json'


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
            if snapshot_hash is None:
                # Retain unsupported historical absolute-input executions as
                # provenance, but do not treat them as canonical pair evidence.
                # An eligible canonical standalone plus named run is mandatory.
                continue
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
    assert plan['status'] == 'independently_reviewed_installed_owner26_selection_plan'
    INVENTORY_SHA = plan['inventory']['sha256']
    assert isinstance(INVENTORY_SHA, str) and re.fullmatch('[0-9a-f]{64}', INVENTORY_SHA)
    actual_source = checked(plan['actual_source53_apply'])
    application = checked(plan['actual_source53_application'])
    actual_exit_zero(actual_source)
    assert plan['actual_source53_application'] == {'file':'reports/full-coverage/source53-correction-application-v1.json','sha256':'fbc298db9520fb9eae49997fe7955062b1bb373605a3af81f40801fd317da548'}
    assert 'passed' in application['status'] and application['inventory_after'] == {'file':INVENTORY,'sha256':INVENTORY_SHA}
    assert INVENTORY_SHA == '4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
    assert application['selected25_proof_sources_unchanged'] == 1156 and application['five_installed25_owner_ledgers_unchanged'] is True
    assert application['source_after'] == {'file':'SafeLearning/lyapunov-mpc.html','sha256':'5e21c5319d41968468781ee0bf9b18aec5147666f764827f3a96e9e73d0138af'}
    assert sha(application['source_after']['file']) == application['source_after']['sha256']
    assert actual_source['helper_sha256_before'] == actual_source['helper_sha256_after'] == {'book/coverage/checks/root_apply_source53_v2.py':'20d5933637d720bdd263838f2af361425d4aa730e6ad33d721e61f5c625d481e'}
    exact(actual_source['helper_sha256_after'])
    source_logs = [actual_source[k] for k in ('log','raw_log') if k in actual_source]
    source_log_hashes = [actual_source[k] for k in ('log_sha256','raw_log_sha256') if k in actual_source]
    assert source_logs and source_log_hashes and all(h == source_log_hashes[0] for h in source_log_hashes)
    assert all(sha(n)==source_log_hashes[0] for n in source_logs)
    assert sha('SafeLearning/nn-in-the-loop.html') == '1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'
    assert plan['inventory'] == {'file': INVENTORY, 'sha256': INVENTORY_SHA}
    assert sha(INVENTORY) == sha('book/coverage/inventory.json') == INVENTORY_SHA
    assert not safe(DESTINATION).exists() and not safe(CONTENT_MAP).exists()
    assert plan['destination'] == DESTINATION and plan['content_map'] == CONTENT_MAP
    baseline = checked(plan['baseline_selection'])
    assert plan['baseline_selection'] == {'file': BASELINE, 'sha256': BASELINE_SHA}
    audit, manifest = checked(plan['baseline_audit']), checked(plan['baseline_manifest'])
    assert plan['baseline_audit'] == {'file': AUDIT, 'sha256': AUDIT_SHA}
    assert plan['baseline_manifest'] == {'file': MANIFEST, 'sha256': MANIFEST_SHA}
    assert audit['status'] == 'passed' and audit['proof_file_count'] == 1156 and audit['theorem_count'] == 9369
    assert all(row['exit_code'] == 0 for row in audit['checks'])
    assert len(baseline['proof_files']) == 1156
    assert audit['proof_sha256'] == {name: row['sha256'] for name, row in baseline['proof_files'].items()}
    assert manifest['status'] == 'formal_verification_passed_partial_coverage'
    assert len(manifest['frozen_inputs_sha256']) == 44111
    assert manifest['selection'] == BASELINE and manifest['selection_sha256'] == BASELINE_SHA
    exact(plan['helpers_sha256'])
    assert str(Path(__file__).relative_to(ROOT)) in plan['helpers_sha256']
    assert 'book/coverage/retain_baseline_inputs26_v2.py' in plan['helpers_sha256']
    authorization = plan['authorized_baseline_owner_evidence_aliases']
    aliases = validate_owner_evidence_aliases(ROOT, BASELINE, MANIFEST, authorization)
    selection = copy.deepcopy(baseline['proof_files'])
    for source, row in selection.items():
        assert sha(source) == row['sha256']
        original = copy.deepcopy(row)
        normalized, used = normalized_baseline_owner_evidence(original, aliases)
        if used:
            assert 'checkpoint26_original_baseline_owner_evidence' not in row
            row['evidence_sha256'] = normalized
            row['checkpoint26_original_baseline_owner_evidence'] = {
                'original_baseline_selection': {'file': BASELINE, 'sha256': BASELINE_SHA},
                'original_baseline_source': source, 'original_row_body': original,
                'authorized_original_path_aliases': used}
        exact(row['evidence_sha256'])
    first = selection[sorted(selection)[0]]
    first['evidence_sha256'].update({BASELINE: BASELINE_SHA, MANIFEST: sha(MANIFEST), AUDIT: sha(AUDIT), plan_name: sha(plan_name)})
    for historical in plan['prior_checkpoint25_selection_provenance'].values():
        assert set(historical) == {'file', 'sha256'} and sha(historical['file']) == historical['sha256']
        first['evidence_sha256'][historical['file']] = historical['sha256']
    preparation_helper = plan['baseline_owner_evidence_alias_plan_preparation_helper']
    assert set(preparation_helper) == {'file', 'sha256'} and sha(preparation_helper['file']) == preparation_helper['sha256']
    first['evidence_sha256'][preparation_helper['file']] = preparation_helper['sha256']
    for path in (ROOT / 'reports/full-coverage/lean-checkpoint-25').rglob('*'):
        if path.is_file():
            name = str(path.relative_to(ROOT))
            first['evidence_sha256'][name] = sha(name)
    first['checkpoint26_inherited_snapshot_provenance_scope'] = 'Every frozen25 original path and byte hash is retained by the exact content binding map. Original audits, commands and times remain historical.'
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
    assert len(selection) == 1156 + len(new_sources)
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
    provenance = retain(ROOT, BASELINE, MANIFEST, selection, extras, CONTENT_MAP, authorization)
    result = dict(status='explicit_current53_source_matched_selection_requires_fresh_aggregate_audit', created_at_utc=datetime.now(timezone.utc).isoformat(), baseline_selection=BASELINE, baseline_selection_sha256=BASELINE_SHA, actual_passing_baseline_audit=AUDIT, actual_passing_baseline_audit_sha256=sha(AUDIT), current_inventory=INVENTORY, current_inventory_sha256=INVENTORY_SHA, offers_sha256={r['offer']['file']:r['offer']['sha256'] for r in owners.values()}, independent_owner_mapping_peers=peers, global_integrity=plan['global_integrity']['file'], global_integrity_sha256=plan['global_integrity']['sha256'], proof_files=dict(sorted(selection.items())), proof_file_count=len(selection), new_file_count=len(new_sources), extra_frozen_inputs=extras, previous_frozen_input_content_binding=provenance, selection_plan=plan_name, selection_plan_sha256=sha(plan_name), deliberate_baseline_source_revisions={}, coverage_complete=False, limits=['All1156 baseline25 proof sources and original evidence remain exact. New source-matched actual standalone evidence requires a fresh frozen26 aggregate build, kernel replay and all-theorem axiom audit.', 'All44111 prior frozen input paths retain their exact original bytes by content fingerprints; retention records are historical provenance, not new executions.', 'Full external references are excluded from additional explicit inputs; any previously inherited audit bytes remain historical.'])
    with safe(DESTINATION).open('x') as output:
        output.write(json.dumps(result, indent=2) + '\n')
    return {'proofs':len(selection),'new':len(new_sources),'selection_sha256':sha(DESTINATION),'extra_inputs':len(extras),'content_map':provenance}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--plan', required=True, help='Immutable independently reviewed installed-owner production plan')
    args = parser.parse_args()
    print(json.dumps(prepare(args.plan)))

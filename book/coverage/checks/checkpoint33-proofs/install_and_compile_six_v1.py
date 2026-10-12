"""Install exact reviewed bytes and record twelve fresh compiler commands.

Only the six new canonical files and this packet are written. Existing source,
native and peer evidence remains at its original exact reference; no prior tree
or build cache is copied. Source qualifications and owner promotions are separate.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
BASE = Path(__file__).resolve().parent
INDEX = 'book/coverage/checks/recovery32/next-batch-source-qualification-index-v1.json'
SELECTION = 'reports/full-coverage/checkpoint-32-selection.json'
SELECTION_SHA = 'c45d7f80ed33c780af30bdf58792bd5fa24cb0019a4e3b05a821520f9d703bb4'
CANONICAL_STEMS = [
    'CompleteFoundationsRegularNewtonAndRateInterpretation33',
    'CompleteFoundationsCommonMixedInducedNormFormulas33',
    'CompleteFoundationsBoxImageZonotope33',
    'CompleteFoundationsCubeRadiusAndNetMargin33',
    'CompleteFoundationsSignedDistanceHausdorff33',
    'CompleteFoundationsPositiveSubunitPNorm33',
]

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def path(n):
    p = Path(n)
    return p if p.is_absolute() else ROOT / p

def ref(p):
    p = path(p) if isinstance(p, str) else p
    return {'file': str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),
            'sha256': sha(p), 'bytes': p.stat().st_size}

def checked(r):
    p = path(r['file'])
    assert p.is_file() and not p.is_symlink(), str(p)
    assert sha(p) == r['sha256'], str(p)
    if 'bytes' in r:
        assert p.stat().st_size == r['bytes'], str(p)
    return p

def read(r):
    return json.loads(checked(r).read_bytes())

def new(p, data):
    assert not p.exists(), str(p)
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f:
        f.write(data)
        f.flush()
    p.chmod(0o444)

def write_json(p, data):
    new(p, (json.dumps(data, indent=2) + '\n').encode())

def source_binding(d, h):
    if isinstance(d, dict):
        return d.get('sha256') == h or any(source_binding(v, h) for v in d.values())
    if isinstance(d, list):
        return any(source_binding(v, h) for v in d)
    return d == h

def main():
    helper = ref(Path(__file__))
    selection_ref = {'file': SELECTION, 'sha256': SELECTION_SHA}
    selection = read(selection_ref)
    index_ref = ref(INDEX)
    index = read(index_ref)
    assert index['current_checkpoint']['selection']['sha256'] == SELECTION_SHA
    selected = {n: r['sha256'] for n, r in selection['proof_files'].items()}
    assert len(selected) == 1254
    names_path = ROOT / 'book/coverage/lean_names.py'
    names_ref = ref(names_path)
    spec = importlib.util.spec_from_file_location('checkpoint33_lean_names', names_path)
    names = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(names)
    selected_names = set()
    for n, h in selected.items():
        p = checked({'file': n, 'sha256': h})
        selected_names.update(r['name'] for r in names.declarations(p.read_text()))
    assert len(selected_names) == index['source81_identity_crosscheck']['selected_public_name_count_inspected']
    originals = {index_ref['file']: index_ref['sha256'],
                 selection_ref['file']: selection_ref['sha256'],
                 helper['file']: helper['sha256'], names_ref['file']: names_ref['sha256']}
    project = ROOT / 'verification/lean'
    project_refs = [ref(project / n) for n in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']]
    for r in project_refs:
        originals[r['file']] = r['sha256']
    rows = []
    new_names = set()
    for f, stem in zip(index['ready_for_exact_source_qualification'], CANONICAL_STEMS, strict=True):
        source = checked(f['source'])
        text = source.read_text()
        declarations = names.declarations(text)
        theorem_count = sum(d['kind'] in {'theorem', 'lemma'} for d in declarations)
        assert theorem_count == f['theorems'] and len(declarations) == f['public_names']
        public_names = {d['name'] for d in declarations}
        assert len(public_names) == len(declarations)
        assert not public_names.intersection(selected_names | new_names)
        new_names.update(public_names)
        assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b', names.without_comments(text))
        assert all(d['name'].startswith(tuple(n + '.' for n in f['original_namespaces'])) for d in declarations)
        imports = re.findall(r'^import (SafeLearning\.[A-Za-z0-9_]+)\s*$', text, re.M)
        assert all('verification/lean/' + n.replace('.', '/') + '.lean' in selected for n in imports)
        canonical = 'verification/lean/SafeLearning/' + stem + '.lean'
        assert not (ROOT / canonical).exists()
        checked_artifacts = set()
        for k in ['source', 'author_request', 'whole_prospective_peer', 'narrow_wording_and_parser_peer', 'exact_proposal']:
            r = f[k]
            checked(r)
            originals[r['file']] = r['sha256']
        for k in ['whole_prospective_peer', 'narrow_wording_and_parser_peer']:
            peer = read(f[k])
            assert peer['status'].startswith('passed_') and peer.get('errors', []) == []
            assert peer.get('protection_errors', []) == []
            assert source_binding(peer, f['source']['sha256'])
            for n, h in peer['required_evidence_artifacts_sha256'].items():
                checked({'file': n, 'sha256': h})
                originals[n] = h
                checked_artifacts.add(n)
        whole = read(f['whole_prospective_peer'])
        decisions = whole.get('whole_unit_decisions', whole.get('prospective_whole_decisions'))
        assert set(decisions) == {r['key'] for r in f['conditionally_approved_whole_material']}
        for decision in decisions.values():
            assert decision.get('prospective_whole_semantic_approved', decision.get('whole_semantic_approved')) is True
            assert decision.get('prospective_missing_requirements', decision.get('missing_requirements')) == []
        native_closure = []
        for original in f['actual_source_and_axiom_natives']:
            native = read(original['record'])
            assert native['actual_exit_code'] == native['actual_runner_exit_code'] == 0
            assert native['protection_errors'] == [] and native['source_unchanged'] is True
            assert native['source_sha256_before'] == native['source_sha256_after'] == native['source_snapshot_sha256']
            if original['role'] == 'final_actual_source':
                assert native['source_sha256_before'] == f['source']['sha256']
            closure = {'role': original['role'], 'original_record': original['record']}
            originals[original['record']['file']] = original['record']['sha256']
            for key, hash_key in [('source_snapshot', 'source_snapshot_sha256'), ('raw_log', 'raw_log_sha256')]:
                rr = {'file': native[key], 'sha256': native[hash_key]}
                checked(rr)
                originals[rr['file']] = rr['sha256']
                closure[key] = rr
            native_closure.append(closure)
        rows.append({'family': f['family'], 'canonical_source': canonical,
                     'original_tmp_source': f['source'], 'original_namespaces': f['original_namespaces'],
                     'public_declarations': declarations, 'public_theorem_count': theorem_count,
                     'public_name_count': len(declarations),
                     'original_actual_source_and_axiom_natives': native_closure,
                     'independent_source_peers': [f['whole_prospective_peer']],
                     'independent_narrow_wording_and_parser_peer': f['narrow_wording_and_parser_peer'],
                     'original_author_request': f['author_request'], 'exact_proposal': f['exact_proposal'],
                     'checked_peer_required_artifact_count': len(checked_artifacts),
                     'conditionally_approved_whole_material': f['conditionally_approved_whole_material'],
                     'whole_qualification_still_requires_exact_source_application': True,
                     'additional_scope_limits': f['additional_scope_limits']})
    assert len(rows) == 6 and len(new_names) == 83
    assert sum(r['public_theorem_count'] for r in rows) == 71
    protected_digest = hashlib.sha256(json.dumps(selected, sort_keys=True).encode()).hexdigest()
    snapshots = {}
    def guard():
        for n, h in {**selected, **originals}.items():
            assert sha(path(n)) == h, n
        for n, rr in snapshots.items():
            assert sha(ROOT / n) == rr['sha256'], n
            checked(rr)
    guard()
    plan = {'status': 'exact_reviewed_six_new_canonical33_plan', 'created_at_utc': datetime.now(timezone.utc).isoformat(),
            'baseline_selection': selection_ref, 'continuation_index': index_ref, 'compiler_recorder': helper,
            'declaration_parser': names_ref, 'project_configuration': project_refs,
            'selected32_protected_source_count': len(selected), 'selected32_protected_source_map_sha256': protected_digest,
            'selected32_public_name_count': len(selected_names), 'new_selected_name_overlap': [],
            'sources': rows, 'source_count': 6, 'public_theorem_count': 71, 'public_name_count': 83,
            'checked_original_evidence_count': len(originals),
            'checked_original_evidence_sha256': originals,
            'coverage_complete': False, 'source_owner_selection_aggregate_publication_changes_claimed': False}
    write_json(BASE / 'exact-reviewed-six-canonical33-plan-v1.json', plan)
    for row in rows:
        canonical = ROOT / row['canonical_source']
        data = checked(row['original_tmp_source']).read_bytes()
        new(canonical, data)
        snapshot = BASE / 'source-snapshots' / canonical.name
        new(snapshot, data)
        snapshots[row['canonical_source']] = ref(snapshot)
    guard()
    pairs = []
    for row in rows:
        name = Path(row['canonical_source']).stem
        for kind in ['standalone', 'named']:
            guard()
            command = ['lake', 'env', 'lean', 'SafeLearning/' + name + '.lean'] if kind == 'standalone' else ['lake', 'build', 'SafeLearning.' + name]
            log = BASE / (name + '-' + kind + '-actual-v1.log')
            receipt = BASE / (name + '-' + kind + '-actual-v1.json')
            source = ROOT / row['canonical_source']
            source_before = sha(source)
            started = datetime.now(timezone.utc).isoformat()
            start = time.monotonic()
            with log.open('xb') as raw:
                result = subprocess.run(command, cwd=project, stdout=raw, stderr=subprocess.STDOUT, check=False)
            elapsed = time.monotonic() - start
            finished = datetime.now(timezone.utc).isoformat()
            log.chmod(0o444)
            source_after = sha(source)
            record = {'status': 'passed' if result.returncode == 0 else 'failed', 'kind': kind,
                      'command': command, 'actual_command': command, 'actual_workdir': str(project),
                      'exit_code': result.returncode, 'actual_exit_code': result.returncode,
                      'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': elapsed,
                      'source': row['canonical_source'], 'source_sha256_before': source_before,
                      'source_sha256_after': source_after, 'source_snapshot': snapshots[row['canonical_source']],
                      'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
                      'compiler_recorder': helper, 'compiler_recorder_sha256_after': sha(Path(__file__)),
                      'baseline_selection': selection_ref, 'source_unchanged': source_before == source_after,
                      'immutable_actual_command_record_no_relabeling': True,
                      'coverage_complete': False}
            write_json(receipt, record)
            guard()
            assert result.returncode == 0, str(receipt)
            pairs.append({'kind': kind, 'source': ref(source), 'actual_record': ref(receipt),
                          'raw_log': ref(log), 'source_snapshot': snapshots[row['canonical_source']],
                          'actual_exit_code': result.returncode})
            print(json.dumps({'completed_actual_commands': len(pairs), 'source': name, 'kind': kind,
                              'actual_exit_code': result.returncode}), flush=True)
    guard()
    report = {'status': 'passed_actual_reviewed33_canonical_standalone_and_named_pairs_unselected', 'errors': [],
              'completed_at_utc': datetime.now(timezone.utc).isoformat(), 'source_count': 6,
              'public_theorem_count': 71, 'public_name_count': 83, 'actual_compiler_command_count': len(pairs),
              'sources': rows, 'actual_paired_records': pairs, 'source_snapshots': snapshots,
              'original_evidence_retained_by_exact_references': True,
              'plan': ref(BASE / 'exact-reviewed-six-canonical33-plan-v1.json'),
              'compiler_recorder': helper, 'baseline_selection': selection_ref,
              'selected32_source_and_public_name_protection_passed': True,
              'selected32_protected_source_count': len(selected), 'selected32_public_name_count': len(selected_names),
              'selected32_protected_source_map_sha256': protected_digest,
              'exact_qualifiers_owner_promotion_and_aggregate_still_separate': True,
              'coverage_complete': False, 'selection_aggregate_owner_or_publication_claimed': False,
              'prior_snapshot_tree_or_build_cache_copied': False}
    target = BASE / 'actual-reviewed33-canonical-paired-readiness-v1.json'
    write_json(target, report)
    print(json.dumps({'status': report['status'], 'readiness': ref(target), 'sources': 6,
                      'actual_commands': len(pairs), 'public_theorems': 71, 'coverage_complete': False}), flush=True)

if __name__ == '__main__':
    main()

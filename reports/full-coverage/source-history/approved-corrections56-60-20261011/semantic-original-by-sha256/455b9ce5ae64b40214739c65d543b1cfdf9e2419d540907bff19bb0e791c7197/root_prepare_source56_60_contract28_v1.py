"""Read-only source55 validation and exact cumulative full29 parser contract."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, importlib.util, json

ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = Path('/tmp/root-source56-60-full29-application-contract28-v1.json')
spec = importlib.util.spec_from_file_location('original_source_parser_guards', ROOT/'book/coverage/checks/root_apply_source54_55_v3.py')
base = importlib.util.module_from_spec(spec); spec.loader.exec_module(base)
sha, read = base.sha, base.read

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source60', required=True)
    parser.add_argument('--source60-sha256', required=True)
    args = parser.parse_args()
    assert not OUT.exists()
    assert sha(ROOT/'book/coverage/inventory.json') == '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
    assert sha(ROOT/'book/coverage/material-corrections.json') == '21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'
    rows = [
        (56, '/tmp/root-mpc-explicit-adopted-domain-source56-proposal-v2/root-mpc-explicit-adopted-domain-source56-proposal-v2.json', 'eb7c2fa86943afc11f6b199fb4946bcd8d9b6f796ceb89afab0e541e92e6e837'),
        (57, '/tmp/probability-trajectory-inputs-source56-proposal27-v1/probability-trajectory-inputs-source56-proposal27-v1.json', '261ac857ae9e1fb16255e9b4bfed146d30fe54b087c24c14c100cb0ffdfda727'),
        (58, '/tmp/modules-ibp-zero-sign-source58-proposal28-v1/modules-ibp-zero-sign-source58-proposal28-v1.json', '7505b1d64cb9b3a55be0001ac7dff8379f3bc35b15606a41fb010c20ead4cc3b'),
        (59, '/tmp/modules-physical-sensor-source59-proposal28-v2/modules-physical-sensor-source59-proposal28-v2.json', '39eae6e09e69a9e9fd5b7165dced786137445336213cf90b5880eceeea8acfd3'),
        (60, args.source60, args.source60_sha256),
    ]
    candidates, steps = {}, []
    previous = read(ROOT/'book/coverage/inventory.json')
    from sys import path
    path.insert(0, str(ROOT/'book'))
    from validate import Document
    for num, n, h in rows:
        p = Path(n); assert p.is_absolute() and p.is_relative_to('/tmp') and not p.is_symlink() and sha(p) == h
        d = read(p)
        source_ref = d.get('source', d.get('current_source'))
        if num == 60:
            source_ref = d['base_source56_candidate']
            source = 'SafeLearning/lyapunov-mpc.html'
        else:
            source = Path(source_ref['file'])
            source = source.relative_to(ROOT).as_posix() if source.is_absolute() else source.as_posix()
        original = candidates.get(source, (ROOT/source).read_bytes()).decode()
        assert hashlib.sha256(original.encode()).hexdigest() == source_ref['sha256']
        replacements = d['raw_replacements'] if 'raw_replacements' in d else [{'before': d['before_raw_fragment'], 'after': d['after_raw_fragment']}]
        new = original
        for r in replacements:
            assert new.count(r['before']) == 1 and r['after'] not in new
            new = new.replace(r['before'], r['after'], 1)
        candidate = d['proposed_source']; assert sha(Path(candidate['file'])) == candidate['sha256']
        assert new.encode() == Path(candidate['file']).read_bytes() and new.count('\n') == original.count('\n')
        reverse = new
        for r in reversed(replacements):
            assert reverse.count(r['after']) == 1
            reverse = reverse.replace(r['after'], r['before'], 1)
        assert reverse == original
        assert [(n.tag,n.attrs,n.line) for n in Document(original).nodes] == [(n.tag,n.attrs,n.line) for n in Document(new).nodes]
        changed = d.get('actual_fresh_parser_changed_text_keys', d.get('fresh_parser_changed_text_keys'))
        step = {'correction_id': num, 'proposal': {'file': n, 'sha256': h}, 'source': source,
                'source_sha256_before': hashlib.sha256(original.encode()).hexdigest(), 'candidate': candidate,
                'exact_replacements': replacements, 'exact_changed_text_keys': changed, 'counts': previous['counts']}
        candidates[source] = new.encode()
        data, following = base.full_parser(candidates)
        base.inventory_diff(previous, following, step)
        step['actual_fresh_isolated_full29_inventory_sha256'] = hashlib.sha256(data).hexdigest()
        steps.append(step); previous = following
    record = {'status': 'prepared_exact_cumulative_source56_to60_full29_application_contract_only',
              'prepared_at_utc': datetime.now(timezone.utc).isoformat(), 'helper_sha256': sha(Path(__file__)),
              'before_inventory': {'file': 'book/coverage/inventory.json', 'sha256': sha(ROOT/'book/coverage/inventory.json')},
              'before_corrections': {'file': 'book/coverage/material-corrections.json', 'sha256': sha(ROOT/'book/coverage/material-corrections.json')},
              'steps': steps, 'final_page_sources_sha256': previous['source_sha256'],
              'both_parser_ROOT_and_OUT_isolated': True, 'all556_exercises_and12774_material_shapes_preserved': True,
              'source_owner_proof_or_coverage_write_claimed': False, 'coverage_complete': False}
    with OUT.open('x') as f:
        f.write(json.dumps(record, indent=2)+'\n')
    assert sha(ROOT/'book/coverage/inventory.json') == record['before_inventory']['sha256']
    assert sha(ROOT/'book/coverage/material-corrections.json') == record['before_corrections']['sha256']
    print(json.dumps({'contract': str(OUT), 'sha256': sha(OUT), 'steps': [r['correction_id'] for r in steps]}))

if __name__ == '__main__':
    main()

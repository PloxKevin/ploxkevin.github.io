"""Synchronize five approved literal substitutions into three authoring fragments.

The actual Source79 integrated pages stay unchanged. Entire original fragment
bytes are preserved before optional writes; no mathematical scope is expanded.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, re

ROOT = Path(__file__).resolve().parents[3]
CONTEXT = Path('/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json')
CONTEXT_SHA = 'd06f4ef21178b787db693df28ca5ae01386728915e0596cba5fd17f000db0737'
SUPPLY = Path('/tmp/modules-seven-unnumbered-qualifiers-root-offer30-v1.json')
SUPPLY_SHA = '5df8cb07cdf76e4997f80b57d1c4aeabf1402fbf4530cc724356ff2465fadca7'
HISTORY = ROOT / 'reports/full-coverage/source-history/source79-three-authoring-fragment-sync-v1'
RESULT = ROOT / 'reports/full-coverage/source79-authoring-fragments-sync-v1.json'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def output(p):
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(ROOT))
    assert not p.exists()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--apply', action='store_true')
    args = ap.parse_args()
    assert sha(CONTEXT) == CONTEXT_SHA and sha(SUPPLY) == SUPPLY_SHA
    context = json.loads(CONTEXT.read_bytes())
    def guard():
        assert sha(CONTEXT) == CONTEXT_SHA and sha(SUPPLY) == SUPPLY_SHA
        for table in ['pins_sha256', 'held_current_source_sha256', 'owners_sha256']:
            for n, h in context[table].items():
                p = ROOT / n
                assert p.is_file() and not p.is_symlink() and sha(p) == h, n
    guard()
    supply = json.loads(SUPPLY.read_bytes())
    proposals = {r['id']: r for r in supply['individual_unnumbered_proposals']}
    selected = [('delayed_roots', 'nn-in-the-loop.html'),
                ('GP_calibration_discrepancy', 'toolkit-gp.html'),
                ('thermal_sharp_threshold', 'viability.html')]
    edits = []
    for key, name in selected:
        proposal = proposals[key]
        path = ROOT / 'book/chapters' / name
        assert path.is_file() and not path.is_symlink()
        before = path.read_bytes()
        original = before.decode()
        text = original
        replacements = proposal['exact_replacements']
        for r in replacements:
            assert text.count(r['before']) == 1 and r['after'] not in text
            text = text.replace(r['before'], r['after'], 1)
        inverse = text
        for r in reversed(replacements):
            assert inverse.count(r['after']) == 1
            inverse = inverse.replace(r['after'], r['before'], 1)
        assert inverse == original and text.count('\n') == original.count('\n')
        page = (ROOT / 'SafeLearning' / name).read_text()
        blocks = re.findall(r'<!-- BOOK APPLICATION START -->\n(.*?)\n<!-- BOOK APPLICATION END -->', page, re.S)
        assert len(blocks) == 1 and blocks[0] == text.strip()
        edits.append((path, before, text.encode(), key, replacements))
    assert sum(len(r[4]) for r in edits) == 5
    output(HISTORY)
    output(RESULT)
    for path, _, _, _, _ in edits:
        output(HISTORY / path.name)
    guard()
    summary = [{'source': str(p.relative_to(ROOT)), 'before_sha256': hashlib.sha256(old).hexdigest(),
                'after_sha256': hashlib.sha256(new).hexdigest(), 'approved_proposal_id': key,
                'replacements': rs} for p, old, new, key, rs in edits]
    if not args.apply:
        print(json.dumps({'status': 'passed_readonly_five_reviewed_fragment_substitution_preflight',
                          'fragments': summary, 'integrated_pages_unchanged': True}))
        return
    HISTORY.mkdir(parents=True)
    for path, old, new, _, _ in edits:
        assert path.read_bytes() == old
        with (HISTORY / path.name).open('xb') as f:
            f.write(old)
        path.write_bytes(new)
    guard()
    assert all(p.read_bytes() == new and (HISTORY / p.name).read_bytes() == old for p, old, new, _, _ in edits)
    record = {'status': 'passed_actual_five_reviewed_source79_substitutions_synchronized_to_three_authoring_fragments',
              'applied_at_utc': datetime.now(timezone.utc).isoformat(), 'fragments': summary,
              'original_fragment_directory': str(HISTORY.relative_to(ROOT)),
              'supply': {'file': str(SUPPLY), 'sha256': SUPPLY_SHA},
              'integrated31_assets_and_old1197_proofs_and_historical29_raw5_unchanged': True,
              'coverage_complete': False}
    with RESULT.open('x') as f:
        f.write(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'status': record['status'], 'result': str(RESULT.relative_to(ROOT)),
                      'result_sha256': sha(RESULT), 'fragments': 3, 'substitutions': 5}))


if __name__ == '__main__':
    main()

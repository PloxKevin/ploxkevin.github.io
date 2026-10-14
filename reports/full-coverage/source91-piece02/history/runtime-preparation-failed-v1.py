"""Freeze the previous selected runtime plus the reviewed part-(ii) bridge.

Only explicit previous audit inputs are selected. Preparation records identities;
it grants no source correspondence, kernel-audit or completion credit.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as h

BASE = 'reports/full-coverage/runtime-source91-piece01-v1'
AUDIT = BASE + '/reports/lean-verification/verification.json'
AUDIT_SHA = '55c37b0078fffcadd1d64453a3490a01b167d3c412cac53e525493543fe898de'
RUNTIME = 'reports/full-coverage/runtime-source91-piece02-v1'
REVIEW = 'reports/full-coverage/source91-piece02/landscape-ar-part-ii-new-bridge-independent-amendment-v1.json'
NEW = 'verification/lean/SafeLearning/CompleteModulesLandscapeSource91ARPartII.lean'
SELF = 'book/coverage/source91-piece02/prepare_runtime.py'
REPORT = 'book/coverage/source91-piece02/runtime-preparation-v1.json'


def main():
    assert h.ref(AUDIT)['sha256'] == AUDIT_SHA
    prior, review = h.read(AUDIT), h.read(REVIEW)
    assert prior['status'] == 'passed'
    assert prior['proof_file_count'] == 1271 and prior['theorem_count'] == 11508
    assert review['binding_errors'] == [] and review['errors_in_mathematical_bodies'] == []
    assert review['current_named_build_passed_at_review']
    assert review['new_proof_source'] == h.ref(NEW)
    selected = dict(prior['proof_sha256'])
    assert NEW not in selected
    selected[NEW] = h.ref(NEW)['sha256']
    assert len(selected) == 1272
    expected = {**prior['proof_sha256'], **prior['source_sha256'], **prior['project_sha256']}
    expected['book/coverage/lean_names.py'] = h.ref(BASE + '/book/coverage/lean_names.py')['sha256']
    assert len(prior['source_sha256']) == 31
    inputs = {AUDIT: AUDIT_SHA, REVIEW: h.ref(REVIEW)['sha256'], SELF: h.ref(SELF)['sha256'],
              NEW: selected[NEW]}
    sources = []
    for name, digest in sorted(expected.items()):
        if name == 'verification/lean/SafeLearning.lean':
            continue
        origin = BASE + '/' + name
        assert h.ref(origin)['sha256'] == digest, origin
        inputs[origin] = digest
        target = RUNTIME + '/' + name
        p = h.path(target, writable=True)
        p.parent.mkdir(parents=True, exist_ok=True)
        if p.exists():
            assert h.ref(target)['sha256'] == digest
        else:
            # Frozen sources are shared. No build cache or archive is copied.
            os.link(h.path(origin), p)
        sources.append({'file': name, 'sha256': digest, 'origin': h.ref(origin)})
    h.put(RUNTIME + '/' + NEW, h.path(NEW).read_bytes())
    sources.append({'file': NEW, 'sha256': selected[NEW], 'origin': h.ref(NEW)})
    aggregate = ('\n'.join('import SafeLearning.' + Path(n).stem for n in sorted(selected)) + '\n').encode()
    h.put(RUNTIME + '/verification/lean/SafeLearning.lean', aggregate)
    for part in ['build', 'packages']:
        destination = ROOT / RUNTIME / 'verification/lean/.lake' / part
        origin = ROOT / 'verification/lean/.lake' / part
        assert origin.is_dir()
        destination.parent.mkdir(parents=True, exist_ok=True)
        if destination.is_symlink():
            assert destination.resolve() == origin.resolve()
        else:
            assert not destination.exists()
            destination.symlink_to(origin.resolve(), target_is_directory=True)
    assert {p.name for p in (ROOT / RUNTIME / 'verification/lean/SafeLearning').iterdir()} == {
        Path(n).name for n in selected}
    assert all(h.ref(name)['sha256'] == digest for name, digest in inputs.items())
    report = {'status': 'prepared_selected1272_source91_piece02_no_completion_credit',
              'runtime': RUNTIME, 'previous_audit': h.ref(AUDIT), 'independent_bridge_review': h.ref(REVIEW),
              'proof_files': 1272, 'expected_theorems': 11522, 'new_proof': h.ref(NEW),
              'selected_proof_sha256': selected, 'site_sha256': prior['source_sha256'],
              'aggregate': h.ref(RUNTIME + '/verification/lean/SafeLearning.lean'),
              'sources': sources, 'protected_input_sha256': inputs,
              'cache_mode': 'symlinks_to_existing_pinned_cache_no_copy',
              'formal_completion_credit': 0, 'helper': h.ref(SELF)}
    h.json_put(REPORT, report)
    print(json.dumps({'status': report['status'], 'report': h.ref(REPORT)}))


if __name__ == '__main__':
    main()

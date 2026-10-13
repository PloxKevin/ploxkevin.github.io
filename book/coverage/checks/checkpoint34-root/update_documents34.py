"""Record verified checkpoint34 and preserve checkpoint33 documents exactly."""
from datetime import datetime, timezone
import argparse
import json

from install_owners34 import ROOT, path, sha, ref, read, exact, atomic, encode

HISTORY = 'reports/full-coverage/source-history/documentation33-before-checkpoint34-v1'
OUT = 'reports/full-coverage/documentation34-local-verification-v1.json'
VISUAL = 'book/coverage/checks/checkpoint34-review/browser34-source90-independent-visual-and-functional-closure-v1.json'
DOCUMENTS = ['README.md', 'book/README.md', 'verification/lean/README.md',
    'reports/full-coverage/README.md', 'book/coverage/progress.json', 'book/coverage/CONTINUATION.md', '_config.yml']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--visual-review-sha256', required=True)
    args = parser.parse_args()
    assert sha(VISUAL) == args.visual_review_sha256
    visual = read(VISUAL)
    assert visual['status'].startswith('passed') and visual['errors'] == []
    manifest = read('reports/full-coverage/checkpoint-34-manifest.json')
    assert manifest['status'] == 'formal_verification_passed_partial_coverage'
    audit = json.loads(exact({'file': manifest['successful_verification']['report'], 'sha256': manifest['successful_verification']['report_sha256']}).read_bytes())
    assert audit['status'] == 'passed' and audit['proof_file_count'] == 1264 and audit['theorem_count'] == 11459
    ledger = read('reports/full-coverage/ledger34-working-v1.json')
    assert ledger['integrity_status'] == 'passed' and ledger['counts']['material_review_statuses'] == {'reviewed': 4858, 'pending': 7916}
    for row in visual['full_changed_page_reports']:
        report = json.loads(exact(row['report']).read_bytes())
        assert len(report) == 1 and report[0]['status'] == 'passed' and report[0]['errors'] == []
        assert row['source_sha256'] == report[0]['source_sha256'] == audit['source_sha256']['SafeLearning/' + row['actual_page']]
    if path(OUT).exists():
        record = read(OUT)
        assert record['manifest'] == ref('reports/full-coverage/checkpoint-34-manifest.json')
        assert all(sha(n) == h for n, h in record['document_sha256'].items())
        print(json.dumps({'status': 'passed_existing_exact_checkpoint34_documents', 'record': ref(OUT)}))
        return
    originals = {}
    for name in DOCUMENTS:
        target = HISTORY + '/' + name
        if not path(target).exists():
            atomic(target, path(name).read_bytes())
        originals[name] = ref(target)
    old = read(HISTORY + '/book/coverage/progress.json')
    assert old['verified_checkpoint']['checkpoint'] == 33
    progress = old.copy()
    progress['previous_checkpoint33_delivery'] = dict(entire_original_progress=originals['book/coverage/progress.json'],
        content_commit=old['last_published_content_commit'], metadata_commit=old['last_published_metadata_commit'],
        actual_delivery_closure=old['live_delivery_evidence']['actual_delivery_closure'])
    progress['inventory_sha256'] = manifest['inventory_sha256']
    progress['current_documented_material_corrections'] = 90
    progress['verified_checkpoint'] = dict(checkpoint=34, proof_files=1264, theorems=11459, status='passed', coverage_complete=False,
        report=manifest['successful_verification']['report'], actual_audit_workdir=manifest['successful_verification']['actual_workdir'],
        actual_execution=ref('reports/full-coverage/verify-runtime34-execution-v1.json'), fresh_kernel_files=3, exact_prior_kernel_reuses=1261)
    progress['working_coverage_report'] = 'reports/full-coverage/ledger34-working-v1.json'
    progress['current_published_ledger_candidate'] = 'reports/full-coverage/ledger34-frozen-source-only-v1.json'
    progress['current_frozen_audit'] = dict(snapshot=manifest['snapshot'], source_only=True, proof_files=1264,
        status='source_exact_mirror_of_actual_runtime_audit', snapshot_execution_claimed=False, manifest=ref('reports/full-coverage/checkpoint-34-manifest.json'))
    progress['publication_status'] = 'checkpoint34_locally_verified_content_delivery_pending'
    progress['live_delivery_status'] = 'checkpoint33_delivery_confirmed_checkpoint34_delivery_pending'
    progress['working_next_checkpoint_preparation'] = dict(status='checkpoint34_locally_verified_full_coverage_objective_unfinished',
        inventory='book/coverage/inventory.json', inventory_sha256=manifest['inventory_sha256'],
        exercise_counts=dict(complete=538, partial=7, pending=11), material_review_units=dict(reviewed=4858, pending=7916),
        owner34_integration=ref('reports/full-coverage/owner34-integration-v1.json'),
        independent_owner_review=ref('book/coverage/checks/checkpoint34-review/independent-four-owner34-candidates-review-v3.json'),
        visual_and_functional_review=ref(VISUAL), source34_application=ref('reports/full-coverage/checkpoint34-source-corrections89-90-v1.json'),
        canonical_sources_selected=True, source_qualifiers_or_owner_promotion34_performed=True,
        aggregate_kernel_axiom_or_delivery34_claimed='actual_aggregate_kernel_and_standard_axiom_audit_passed_delivery_pending',
        coverage_complete=False)
    remaining, owners = [], {}
    for domain in ['foundations', 'applied', 'modules', 'core']:
        name = 'book/coverage/' + domain + '.json'
        owners[name] = sha(name)
        for exercise in read(name)['exercises']:
            if exercise['status'] != 'complete_math':
                remaining.append(dict(owner=domain, inventory_key=exercise['inventory_key'], label=exercise['label'], status=exercise['status'],
                    pending_claims=[c for c in exercise['claims'] if c['status'] != 'proved']))
    assert len(remaining) == 18
    remaining_name = 'book/coverage/remaining-exercises34.json'
    if not path(remaining_name).exists():
        atomic(remaining_name, encode(dict(generated_at_utc=datetime.now(timezone.utc).isoformat(), checkpoint=34,
            owner_sha256=owners, exercises=remaining, coverage_complete=False,
            scope='Current incomplete exercises and their unproved claims. Historical reviews remain unchanged.')))
    else:
        assert read(remaining_name)['owner_sha256'] == owners and read(remaining_name)['exercises'] == remaining
    atomic('book/coverage/progress.json', encode(progress))
    for name in ['README.md', 'book/README.md', 'verification/lean/README.md']:
        text = path(HISTORY + '/' + name).read_text()
        text = text.replace('11,345', '11,459').replace('1,261', '1,264').replace('7,923', '7,916')
        if name == 'README.md':
            marker = 'The [continuing coverage audit]'
            assert text.count(marker) == 1
            text = text[:text.index(marker)] + '''The [continuing coverage audit](reports/full-coverage/README.md) now verifies
11,459 theorems in 1,264 selected Lean files. Of 556 exercises, 538 are complete,
7 partial and 11 pending; 7,916 overlapping teaching-material units remain
pending. Checkpoint 34 is verified locally and awaits delivery. It adds three
proof files, 114 theorems, two complete exercises and seven reviewed material
units. Its current delivery status is in [the progress ledger](book/coverage/progress.json).
The [continuation note](book/coverage/CONTINUATION.md) lists the remaining work.
Browser reports identify the exact site bytes they checked.
'''
        elif name == 'book/README.md':
            text = text.replace('536 of 556', '538 of 556')
        else:
            text = text.replace('Seven new modules', 'Three new modules').replace('1,254 exact earlier results', '1,261 exact earlier results')
            text = text.replace('runtime-checkpoint-33-source88-v1', 'runtime-checkpoint-34-source90-v1').replace('checkpoint33 runtime', 'checkpoint34 runtime')
            text = text.replace('536 exercises are complete, 8 partial and 12 pending', '538 exercises are complete, 7 partial and 11 pending')
        atomic(name, text.encode())
    config = path(HISTORY + '/_config.yml').read_text()
    for name in ['book/coverage/inventory-' + side + '-correction' + str(i) + '.json' for i in [89, 90] for side in ['before', 'after']] + ['reports/full-coverage/source34-parsers-v1']:
        line = '  - ' + name + '\n'
        if line not in config:
            config += line
    atomic('_config.yml', config.encode())
    atomic('reports/full-coverage/README.md', '''# Continuing full mathematical coverage

Checkpoint 34 passed the Lean 4.34.1 build, kernel checks and standard-axiom
audit: **11,459 public theorems in 1,264 selected files**. Three new files
passed standalone and named builds and fresh kernel replays. The 1,261 earlier
kernel results were reused after exact source, transitive import and dependency
identities matched. The aggregate build and every theorem's axiom audit ran again.
The [original audit](lean-checkpoint-34-source90-v1/verification-original.json)
and [actual execution](verify-runtime34-execution-v1.json) preserve their provenance.

Coverage remains partial: **538 of 556 exercises are complete, 7 partial and
11 pending**. Of 12,774 overlapping material units, **4,858 are reviewed and
7,916 pending**. The [working ledger](ledger34-working-v1.json) and
[frozen ledger](ledger34-frozen-source-only-v1.json) pass integrity checks.

The batch adds 114 theorems about shifted temporal IQCs, scalar neural feedback
and conditional expectation. Independently reviewed mappings complete Exercises
14.3 and 14.6 and seven whole teaching-material units. Source corrections 89–90
make the neural-loop stability and conditional-expectation domains precise.
The [owner review](../../book/coverage/checks/checkpoint34-review/independent-four-owner34-candidates-review-v3.json)
retains earlier proved claims, pending obligations and historical evidence.
Earlier failed and superseded candidate attempts retain their actual outcomes.

[Static checks](integration34-source90-v1.json) pass for all 29 pages, 556 exercises
and 21 labs. The [functional and visual review](../../book/coverage/checks/checkpoint34-review/browser34-source90-independent-visual-and-functional-closure-v1.json)
binds both changed pages at five widths, ten changed-region captures and mobile
formula scrolling to their exact source hashes. Print was skipped in these runs.
The finite scalar trajectories are bounded floating-point observations;
neither all-time formal safety nor numerical correctness of the 2D explorer is inferred.

The [selection](checkpoint-34-selection.json) retains every checkpoint33 proof.
The [manifest](checkpoint-34-manifest.json) identifies a source-only snapshot.
The actual compiler ran in `runtime-checkpoint-34-source90-v1`; the frozen
snapshot mirrors its exact proof, site and project bytes. No earlier snapshot
or Lean build tree is copied. Three unused Applied proof metadata entries are
omitted from the frozen ledger; every claim is preserved.

Checkpoint 34 is verified locally; its GitHub delivery is pending.
Checkpoint33 delivery is [fully confirmed](publication33-finish-v1.json).
The [continuation note](../../book/coverage/CONTINUATION.md) and
[remaining exercises](../../book/coverage/remaining-exercises34.json) identify further work.

To reproduce the selected snapshot with fresh output paths:

```sh
cd reports/full-coverage/checkpoint-34
python3 book/coverage/validate.py --output reports/ledger-reproduction34.json
cd verification/lean
lake exe cache get
python3 verify.py --output ../../reports/lean-reproduction34
```

The published checkout places selected Lean sources at their normal paths.
The working tree also retains unselected historical sources; its default
aggregate differs from the selected runtime.
'''.encode())
    atomic('book/coverage/CONTINUATION.md', '''# Continue full mathematical coverage

Checkpoint34 verifies 11,459 theorems in 1,264 selected files. Coverage is
538 complete, 7 partial and 11 pending exercises; 4,858 reviewed and 7,916
pending overlapping material units. Full mathematical coverage remains unfinished.
`remaining-exercises34.json` lists the 18 incomplete exercises and current gaps.
Read `progress.json` and `../../reports/full-coverage/README.md` for delivery status.

All three packets in `checks/checkpoint34-preparation-root/three-future34-paired-packets-v1.json`
are now selected and installed. IQC21, NN65 and Conditional28 add 114 theorems;
source89–90 and the v3 owner candidates close Exercises14.3/14.6 and seven new
whole material units. Do not select them or promote their units again.
The prepared NN26 is redundant with NN65 and remains unselected.

The actual audit ran in `../../reports/full-coverage/runtime-checkpoint-34-source90-v1`.
The source-only `../../reports/full-coverage/checkpoint-34` mirrors its bytes.
The working Lean tree retains unselected historical sources; use the selected
snapshot or published checkout for exact reproduction.

The publication checkout is `../../reports/book/publication-repo`; the project
root has no Git repository. Preserve original logs, command receipts, source
history and owner decisions. Copy no earlier snapshot or `.lake` build tree.
Static checks use `../validate28_v1.py --allow-reviewed-corrections`.

The installation and finalization helpers in `checks/checkpoint34-root/` use
atomic writes and accept only exact completed or original stages on a rerun.
`../../reports/full-coverage/finalize-checkpoint34-recovery-execution-v1.json`
retains the genuine audit input hashes and exact finalization command.

The current pending-material triage is
`checks/full-coverage-material-triage/source90-owner34-v3-pending-material-triage-v1.json`.
Its queue is not proof coverage. Broader Basics node922 algorithms, Filippov
integral-curve existence/derivative inclusion and enclosing invariance remain
pending. Review exact current source and independently qualified statements
before further promotion. Finite scalar observations and the 2D explorer remain
distinct scopes, as recorded in the Source90 visual review.
'''.encode())
    record = dict(status='passed_actual_checkpoint34_local_verification_documents_updated_delivery_pending',
        preserved_originals=originals, manifest=ref('reports/full-coverage/checkpoint-34-manifest.json'),
        visual_review=ref(VISUAL), document_sha256={n: sha(n) for n in [*DOCUMENTS, remaining_name]}, coverage_complete=False)
    atomic(OUT, encode(record))
    print(json.dumps({'status': record['status'], 'record': ref(OUT), 'coverage_complete': False}))


if __name__ == '__main__':
    main()

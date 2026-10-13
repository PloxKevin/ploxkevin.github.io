"""Document the actually verified checkpoint35, preserving checkpoint34 documents."""
import copy
import json
import os
import tempfile
from prepare_runtime35 import ROOT, encode, path, put, read, ref, sha

OUT = 'reports/full-coverage/checkpoint35-documentation-v1.json'
HISTORY = 'reports/full-coverage/source-history/documentation34-before-checkpoint35-v1'


def atomic(name, data):
    p = path(name)
    fd, temporary = tempfile.mkstemp(prefix='.' + p.name + '-', dir=p.parent)
    try:
        with os.fdopen(fd, 'wb') as output:
            output.write(data)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, p)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def main():
    final = read('reports/full-coverage/checkpoint35-finalization-v1.json')
    assert final['status'] == 'passed_checkpoint35_actual_audit_export_and_source_only_freeze'
    ledger = read(final['working_ledger']['file'])
    assert ledger['integrity_status'] == 'passed' and ledger['errors'] == []
    assert ledger['counts']['material_review_statuses'] == {'reviewed': 4878, 'pending': 7896}
    originals = {}
    docs = ['README.md', 'verification/lean/README.md', 'book/coverage/progress.json',
            'book/coverage/CONTINUATION.md', 'reports/full-coverage/README.md']
    for n in docs:
        h = HISTORY + '/' + n
        if not path(h).exists():
            put(h, path(n).read_bytes())
        originals[n] = ref(h)
    progress = read('book/coverage/progress.json')
    previous = read(HISTORY + '/book/coverage/progress.json')
    progress['verified_checkpoint'] = {
        'checkpoint': 35, 'proof_files': 1267, 'theorems': 11472, 'status': 'passed',
        'coverage_complete': False, 'report': final['audit']['file'],
        'actual_audit_workdir': str(path('reports/full-coverage/runtime-checkpoint-35-source90-v1/verification/lean')),
        'actual_execution': final['native_execution'], 'fresh_kernel_files': 3,
        'exact_prior_kernel_reuses': 1264}
    progress['working_coverage_report'] = final['working_ledger']['file']
    progress['current_frozen_audit'] = {
        'snapshot': 'reports/full-coverage/checkpoint-35', 'source_only': True,
        'proof_files': 1267, 'status': 'source_exact_mirror_of_actual_runtime_audit',
        'snapshot_execution_claimed': False, 'manifest': final['manifest']}
    progress['current_published_ledger_candidate'] = final['frozen_ledger']['file']
    progress['publication_status'] = 'checkpoint35_verified_locally_publication_pending'
    progress['live_delivery_status'] = 'checkpoint34_delivery_confirmed_checkpoint35_delivery_pending'
    progress['working_next_checkpoint_preparation'] = {
        'status': 'checkpoint35_selected_verified_and_frozen_delivery_pending',
        'inventory': ref('book/coverage/inventory.json'),
        'exercise_counts': {'complete': 539, 'partial': 6, 'pending': 11},
        'material_review_units': {'reviewed': 4878, 'pending': 7896},
        'owner35_integration': final['owner_integration'],
        'canonical_sources_selected': True, 'owner_promotion_performed': True,
        'source_changes_performed': False, 'coverage_complete': False,
        'remaining_exercises': {'file': 'book/coverage/remaining-exercises35.json'},
        'next_material_triage': previous['working_next_checkpoint_preparation'].get('next_material_triage'),
        'triage_limit': 'Source90 owner34 triage remains historical; consult the current ledgers for completed B2 and diagonal units.'}
    progress['checkpoint35_recovery'].update({
        'actual_verification': final['native_execution'],
        'actual_finalization': ref('reports/full-coverage/finalize-checkpoint35-execution-v1.json'),
        'recorder_interruption_and_corruption_tests': ref('book/coverage/checks/checkpoint35-root/recorder-tests-v1.json'),
        'atomic_verification_writer_tests': ref('book/coverage/checks/checkpoint35-root/pipeline-writer-tests-v3.json'),
        'current_runtime_helper_review': ref('book/coverage/checks/checkpoint35-root/pipeline-review-amendment-v4.json'),
        'scope': 'Native command outcomes and atomic verification progress survive tested interruptions. Client/application crash causes remain undiagnosed.'})
    remaining = []
    owners = {}
    for domain in ['foundations', 'applied', 'modules', 'core']:
        n = 'book/coverage/' + domain + '.json'
        owners[n] = sha(n)
        for e in read(n)['exercises']:
            if e['status'] != 'complete_math':
                remaining.append({'owner': domain, 'inventory_key': e['inventory_key'],
                    'label': e['label'], 'status': e['status'],
                    'pending_claims': [c for c in e['claims'] if c['status'] == 'pending' or c['remaining_gaps']]})
    assert len(remaining) == 17
    put('book/coverage/remaining-exercises35.json', encode({
        'checkpoint': 35, 'owner_sha256': owners, 'exercises': remaining, 'coverage_complete': False,
        'scope': 'Current incomplete exercises and exact remaining gaps; not a full teaching-material triage.'}))
    progress['working_next_checkpoint_preparation']['remaining_exercises'] = ref('book/coverage/remaining-exercises35.json')
    continuation = """# Continue full mathematical coverage

Checkpoint35 verifies 11,472 theorems in 1,267 selected files. Coverage is
539 complete, 6 partial and 11 pending exercises; 4,878 reviewed and 7,896
pending overlapping material units. Full mathematical coverage remains unfinished.
`remaining-exercises35.json` lists the 17 incomplete exercises and exact gaps.
Read `progress.json` and `../../reports/full-coverage/README.md` for delivery status.

The three checkpoint35 sources are selected and installed. Adaptive Gaussian
conditional laws, exact noise/radius calculations and diagonal multiplier/QC
bridges add 13 theorems, complete Exercise5.B2 and 20 whole material units.
Three already reviewed diagonal mappings are refreshed without extra completion
credit. All displayed decimals remain approximations to exact expressions.
Do not select these sources or promote those units again. Antiderivative
strong-convexity equivalences and broader overlapping parents remain pending.

The actual audit ran in `../../reports/full-coverage/runtime-checkpoint-35-source90-v1`;
the source-only `../../reports/full-coverage/checkpoint-35` mirrors its exact bytes.
All31 site assets are unchanged from checkpoint34. Its existing functional and
visual evidence remains tied to those same bytes. Static checks ran again.
The working Lean tree also retains unselected historical sources; use the selected
snapshot or the published checkout to reproduce the selected aggregate.

The publication checkout is `../../reports/book/publication-repo`; the project
root has no Git repository. Preserve native logs, source history and owner
decisions. Copy no previous snapshot, recursive archive or `.lake` build tree.
New runtime/snapshot sources share immutable content objects by hardlink.
Final device-bloat cleanup remains due after full coverage and final publication.

`checks/checkpoint35-root/record_native35.py` saves genuine started/final command
receipts and refuses to call unfinished attempts successful. Completed reruns
verify the actual command, cwd, input and raw-log hashes. Failed attempts remain
immutable; use a fresh attempt filename after a failure or hard interruption.
`verify.py --resume-kernel` accepts only complete identity-matched replay results.
Kernel progress and the final report now use atomic writes. Runtime preparation,
owner installation and finalization accept exact completed stages on reruns.
The recorder and writer passed injected interruption/corruption tests.
These checks address pipeline resumption; client/application crash causes were
not diagnosed. Checkpoint34 delivery remains preserved separately.
"""
    report = """# Continuing full mathematical coverage

Checkpoint35 passed the Lean4.34.1 build, kernel replay and standard-axiom audit:
**11,472 public theorems in 1,267 selected files**. Three new modules received
fresh kernel checks; 1,264 earlier results were reused only after exact source,
transitive-import and dependency identities matched. The aggregate build and
every theorem's axiom audit ran again. The [original audit](lean-checkpoint-35-source90-v1/verification-original.json)
and [native execution](verify-runtime35-execution-v1.json) retain actual provenance.

Coverage remains partial: **539 of 556 exercises complete, 6 partial, 11 pending**.
Of 12,774 overlapping teaching units, **4,878 reviewed and 7,896 pending**.
The [working ledger](ledger35-working-v1.json), [frozen ledger](ledger35-frozen-source-only-v1.json)
and [manifest](checkpoint-35-manifest.json) pass exact integrity checks.

The batch adds 13 theorems about genuine conditional Gaussian laws, finite-horizon
noise envelopes, exact rational enclosures and diagonal activation QCs.
Independent reviews complete Exercise 5.B2, 14 mathematical units and 6 literal
navigation/citation labels. Three existing proved mappings are refreshed without
extra completion credit. Rounded envelope/radius values are approximations;
the exact expressions and stated probability/model hypotheses carry the certificate.
Broader antiderivative and other overlapping parent scopes remain pending.

All 31 site assets retain checkpoint34's exact hashes and functional/visual scope.
The [fresh static check](integration35-source90-v1.json) passes all 29 pages,
556 exercises and 21 labs. No browser or numerical-explorer guarantee is widened.
The [selection](checkpoint-35-selection.json) retains all checkpoint34 proofs.
The source-only snapshot mirrors the actual runtime bytes and shares immutable
objects; no previous archive or build cache is copied. Unused Applied proof
metadata is omitted from the frozen ledger while all claims remain preserved.

Workspace reproduction, with fresh output paths:

```sh
cd reports/full-coverage/checkpoint-35
python3 book/coverage/validate.py --output reports/ledger-reproduction35.json
cd verification/lean
lake exe cache get
python3 verify.py --output ../../reports/lean-reproduction35
```

In the published checkout the selected sources occupy their normal paths:
run `python3 book/coverage/validate.py`, then run `lake exe cache get` and
`python3 verify.py` from `verification/lean`. The workspace's default aggregate
also retains unselected historical sources and differs from this selected runtime.

Delivery is tracked separately in the [progress ledger](../../book/coverage/progress.json).
Checkpoint34 content/metadata delivery is [confirmed](publication34-finish-v1.json).
The [continuation note](../../book/coverage/CONTINUATION.md) and
[remaining exercises](../../book/coverage/remaining-exercises35.json) retain further work.

Native command recording passed nine interruption/restart/corruption scenarios.
Atomic kernel/final-report writes, source-only exact reruns and finalizer log
checks passed isolated failure-injection tests. Earlier failed attempts remain
untouched. These tests establish pipeline behavior and do not diagnose a client crash.
"""
    root_readme = path(HISTORY + '/README.md').read_text()
    marker = 'The [continuing coverage audit]'
    index = root_readme.index(marker)
    root_readme = root_readme[:index] + """The [continuing coverage audit](reports/full-coverage/README.md) verifies
11,472 theorems in 1,267 selected Lean files. Of 556 exercises, 539 are complete,
6 partial and 11 pending; 7,896 overlapping teaching-material units remain pending.
Checkpoint35 adds 13 theorems, completes Exercise 5.B2 and 20 whole material units,
and preserves earlier evidence. Native recording and atomic progress writes
support interrupted-run recovery. Delivery status is recorded separately in
[the progress ledger](book/coverage/progress.json); the
[continuation note](book/coverage/CONTINUATION.md) retains all remaining work.
Browser evidence stays bound to the exact unchanged site bytes.
"""
    lean_readme = path(HISTORY + '/verification/lean/README.md').read_text()
    for before, after in [('11,459', '11,472'), ('1,264 files', '1,267 files'),
                          ('1,261 exact', '1,264 exact'), ('checkpoint-34', 'checkpoint-35'),
                          ('checkpoint34', 'checkpoint35'), ('538 exercises', '539 exercises'),
                          ('7 partial', '6 partial'), ('7,916 material', '7,896 material')]:
        lean_readme = lean_readme.replace(before, after)
    lean_readme += '\nKernel-progress and final-report JSON are installed atomically, preserving the last complete receipt if a write is interrupted.\n'
    new_docs = {'README.md': root_readme.encode(), 'verification/lean/README.md': lean_readme.encode(),
        'book/coverage/progress.json': encode(progress), 'book/coverage/CONTINUATION.md': continuation.encode(),
        'reports/full-coverage/README.md': report.encode()}
    if path(OUT).exists():
        receipt = read(OUT)
        assert receipt['finalization'] == ref('reports/full-coverage/checkpoint35-finalization-v1.json')
        assert receipt['document_sha256'] == {n: sha(n) for n in new_docs}
        print(json.dumps({'status': 'passed_existing_exact_documentation_receipt', 'record': ref(OUT)}))
        return
    for n, data in new_docs.items():
        atomic(n, data)
    put(OUT, encode({'status': 'passed_checkpoint35_actual_audit_documentation_delivery_pending',
        'preserved_original_documents': originals,
        'finalization': ref('reports/full-coverage/checkpoint35-finalization-v1.json'),
        'document_sha256': {n: sha(n) for n in docs}, 'remaining_exercises': ref('book/coverage/remaining-exercises35.json'),
        'coverage_complete': False, 'publication_claimed': False}))
    print(json.dumps({'status': 'passed_checkpoint35_documentation', 'record': ref(OUT)}))


if __name__ == '__main__':
    main()

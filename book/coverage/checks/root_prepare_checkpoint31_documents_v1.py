"""Document genuine checkpoint31 results without claiming full coverage or delivery."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil

ROOT = Path(__file__).resolve().parents[3]
HISTORY = ROOT/'reports/full-coverage/source-history/documentation-before-checkpoint31-v1'
OUT = ROOT/'reports/full-coverage/checkpoint31-documentation-preparation-v1.json'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n): return json.loads((ROOT/n).read_bytes())
def ref(n): return {'file':n, 'sha256':sha(ROOT/n)}

assert not HISTORY.exists() and not OUT.exists()
manifest = read('reports/full-coverage/checkpoint-31-manifest.json')
audit = read('reports/full-coverage/lean-checkpoint-31-source81-v1/verification-original.json')
ledger = read('reports/full-coverage/lean-checkpoint-31/ledger-audit-frozen-v1.json')
browser = read('reports/full-coverage/browser-checkpoint-31-changed2-v1.json')
delivery30 = read('reports/full-coverage/publication30-finish-root-v1.json')
assert manifest['status'] == 'formal_verification_passed_partial_coverage' and manifest['source_only_snapshot'] is True
assert audit['status'] == 'passed' and audit['proof_file_count'] == 1248 and audit['theorem_count'] == 11184
assert ledger['integrity_status'] == 'passed' and ledger['errors'] == [] and ledger['mathematical_coverage_complete'] is False
assert len(browser) == 2 and all(r['status']=='passed' and r['errors']==[] and len(r['viewports'])==5 for r in browser)
assert {r['file']:r['source_sha256'] for r in browser} == {n.split('/')[-1]:h for n,h in audit['source_sha256'].items() if n in ['SafeLearning/primer-linalg.html','SafeLearning/nn-in-the-loop.html']}
counts = ledger['counts']
assert [counts['statuses'][n] for n in ['exercise:complete_math','exercise:partial','exercise:pending']] == [536,8,12]
assert counts['material_review_statuses'] == {'reviewed':4835,'pending':7939}
files = ['reports/full-coverage/README.md','book/coverage/progress.json','book/README.md','verification/lean/README.md']
originals = {}
for n in files:
    p = HISTORY/n; p.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(ROOT/n,p)
    assert sha(p)==sha(ROOT/n); originals[n]={'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
progress = read('book/coverage/progress.json')
progress['previous_checkpoint30_delivery'] = {'content_commit':'ae9e78658094db31d456b9dec509cc7a92b7f386',
    'metadata_commit':'676db1f7d13ddbf65c2f0253d1fab79c44948a7e',
    'original_progress':originals['book/coverage/progress.json'],
    'actual_delivery_closure':ref('reports/full-coverage/publication30-finish-root-v1.json'),
    'actual_metadata_all31_live':ref('reports/full-coverage/live-checkpoint-30-attempt3.json'),
    'scope':'Successful checkpoint30 delivery. These earlier receipts do not establish checkpoint31 delivery.'}
progress['verified_checkpoint'] = {'checkpoint':31,'proof_files':1248,'theorems':11184,'status':'passed','coverage_complete':False,
    'report':'reports/full-coverage/lean-checkpoint-31-source81-v1/verification-original.json',
    'actual_audit_workdir':str(ROOT/'reports/full-coverage/runtime-checkpoint-31-source81-v1/verification/lean'),
    'actual_execution':ref('reports/full-coverage/verify-runtime-checkpoint31-source81-execution-v1.json'),
    'fresh_kernel_files':6,'exact_prior_kernel_reuses':1242}
progress['current_frozen_audit'] = {'snapshot':manifest['snapshot'],'source_only':True,'proof_files':1248,
    'status':'source_exact_mirror_of_actual_runtime_audit','snapshot_execution_claimed':False,
    'manifest':ref('reports/full-coverage/checkpoint-31-manifest.json')}
progress['publication_status']='prepared_source_exact_checkpoint_31_awaiting_delivery'
progress['live_delivery_status']='checkpoint31_not_yet_pushed_or_live_verified'
progress['live_delivery_evidence']={'previous_checkpoint30':progress['previous_checkpoint30_delivery']}
progress['current_documented_material_corrections']=81
progress['inventory_sha256']=ledger['inventory_sha256']
progress['working_coverage_report']='reports/full-coverage/lean-checkpoint-31/ledger-audit-working-v1.json'
progress['current_published_ledger_candidate']='reports/full-coverage/lean-checkpoint-31/ledger-audit-frozen-v1.json'
progress['working_next_checkpoint_preparation']={'status':'checkpoint31_selected_verified_and_mapped_original_full_coverage_objective_unfinished',
    'inventory':'book/coverage/inventory.json','inventory_sha256':ledger['inventory_sha256'],
    'exercise_counts':{'complete':536,'partial':8,'pending':12},'material_review_units':counts['material_review_statuses'],
    'owner31_integration':ref('reports/full-coverage/owner31-reviewed-candidate-integration-v4.json'),'coverage_complete':False}
(ROOT/'book/coverage/progress.json').write_text(json.dumps(progress,indent=2)+'\n')
text = f'''# Continuing full mathematical coverage

Checkpoint 31 passed the local Lean 4.34.1 build, kernel checks and standard-axiom
audit: **11,184 public theorems in 1,248 selected files**. Six new files passed
twelve standalone and named compiler commands, then received fresh kernel
replays. The 1,242 earlier kernel results were reused only after exact module,
transitive import and dependency identities matched. The normal aggregate build
and every theorem's axiom audit ran again. There are no nonstandard axioms.
The [original audit](lean-checkpoint-31-source81-v1/verification-original.json)
and [actual execution record](verify-runtime-checkpoint31-source81-execution-v1.json)
preserve commands, outputs, hashes, times and the real runtime directory.

Coverage remains partial: **536 of 556 exercises are complete, 8 partial and
12 pending**. Of 12,774 overlapping material units, 4,835 are reviewed and
7,939 pending. The [working ledger](lean-checkpoint-31/ledger-audit-working-v1.json)
and [frozen ledger](lean-checkpoint-31/ledger-audit-frozen-v1.json) pass integrity
checks. Independent reviews establish correspondence with the exact lesson
text and assumptions; Lean checks the encoded statements. Component proofs
do not silently complete whole exercises or enclosing paragraphs.

The new sources cover full spectral induction including repeated eigenvalues,
logarithmic and polynomial growth comparisons, log-determinant Taylor
estimates, discounted-return and fixed-point explorer captions, and integral
tracking with exact offsets and spectral radii. Actual bounded Filippov
velocities and discrete Euler nodes are proved as components; integral-curve
existence and the whole invariance exercise remain pending. [Corrections 80–81](source80-81-corrections-application-v3.json)
add the positive-dimension qualification to eigenbasis nonuniqueness and
distinguish exact values from rounded integral-tracking numbers. Full-page
parser checks, preserved originals and exact inverse evidence accompany
the [five reviewed owner records](owner31-reviewed-candidate-integration-v4.json).

[Static book checks](integration-31-source81-v2.json) pass for 29 pages,
556 exercises and 21 application labs. [Browser checks](browser-checkpoint-31-changed2-v1.json)
pass on both corrected pages at five widths each. [Separate captures](browser31-source81-two-changed-regions-v1.json)
show the corrected original proof sketch and Exercise 14.5 at 360px and 1280px;
their visual review is limited to those regions. All failed earlier attempts
remain preserved alongside their subsequent passing records.

The [selection](checkpoint-31-selection.json) retains all 1,242 earlier proof
sources. The [manifest](checkpoint-31-manifest.json) identifies
{len(manifest['frozen_inputs_sha256']):,} files in the source-only snapshot.
No old snapshot or Lean build tree was copied. The actual compiler ran in
`runtime-checkpoint-31-source81-v1`; the later frozen snapshot mirrors its
source bytes. Only three unused Applied proof metadata entries are omitted
from the frozen owner ledger; all claims and original raw records remain.
The working tree has additional unselected historical sources, and its
default aggregate differs from the selected runtime. In the published
checkout, selected sources and their aggregate occupy the normal paths.

Checkpoint 31 is verified locally; its GitHub delivery is pending.
Checkpoint 30's content and metadata delivery is [fully confirmed](publication30-finish-root-v1.json),
including successful Pages jobs and the [fresh metadata all-31-asset check](live-checkpoint-30-attempt3.json).
Further conditional-expectation, IQC, Newton, norm and convolution work remains
outside this selected batch until compilation and independent source review.

To reproduce the selected Lean audit and ledger from this local snapshot,
use fresh report paths:

```sh
cd reports/full-coverage/checkpoint-31
python3 book/coverage/validate.py --output reports/ledger-reproduction31.json
cd verification/lean
lake exe cache get
python3 verify.py --output ../../reports/lean-reproduction31
```

The [published Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
and original audit records are available in Git. The full coverage objective
remains unfinished.
'''
(ROOT/'reports/full-coverage/README.md').write_text(text)
p=ROOT/'book/README.md'; s=p.read_text()
assert s.count('11,080 theorems in 1,242 selected files; 535 of 556 exercises')==1
s=s.replace('11,080 theorems in 1,242 selected files; 535 of 556 exercises','11,184 theorems in 1,248 selected files; 536 of 556 exercises')
assert s.count('python3 book/validate.py')==1
s=s.replace('python3 book/validate.py','python3 book/validate28_v1.py --allow-reviewed-corrections --output reports/book/static-current.json')
p.write_text(s)
p=ROOT/'verification/lean/README.md';s=p.read_text();start=s.index('Its current selected batch contains');end=s.index('\n\nThe separate numerical recomputation',start)
s=s[:start]+'''Its current selected batch contains 11,184 theorems in 1,248 files.
Six new modules received fresh kernel replays; 1,242 exact earlier results
were reused under source/import and dependency fingerprints. The normal
aggregate build and every theorem's standard-axiom audit ran again. The
actual audit ran in `runtime-checkpoint-31-source81-v1`. The source-only
snapshot mirrors its bytes and contains no copied build cache or earlier trees.

The inventory contains 556 exercises and 12,774 overlapping material units.
536 exercises are complete, 8 partial and 12 pending; 7,939 material units
remain pending. Source correspondence review can reopen entries while their
formal proofs remain valid. Follow the source-only snapshot reproduction
commands in the continuing audit for the exact selected batch. The working
directory also retains unselected historical sources, and its default
aggregate is not the selected checkpoint31 runtime. In a clean published
checkout the selected sources and aggregate occupy their normal paths.'''+s[end:]
p.write_text(s)
record={'status':'actual_checkpoint31_documented_delivery_pending_full_coverage_unfinished','prepared_at_utc':datetime.now(timezone.utc).isoformat(),
    'original_documents':originals,'current_documents':{n:ref(n) for n in files},
    'manifest':ref('reports/full-coverage/checkpoint-31-manifest.json'),'audit':ref('reports/full-coverage/lean-checkpoint-31-source81-v1/verification-original.json'),
    'frozen_ledger':ref('reports/full-coverage/lean-checkpoint-31/ledger-audit-frozen-v1.json'),'browser':ref('reports/full-coverage/browser-checkpoint-31-changed2-v1.json'),
    'previous_delivery':ref('reports/full-coverage/publication30-finish-root-v1.json'),'coverage_complete':False,'checkpoint31_delivery_claimed':False}
with OUT.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':record['status'],'result':ref(OUT.relative_to(ROOT).as_posix()),'coverage_complete':False}))

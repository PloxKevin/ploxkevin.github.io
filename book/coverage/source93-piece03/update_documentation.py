"""Install the exact selected aggregate and document verified progress honestly."""
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'book/coverage/source91-piece01'))
import common as c
sys.path.insert(0,str(ROOT/'book/solutions'))
from solution_release import atomic_copy

HERE='book/coverage/source93-piece03'
REPORTS='reports/full-coverage/source93-piece03'
RUNTIME='reports/full-coverage/runtime-source93-piece03-v1'
AUDIT=RUNTIME+'/reports/lean-verification/verification.json'


def main():
    ledger=c.read(HERE+'/ledger-v1.json');audit=c.read(AUDIT)
    assert audit['status']=='passed' and ledger['audit']==c.ref(AUDIT)
    assert ledger['counts']['new_theorems']==22 and ledger['independent_review'] is None
    prior=c.read('reports/solution-review/runtime-source93-foundations-v1/reports/lean-verification/verification.json')
    names=['README.md','verification/lean/README.md','book/coverage/CONTINUATION.md',
        'book/coverage/progress.json','book/solutions/RELEASE.md','book/coverage/README.md',
        'verification/lean/SafeLearning.lean']
    for name in names:c.put(HERE+'/before-piece03/'+name,c.path(name).read_bytes())
    assert c.ref('verification/lean/SafeLearning.lean')['sha256']==prior['project_sha256']['verification/lean/SafeLearning.lean']
    aggregate=c.path(RUNTIME+'/verification/lean/SafeLearning.lean').read_bytes()
    assert c.sha(aggregate)==audit['project_sha256']['verification/lean/SafeLearning.lean']
    atomic_copy(ROOT/'verification/lean/SafeLearning.lean',aggregate)
    text=c.path('README.md').read_text()
    old='Lean audit passes **11,522 theorems in 1,272 unchanged proof files**. New explanations\nare queued for exact formal correspondence; Exercise 1.5 remains partial. Earlier\n'
    new='Lean audit passes **11,544 theorems in 1,274 selected proof files**. The latest\n[formal piece](book/coverage/source93-piece03/README.md) adds 22 checked theorems\nfor Gaussian-tail rounding, underflow and the original expected count. Its source\nmapping is self-reviewed; independent review is pending, with no new full-coverage\ncredit. All eighty foundation answers remain queued for exact correspondence,\nand Exercise 1.5 remains partial. Earlier\n'
    assert text.count(old)==1
    atomic_copy(ROOT/'README.md',text.replace(old,new,1).encode())
    text=c.path('verification/lean/README.md').read_text()
    end=text.index('Source91 formal piece 01 closes')
    opening='''# Current Source93 selection

The current frozen workspace runtime is
`../../reports/full-coverage/runtime-source93-piece03-v1`.
It audits **1,274 selected files / 11,544 theorems**. Two new modules add
22 theorems for finite-format Gaussian-tail rounding and a same-process
expected-count counterexample. Their kernel replays, aggregate build and
all-theorem standard-axiom audit pass. The remaining 1,272 module checks retain
exact prior source/import and pinned dependency evidence.

The [piece ledger](../../book/coverage/source93-piece03/ledger-v1.json) records
the finite format, nearest rounding model, exact source hashes and limits.
The new mapping is self-reviewed; independent source-to-statement review is
pending. The current independently reviewed total stays at 27 mathematical
clauses and 12 complete leaves, with Exercise 1.5 partial. The new model
supports three further candidate clauses and one candidate leaf, with zero
new completion credit until that review. The book has 586 exercises; all
eighty expanded foundation answers still need exact current correspondence.

The published checkout contains exactly the selected proof set at normal paths.
The canonical workspace also retains eight unselected future modules: do not
run its directory-wide verifier as if they were selected. Use the frozen runtime
above, or a clean published checkout. Do not overwrite historical audit output.
All source/version counts below describe their historical snapshots.

'''
    atomic_copy(ROOT/'verification/lean/README.md',(opening+text[end:]).encode())
    text=c.path('book/solutions/RELEASE.md').read_text()
    start=text.index('The selected Source93 Lean audit passes')
    end=text.index("Source92's 556-exercise inventory",start)
    new='''The latest selected Source93 Lean audit passes 1,274 files and 11,544 theorems.
The [rounding proof piece](../coverage/source93-piece03/README.md) adds 22
theorems for false-zero CDF subtraction, direct-tail underflow and an actual
positive expected-count example whose CDF evaluation is zero. Its finite
nearest-rounding model and original-process bridge are kernel-checked and
self-reviewed; independent correspondence review is pending. No new whole
leaf or exercise credit is claimed. The previously reviewed total remains
27 clauses and 12 complete leaves, with Landscape Exercise 1.5 partial.

All eighty current foundation answers remain queued for exact source
correspondence, with shifted ordinal keys explicitly recorded. This proof-only
continuation preserves all thirty-one reader assets and the existing browser,
print, arithmetic and integration evidence bound to those exact assets.

'''
    atomic_copy(ROOT/'book/solutions/RELEASE.md',(text[:start]+new+text[end:]).encode())
    text=c.path('book/coverage/README.md').read_text()
    old='Run `python3 book/inventory_claims.py` to freeze the 556 exercise sources and\nthe review queue of mathematical source units. The queue itself is not proof\ncoverage. Review surrounding prose too; mathematical assertions can lack TeX.\n'
    new='The current [Source93 inventory](../solutions/releases/source93-foundations-v1/source93-inventory/inventory.json)\ncontains 586 exercises and 14,889 overlapping source units. Regenerate inventories\nin a fresh versioned output directory; retain historical inventories unchanged.\nThe queue itself is not proof coverage. Review surrounding prose too; mathematical\nassertions can lack TeX. The [continuation](CONTINUATION.md) identifies the latest\nselected audit and distinguishes kernel checks from independent source review.\n'
    assert text.count(old)==1
    atomic_copy(ROOT/'book/coverage/README.md',text.replace(old,new,1).encode())
    continuation='''# Continue from Source93 formal piece 03

Block 0 retains 80 exercises: six algebra warm-ups, 63 local exercises, four
application questions and seven mixed review problems. Thirty exercises were
added and all fifty original solutions expanded. The book has 586 exercises.
All eighty arithmetic checks, browser checks from 320 to 1280 pixels, print
and all twenty-one lab integration checks remain tied to the unchanged reader
assets. Source93's additions are self-reviewed; no independent review is claimed.

The current inventory is
`../solutions/releases/source93-foundations-v1/source93-inventory/inventory.json`.
All eighty current foundation answers still need exact formal correspondence.
The thirty additions and fifty expanded answers receive no automatic credit.
Consult `../solutions/releases/source93-foundations-v1/foundation-formal-status.json`;
ordinal exercise and material-unit keys shifted. Rematch retained theory by
exact HTML/text and context, never by old node positions. The other 506 reader
exercise bodies are unchanged from Source92.

The current passing selected audit is
`../../reports/full-coverage/runtime-source93-piece03-v1/reports/lean-verification/verification.json`:
1,274 files and 11,544 theorems. Two new modules add 22 theorem bodies and
received fresh kernel replays. All other 1,272 checks reuse exact prior
source/import and pinned dependency evidence; the aggregate build and every
theorem's axiom audit are fresh. Only propext, Classical.choice and Quot.sound
occur. Use a fresh output directory for later audits. The canonical tree still
has eight unselected future modules; only the selected set is published.

The latest exact mapping is `source93-piece03/ledger-v1.json`, tied to
Landscape Exercise 1.5(ii), leaf `landscape.html::node-1461`. The finite
exponent/fraction model constructs nearest rounding on binary64 values in
[0,1]. Actual Gaussian tails tend to zero and remain positive at every finite
threshold. The proofs derive CDF false zeros and direct-tail underflow, then
produce a finite threshold with true tail 2^-60: direct rounding preserves it,
while CDF subtraction gives zero. A valid one-step original recurrence has
that same positive expected count and a zero CDF evaluation.

These 22 new proofs pass the kernel and are self-reviewed. A separate review
agent needs explicit user authorization under the session's delegation rule;
authorization was requested asynchronously and has not been received. No
independent review or completion promotion is claimed. The reviewed total
therefore stays at 27 mathematical clauses and 12 complete leaves. Three new
candidate clauses and the mixed numerical leaf await independent source review.
The model rounds exact real function values; it does not certify a library
implementation, hardware primitives, input rounding or part(iii)'s numbers.

Next: independently check the exact mapping and model limits, then prove
part(iii)'s nine-digit numerical enclosures, stationary comparison and actual
joint-failure interpretation. The whole Exercise 1.5 and full book coverage
remain incomplete. Source90's 539/6/11 exercise totals remain historical.

Publish only exact verified selected sources/evidence to
`../../reports/book/publication-repo`. Record all Pages jobs and all 31 live
asset hashes separately. Preserve unique failed/interrupted evidence. Final
cleanup remains deferred until full coverage and final publication; exclude
build caches. The cause of the earlier application crash is undiagnosed.
'''
    atomic_copy(ROOT/'book/coverage/CONTINUATION.md',continuation.encode())
    progress=c.read('book/coverage/progress.json')
    progress.update(current_site_source_version='Source93: 80 foundation exercises; proof-only piece03 preserves all31 reader assets',
        current_selected_proof_audit=c.ref(AUDIT),current_selected_audit=c.ref(AUDIT),
        current_selected_proof_audit_scope='Source93: 1274 selected files / 11544 theorems; 22 new kernel-checked theorem bodies. New numerical model correspondence is self-reviewed, independent review pending. Reviewed totals remain27 clauses /12 leaves; whole Exercise1.5 partial.',
        publication_status='Source93_piece03_verified_exact_publication_pending')
    piece=progress['formal_coverage_piecewise_work']
    piece['previous_piece02_before_piece03']={k:v for k,v in piece.items() if k!='previous_piece01'}
    piece.update(current_piece=3,current_piece_publication='pending',selected_proof_files=1274,
        selected_public_theorems=11544,new_reviewed_proved_clauses=0,new_complete_leaf_units=0,
        new_complete_whole_exercises=0,new_kernel_checked_theorems=22,
        new_kernel_verified_mathematical_clause_candidates=3,independent_review_pending=True,
        current_piece_ledger=c.ref(HERE+'/ledger-v1.json'),current_audit=c.ref(AUDIT),
        current_piece_completion_record=c.ref(REPORTS+'/completion-v1.json'),
        next_piece='Independent numerical-model source review; then part(iii) nine-digit enclosures and joint-failure interpretation.')
    piece['checked_local_piece_candidates']=[c.ref(REPORTS+'/completion-v1.json')]
    for key in ['current_piece_commit','completed_delivery','metadata_commit']:
        piece.pop(key,None)
    atomic_copy(ROOT/'book/coverage/progress.json',(json.dumps(progress,indent=2)+'\n').encode())
    assert all(c.ref(n)['sha256']==digest for n,digest in audit['source_sha256'].items())
    c.json_put(REPORTS+'/documentation-v1.json',dict(status='passed_exact_docs_and_selected_aggregate',
        ledger=c.ref(HERE+'/ledger-v1.json'),audit=c.ref(AUDIT),files=[c.ref(n) for n in names],
        reader_assets_unchanged=31,new_independent_completion_credit=0,helper=c.ref(HERE+'/update_documentation.py')))
    print(dict(status='updated',proof_files=1274,theorems=11544,new_independent_completion_credit=0))


if __name__=='__main__':main()

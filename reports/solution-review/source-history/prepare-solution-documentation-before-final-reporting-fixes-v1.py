"""Bind actual completed checks and prepare accurate Source91 release documentation."""
import json
from pathlib import Path
import re

import solution_review as review
import solution_release as release

READY='reports/solution-review/source91-release-ready-v1.json'
HISTORY='reports/solution-review/source-history/before-source91-documentation-v1'


def native(name):
    value=review.read(name)
    assert value['status']=='passed' and value['actual_exit_code']==0
    assert value['helper_sha256_before']==value['helper_sha256_after']
    assert review.ref(value['log'])['sha256']==value['log_sha256']
    return value


def main():
    fingerprint=review.ref(release.PLAN)['sha256'];plan=release.load_plan(fingerprint)
    integration=review.read('reports/solution-review/release-source91-integration-v1.json')
    assert integration['status']=='passed_all556_installed_solution_preservation_and_book_integration'
    assert integration['counts']==plan['counts'] and integration['plan']==review.ref(release.PLAN)
    assert integration['book_integration']['status']=='PASS'
    executions=[native('reports/solution-review/'+n) for n in [
        'source91-prepare-execution-v1.json','source91-install-execution-v1.json','source91-book-build-execution-v1.json',
        'source91-integration-execution-v1.json','source91-runtime-prepare-execution-v1.json','source91-lean-audit-execution-v1.json',
        'source91-qa-check-execution-v1.json','source91-reader-final-composition-execution-v1.json','source91-visual-execution-v1.json']]
    qa=review.read(executions[6]['log'])
    assert len(qa)==29 and {r['file'] for r in qa}=={Path(n).name for n in plan['site_source91_sha256'] if n.endswith('.html')}
    for row in qa:
        assert all(not row[k] for k in ['consoleErrors','pageErrors','leftoverDollar','katexErrors','missingAnchors','brokenLinks','mobileOverflow','mobileOverflowExpanded']),row['file']
    browser_final=review.read('reports/solution-review/source91-reader-browser-final-v1.json')
    assert browser_final['status']=='passed_all29_reader_pages_from_exact_native_attempts'
    browser=browser_final['pages']
    assert len(browser)==29 and all(r['status']=='passed' and not r['errors'] for r in browser)
    assert {r['file'] for r in browser}=={r['file'] for r in qa}
    assert sum(r['exerciseCounts']['total'] for r in browser)==556
    for row in browser:
        assert row['source_sha256']==plan['site_source91_sha256']['SafeLearning/'+row['file']]
        assert {v['width'] for v in row['viewports']}=={320,390,768,820,1280}
    audit=review.read('reports/solution-review/source91-lean-audit-export-v1.json')
    assert audit['status']=='passed_actual_source91_selected35_build_kernel_and_all_axiom_audit_export'
    assert audit['proof_files']==1267 and audit['public_theorems']==11472 and audit['fresh_build_and_all_theorem_axiom_audit']
    installed=review.read('reports/solution-review/source91-installed-independent-review-v1.json')
    assert installed['status'].startswith('approved') and not installed.get('errors')
    visual=review.read('reports/solution-review/source91-final-visual-review-v1.json')
    assert visual['status'].startswith('approved') and not visual.get('errors')
    pipeline=review.read('reports/solution-review/solution-release-independent-pipeline-review-v1.json')
    runtime=review.read('reports/solution-review/source91-runtime-delivery-independent-review-v1.json')
    assert pipeline['status'].startswith('approved') and runtime['status'].startswith('approved')
    for name,h in plan['site_source91_sha256'].items():assert review.ref(name)['sha256']==h
    evidence_names=['book/solutions/releases/source91-v1/plan.json',
        'reports/solution-review/release-source91-integration-v1.json','reports/solution-review/source91-lean-audit-export-v1.json',
        'reports/solution-review/source91-reader-browser-final-v1.json','reports/solution-review/source91-qa-check-execution-v1.json',
        'reports/solution-review/source91-installed-independent-review-v1.json','reports/solution-review/source91-final-visual-review-v1.json',
        'reports/solution-review/solution-release-independent-pipeline-review-v1.json','reports/solution-review/source91-runtime-delivery-independent-review-v1.json']
    ready={'status':'passed_source91_all556_release_ready_for_publication','counts':plan['counts'],
           'helper':review.ref(Path(__file__).relative_to(review.ROOT).as_posix()),'evidence':[review.ref(n) for n in evidence_names],
           'site_source91_sha256':plan['site_source91_sha256'],'all556_math_and_student_depth_independently_approved':True,
           'actual_all29_browser_QA_passed':True,'actual_selected_proof_build_and_axiom_audit_passed':True,
           'actual_visual_views_inspected':True,'formatting_exceptions':plan['formatting_exceptions'],
           'publication_status':'pending_actual_content_commit_push_Pages_and_live_hashes',
           'formal_source_correspondence_for_rewritten_answers':'pending_explicit_rebase',
           'historical_checkpoint35_coverage_source90_only':{'complete':539,'partial':6,'pending':11,'material_reviewed':4878,'material_pending':7896}}
    review.json_put(READY,ready)
    doc_names=['README.md','book/coverage/progress.json','book/coverage/CONTINUATION.md','reports/full-coverage/README.md','verification/lean/README.md']
    for name in doc_names:
        saved=HISTORY+'/'+name
        if not review.path(saved).exists():review.put(saved,review.path(name).read_bytes())
    progress=review.read(HISTORY+'/book/coverage/progress.json')
    progress['previous_checkpoint35_delivery']=progress['live_delivery_evidence']
    progress['current_site_source_version']='Source91: independently reviewed student solution expansion'
    progress['publication_status']='source91_all556_solutions_ready_publication_pending'
    progress['verified_checkpoint']['source_correspondence_version']='Source90 historical exact owner ledgers'
    progress['current_selected_proof_audit']=audit['relocated_report']
    progress['current_selected_proof_audit_scope']='Encoded selected checkpoint35 proofs pass with Source91 asset fingerprints; correspondence for rewritten answers remains pending.'
    progress['solution_depth_requirement'].update(status='all556_independently_reviewed_installed_and_reader_QA_passed_publication_pending',
        counts=plan['counts'],pedagogical_completion_claimed=True,release_ready=review.ref(READY),
        immutable_approved_tracker=plan['approved_tracker'],question_and_hint_semantics_preserved=True,
        exact_non_solution_formatting_exceptions=plan['formatting_exceptions'])
    progress['working_next_checkpoint_preparation']['source_version']='Source90 historical; Source91 formal correspondence rebase required before further coverage promotions'
    progress['source91_inventory']=review.ref(release.RELEASE+'/source91-inventory/inventory.json')
    release_doc=f'''# Source91 worked solutions

All **556 exercise solutions on 22 pages** have independent mathematical and
student-depth review. **251 answers are expanded; 305 already thorough answers
are retained.** Expanded solutions explain the method, notation and assumptions,
intermediate calculations or proof steps, and the meaning of the result.

The questions, hints, exercise order, anchors and interactive scripts are
preserved. One separate formatting repair restores the closing inner-product
delimiter in the GP readiness question. The exact exception and every selected
answer are recorded in [the release plan](releases/source91-v1/plan.json).

The [installed-source review](../../reports/solution-review/source91-installed-independent-review-v1.json)
and [book integration](../../reports/solution-review/release-source91-integration-v1.json)
check all 556 bodies, both authored/integrated copies, and all other page bytes.
Actual browser checks pass all 29 pages, every expanded disclosure, keyboard and
mobile navigation, print behavior, sliders and dynamic math at 320, 390, 768,
820 and 1280 pixels. [Captured views](../../reports/solution-review/source91-final-visual-review-v1.json)
were inspected at readable resolution; viewport images show the visible parts
of long answers, while automated math/overflow checks cover every expanded box.

The selected checkpoint35 proof bundle passes the pinned Lean build and all
11,472 theorem axiom checks in 1,267 files. Its identical module/import kernel
results are reused with explicit original provenance. The expanded HTML has a
new inventory of 14,270 overlapping material units. Formal source correspondence
for rewritten answers requires a separate rebase. The historical Source90
539 complete / 6 partial / 11 pending exercise counts and 4,878 reviewed material
units remain attached to that earlier exact source version.

Installation and publication staging preserve before/after identities and
resume after interruptions. Independent failure tests cover unfinished reviews,
corrupt identities, atomic replacement failures, late edits, locks and completed
reruns. Historical failures and prior bytes are retained.

The original [review rubric](README.md) remains unchanged as the criteria used
by all independent reviews. [Release readiness](../../{READY}) records completed
local checks; actual publication evidence is recorded separately.

To repeat static integration without overwriting a report:

```sh
python3 -B book/solutions/solution_release.py check --plan-sha256 {fingerprint} --report reports/solution-review/reproduce-source91-integration-v1.json
```
'''
    overview=review.path(HISTORY+'/README.md').read_text()
    overview=overview.replace('have separate hints and worked solutions; the original 489 exercise bodies are\npreserved.', 'have separate hints and worked solutions. All 556 solutions now have independent\nmathematical and student-depth review; the exercise questions and hints are preserved.')
    overview=overview.replace('python3 book/validate28_v1.py --allow-reviewed-corrections --output reports/book/static-current.json',
        f'python3 -B book/solutions/solution_release.py check --plan-sha256 {fingerprint} --report reports/solution-review/reproduce-source91-integration-v1.json')
    overview=overview.replace('python3 verification/lean/verify.py --output reports/book/lean-verification\n','')
    overview=overview.replace('`book/validate28_v1.py` checks static links, navigation, exercise disclosures and\npreservation of the original teaching pages.', '`book/solutions/solution_release.py check` checks static links, navigation, disclosures,\nall selected solutions and the exact protected-byte preservation chain.')
    marker='The [continuing coverage audit](reports/full-coverage/README.md) verifies'
    assert marker in overview
    overview=overview.split(marker)[0]+'''The [worked-solution release](book/solutions/RELEASE.md) reviews all 556 solutions:
251 are expanded and 305 retained. Full-site reader and rendered-math checks pass.
The selected proof audit passes 11,472 theorems in 1,267 files with the new asset
fingerprints. The current working Lean tree also contains unselected future
proofs; use the selected Source91 runtime to reproduce this exact bundle.

Checkpoint35 is published and delivered at content `069532b7` and metadata
`36b715de`. Its Source90 formal coverage remains historical: 539 complete,
6 partial and 11 pending exercises, with 7,896 pending material units.
Expanded-answer formal correspondence requires a separate rebase. Publication
of the reviewed Source91 answers is recorded separately in the
[progress ledger](book/coverage/progress.json).
'''
    continuation=f'''# Continue full mathematical coverage

The student solution release has independent approval for all 556 exercises:
251 expanded, 305 retained. Actual installation, authored integration, all 29-page
reader QA and the selected proof audit pass. See
`../solutions/RELEASE.md` and `../../{READY}` for exact evidence.
Source91 publication is pending its actual commit, push, Pages jobs and live hashes.

Checkpoint35 delivery is complete at content `069532b7` / metadata `36b715de`.
Its exact Source90 audit verifies 11,472 theorems in 1,267 selected files and historical
coverage 539 complete / 6 partial / 11 pending exercises; 4,878 reviewed / 7,896 pending
material units. All earlier proofs, owner decisions and failure evidence remain.

Source91 changes solution explanations and adds an inventory of 14,270 overlapping
material units. The selected proof statements remain unchanged and pass their
native build/kernel-provenance/axiom audit. HTML-to-proof mappings for rewritten
answers require explicit rebase before new coverage claims. Retain the Source90
inventory and owner ledgers as historical evidence; do not simply replace their
source hashes with Source91 hashes. The 17 old incomplete exercise families and
unselected checkpoint36 work also remain to be completed.

The project root is not a Git repository. Publication uses
`../../reports/book/publication-repo`. Native commands use
`checks/checkpoint35-root/record_native35.py`; failed or unfinished attempts require
fresh names. `book/solutions/solution_release.py apply` accepts each target only
at its recorded before/after SHA and saves atomic per-file completion receipts.
The completed Source91 plan SHA is `{fingerprint}`.

Actual verification runs in
`../../reports/solution-review/runtime-source91-selected35-v1` with exactly the
selected 1,267 proofs and 31 site assets. Runtime cache symlinks and immutable hardlinked
objects stay local. The working canonical proof folder retains 11 unselected files.
Never copy prior snapshots, recursive archives or .lake caches into publication.
Final device-bloat cleanup remains due after full mathematical coverage and final
publication. Pipeline recovery is tested; client/application crash causes remain
undiagnosed.
'''
    coverage=review.path(HISTORY+'/reports/full-coverage/README.md').read_text()
    coverage='''# Formal coverage and worked solutions

The current teaching pages are Source91. All556 solutions have independent
mathematical/student-depth review; 251 are expanded and 305 retained. Actual rendered,
reader and selected-proof checks pass. See [the solution release](../../book/solutions/RELEASE.md).
Source91 formal correspondence for rewritten answers awaits an explicit rebase.

The following checkpoint35 counts and reports describe its historical Source90
bytes. Its delivery is complete at `069532b7` / `36b715de`; see
[the actual delivery receipt](publication35-finish-v1.json).

'''+coverage
    lean=review.path(HISTORY+'/verification/lean/README.md').read_text()
    lean='''The reviewed Source91 solution release has a separate selected-proof runtime
at `reports/solution-review/runtime-source91-selected35-v1`. It contains exactly
the same 1,267 selected checkpoint35 proof sources with new 31 asset hashes. The actual
build and all 11,472 axiom checks pass; unchanged module/import kernel evidence is
reused with its original command, workdir and logs. The source-correspondence rebase
for expanded answers remains pending. The canonical working folder retains
11 unselected future files; use the selected runtime for this exact audit.

'''+lean
    bodies={'README.md':overview.encode(),'book/coverage/progress.json':(json.dumps(progress,indent=2)+'\n').encode(),
            'book/coverage/CONTINUATION.md':continuation.encode(),'reports/full-coverage/README.md':coverage.encode(),
            'verification/lean/README.md':lean.encode(),'book/solutions/RELEASE.md':release_doc.encode()}
    # Save all original documents before the first edit, then accept only
    # exact original/selected bytes on both an initial run and a resumed run.
    for name,data in bodies.items():
        path=review.path(name)
        original=review.path(HISTORY+'/'+name).read_bytes() if name in doc_names else None
        assert (path.read_bytes() if path.exists() else None) in (original,data), 'Unplanned document edit: '+name
    for name,data in bodies.items():
        path=review.path(name);path.parent.mkdir(parents=True,exist_ok=True)
        original=review.path(HISTORY+'/'+name).read_bytes() if name in doc_names else None
        observed=path.read_bytes() if path.exists() else None
        assert observed in (original,data), 'Document edited after preflight: '+name
        if observed!=data:release.atomic_copy(path,data)
    evidence={'status':'passed_source91_completed_local_checks_and_documentation','release_ready':review.ref(READY),
              'helper':review.ref(Path(__file__).relative_to(review.ROOT).as_posix()),'documents':[review.ref(n) for n in bodies],
              'preserved_document_sources':[review.ref(HISTORY+'/'+n) for n in doc_names],
              'formal_coverage_promoted':False,'actual_publication_claimed':False}
    review.json_put('reports/solution-review/source91-documentation-v1.json',evidence)
    print(json.dumps({'status':evidence['status'],'counts':plan['counts'],'ready':review.ref(READY)}))


if __name__=='__main__':main()

"""Write honest current-source documentation after all installation/audit gates."""
from pathlib import Path
import copy
import json
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h
from solution_release import atomic_copy
sys.path.insert(0,str(ROOT/'book/coverage/source91-piece01'))
import common as c

BASE='book/solutions/releases/source92-opening-v1'
HISTORY='reports/solution-review/source92-recovery-history-v1'
AUDIT='reports/solution-review/runtime-source92-piece02-v1/reports/lean-verification/verification.json'
READY='reports/solution-review/source92-recovery-ready-v1.json'


def main():
    plan,installed,rebased,audit=map(h.read,[BASE+'/plan-v1.json',BASE+'/installation-v1.json',BASE+'/formal-rebase-v1.json',AUDIT])
    assert installed['status']=='passed_installed_source92_opening_solution_only_changes'
    assert rebased['status']=='passed_exact_source92_piece01_piece02_rebase'
    assert audit['status']=='passed' and audit['source_sha256']==plan['site_after_sha256']
    assert audit['proof_file_count']==1272 and audit['theorem_count']==11522
    for name,digest in audit['source_sha256'].items():assert h.ref(name)['sha256']==digest
    browser=h.read(BASE+'/reader-QA-v1.json')
    assert len(browser)==18 and all(r['status']=='passed' and not r['errors'] for r in browser)
    assert all(r['source_sha256']==audit['source_sha256']['SafeLearning/'+r['file']] for r in browser)
    natives=['reports/solution-review/source92-installation-native-v1.json','reports/solution-review/source92-reader-QA-native-v1.json',
             'reports/solution-review/source92-selected-audit-native-v1.json','reports/solution-review/source92-formal-rebase-native-v1.json',
             'reports/solution-review/source92-arithmetic-native-v1.json']
    for name in natives:
        n=h.read(name);assert n['status']=='passed' and n['actual_exit_code']==0
        assert n['helper_sha256_before']==n['helper_sha256_after']
        assert h.ref(n['log'])['sha256']==n['log_sha256']
    visual=[]
    for shot in h.read(BASE+'/opening-capture-v1.json')['shots']:
        visual.append({**shot,'image':h.ref(shot['path']),'inspected_by':'/root',
            'result':'Readably inspected at original resolution. Prose, table rows and solution controls fit; long display formulas use the existing horizontal math scroll regions.'})
    h.json_put(BASE+'/opening-visual-review-v1.json',{'status':'inspected_four_actual_phone_openings',
        'plan':h.ref(BASE+'/plan-v1.json'),'shots':visual,'all18_pages_visually_inspected_claimed':False})
    names=['README.md','book/solutions/RELEASE.md','book/coverage/CONTINUATION.md','reports/full-coverage/README.md',
           'verification/lean/README.md','book/coverage/progress.json']
    for name in names:c.put(HISTORY+'/'+name,c.path(name).read_bytes())
    progress=c.read(HISTORY+'/book/coverage/progress.json')
    progress['current_site_source_version']='Source92: 56 further opening-solution expansions; 113 exercise-specific assessments'
    progress['current_source_inventory']=h.ref(BASE+'/source92-inventory/inventory.json')
    progress['source92_solution_refresh']={'status':'locally_complete_delivery_pending','counts':plan['counts'],
        'plan':h.ref(BASE+'/plan-v1.json'),'installation':h.ref(BASE+'/installation-v1.json'),
        'reader_QA':h.ref(BASE+'/reader-QA-v1.json'),
        'all_current556_independently_reviewed_claimed':False,
        'review_provenance':plan['review_provenance']}
    progress['solution_depth_requirement']['source91_historical_completion']=copy.deepcopy(progress['solution_depth_requirement'])
    progress['solution_depth_requirement'].update(status='source92_opening_refresh_locally_complete_delivery_pending',
        current_release=progress['source92_solution_refresh'],all_current556_independently_reviewed_claimed=False)
    progress['current_selected_proof_audit']=h.ref(AUDIT)
    progress['current_selected_proof_audit_scope']='Source92: 1272 files / 11522 theorems. 27 exact mathematical clauses and 12 complete leaves rebased; no complete whole exercise credit.'
    prior=copy.deepcopy(progress['formal_coverage_piecewise_work'])
    progress['formal_coverage_piecewise_work'].update(source_version='Source92',status='in_progress',current_piece=2,
        current_piece_publication='pending',selected_proof_files=1272,selected_public_theorems=11522,
        new_reviewed_proved_clauses=15,new_complete_leaf_units=5,new_complete_whole_exercises=0,
        current_source_rebase=h.ref(BASE+'/formal-rebase-v1.json'),previous_piece01=prior,
        next_piece='Part(ii) numerical warning: model CDF rounding and underflow; then part(iii) numerical enclosures and joint-failure interpretation.')
    progress['formal_coverage_piecewise_work']['completed_local_pieces'].append(h.ref('reports/full-coverage/source91-piece02/completion-v1.json'))
    progress['publication_status']='Source92_openings_and_formal_piece02_locally_verified_delivery_pending'
    header='''# Current Source92 recovery checkpoint

The recovered solution pass reviews **113 exercises** and expands **56 answers**:
all 50 exercises in Primer 0, the first three in each other primer, and the first
three actual document-order exercises on each non-primer exercise page. Questions,
hints, anchors, scripts, retained answers and all other page bytes are preserved.
All 18 changed pages pass reader/rendered-math checks at 320–1280 pixels.
See the [release and review provenance](../../book/solutions/releases/source92-opening-v1/README.md).

The selected Source92 audit passes **1,272 files and 11,522 theorems**. Formal
piece02 adds 14 theorem bodies, **15 mathematical clauses and five complete
source leaves**. Exact unchanged-byte rebase retains piece01 too: 27 clauses
and 12 complete leaves in the current source, with **zero complete whole-exercise
credit**. Exercise 1.5 remains partial. The mixed erfc paragraph still needs a
numerical model for CDF rounding and tail underflow; part (iii) remains pending.
See the [current rebase](../../book/solutions/releases/source92-opening-v1/formal-rebase-v1.json).

Compilation, kernel replay and the all-theorem axiom audit verify encoded
statements. They do not make unreviewed source scopes complete. Actual delivery
is recorded separately. The earlier Source91/Source90 reports below are history.

'''
    continuation='''# Continue from Source92, one formal piece at a time

The crash recovery is locally verified. 113 opening exercises were reassessed
and 56 solutions expanded. All 50 Primer0 exercises were included. All 556
questions/hints and every unselected solution preserve their exact prior bytes.
See `../solutions/releases/source92-opening-v1/README.md` for review provenance.

Exercise 1.5(i) retains 12 reviewed clauses and seven complete leaves. Piece02
adds 15 mathematical clauses and five complete leaves from part(ii). The exact
whole exercise and reviewed fragments are unchanged in Source92; both mappings
are rebased in `../solutions/releases/source92-opening-v1/formal-rebase-v1.json`.
The Source92 selected audit passes 1,272 files / 11,522 theorems, including the
14 new part(ii) theorem bodies. Zero whole exercises become complete.

Next: the mixed part(ii) erfc paragraph needs a genuine numerical model deriving
CDF rounding to one and tail underflow from actual positive Gaussian tails.
Real-valued positivity alone does not prove a floating-point implementation.
Then treat part(iii)'s numerical enclosures and joint-failure interpretation.
All parent scopes and full formal coverage remain pending. Historical Source90
539 complete / 6 partial / 11 pending totals are not current Source92 counts.

Canonical proof sources retain unselected work. Use the exact frozen workspace
runtime `../../reports/solution-review/runtime-source92-piece02-v1` for the current
audit. Publication contains only the selected proofs at their normal paths.
Fresh native attempt names preserve interrupted and failed evidence.

Delivery is separate from local completion. Publication checkout:
`../../reports/book/publication-repo`. Final device cleanup remains due after
full formal coverage and final publication. Keep unique unpublished evidence;
do not copy .lake caches or source-archive trees into publication.
Client/application crash causes remain undiagnosed.
'''
    release='''# Source92 opening solutions

**113 exercises are reassessed; 56 solutions receive further step-by-step
expansions and 57 are retained.** The pass includes all 50 Primer0 exercises and
the first three actual document-order exercises on every other exercise page.
All 556 questions, hints, exercise order, anchors and scripts are preserved.
Every unselected and retained answer keeps its exact Source91 bytes.

The [current release](releases/source92-opening-v1/README.md) records actual
installation, 18-page reader/rendered-math checks, arithmetic checks and review
provenance. The prior Source91 release independently reviewed all 556 solutions
and expanded 251. In this recovery, 35 saved replacements receive a separate
recovery review; 21 newly authored replacements are explicitly self-reviewed.
The release does not claim a new independent review of all current 556 bodies.

Formal piece02 adds 14 theorem bodies about actual Gaussian tails, indicator
count expectations, zero-noise cases and erfc. The selected Source92 audit passes
1,272 files / 11,522 theorems. Exact unchanged Exercise1.5 fragments retain and
extend correspondence to 27 mathematical clauses and 12 complete leaves, with
zero complete whole-exercise credit. The floating-point warning and part(iii)
remain pending. Source90 totals remain historical.

Actual publication/delivery is tracked separately in
`../../reports/solution-review/source92-delivery-v1.json` when confirmed.
'''
    current_readme='''# Source92 opening review and formal recovery

The interrupted pass is complete locally: **65 primer + 48 non-primer exercises**
reviewed, **56 replacements + 57 retained answers**. Primer0 is reviewed in full;
elsewhere the selection is the first three actual DOM exercises. All 556 questions,
hints and unselected solutions, authoring mirrors, anchors, scripts and all other
page bytes are preserved. [Plan](plan-v1.json) and [installation](installation-v1.json)
bind exact before/after identities and retain rationale for every selected answer.

The earlier Source91 release independently reviewed all 556 solutions. This
recovery separately reviews 23 module and 12 primer drafts saved before the crash.
The 21 additional recovery-authored replacements are explicitly self-reviewed;
no independent second-agent review is claimed for those new bodies. Retained and
unselected bodies keep their exact previous independent-review lineage.

[Reader QA](reader-QA-v1.json) passes every changed page at 320, 390, 768, 820 and
1280 pixels, including expanded disclosures, dynamic math, links, navigation,
print behavior and slider smoke checks. Four actual phone openings were inspected
at original resolution; this is not a claim to have visually inspected every
captured page. [Arithmetic](arithmetic-v1.json) recomputes worked values; finite
checks alone do not prove universal mathematical statements.

The Source92 selected audit is in
`../../../../reports/solution-review/runtime-source92-piece02-v1/reports/lean-verification/verification.json`.
It passes 1,272 files / 11,522 theorem axiom checks. Part(ii)'s 14 new bodies
received a fresh kernel replay in the original Source91 piece02 audit; the final
Source92 audit reuses only identical proof/import/dependency identities and runs
the aggregate build and every theorem axiom check again.

[Exact unchanged-source rebase](formal-rebase-v1.json) preserves part(i) and the
new part(ii) mapping: 27 mathematical clauses and 12 complete leaves. Exercise1.5
and all parent scopes remain partial; rounding/underflow and part(iii) are pending.
Opening rewrites receive zero automatic formal-completion credit.

Workspace installed-preservation reproduction:

```sh
python3 -B book/solutions/releases/source92-opening-v1/recover_release.py check --plan-sha256 101854993fd3cb88625c5bbe3ebe78f09b65fd41bc5c628451818ce235c3878b
```

For the exact frozen workspace Lean audit, run `verify.py` in
`reports/solution-review/runtime-source92-piece02-v1/verification/lean` with a
fresh output directory. In the published checkout the selected proofs are at
`verification/lean`; run `lake exe cache get` and `python3 verify.py --output
../../reports/source92-reproduction` there. Omitting reuse replays every module.
Actual commit/push/Pages/live hashes are recorded separately after delivery.
'''
    root_readme=c.path(HISTORY+'/README.md').read_text()
    root_readme=root_readme.replace('# SafetyBased: Safe Learning study notes\n', '# SafetyBased: Safe Learning study notes\n\nCurrent recovery: **56 further step-by-step solution expansions across 113 reviewed openings**.\nThe selected Source92 Lean audit passes **11,522 theorems in 1,272 files**.\nExercise 1.5 remains formally partial. See the [current release](book/solutions/releases/source92-opening-v1/README.md)\nand [formal continuation](book/coverage/CONTINUATION.md). Earlier Source91/Source90 counts below are historical.\n')
    root_readme=root_readme.replace('All 556 solutions now have independent', 'The Source91 release gave all 556 solutions independent')
    root_readme=root_readme.replace('The current selected\nproof audit passes', 'The earlier Source91 selected\nproof audit passed')
    root_readme=root_readme.replace('The working Lean tree retains eight unselected future modules;', 'The working Lean tree retains unselected future modules;')
    lean_header='''# Current Source92 selection

The current frozen workspace runtime is
`../../reports/solution-review/runtime-source92-piece02-v1`.
It audits 1,272 selected files / 11,522 theorems. The published checkout has
those selected sources at their normal paths. Exercise1.5 correspondence covers
27 mathematical clauses and 12 complete leaves; the exercise remains partial.
See `../../book/solutions/releases/source92-opening-v1/formal-rebase-v1.json`.
Older source/version counts below describe their historical snapshots.

'''
    bodies={'README.md':root_readme,'book/solutions/RELEASE.md':release,
        'book/coverage/CONTINUATION.md':continuation,
        'reports/full-coverage/README.md':header+c.path(HISTORY+'/reports/full-coverage/README.md').read_text().replace('# Current Source91 formal piece 01','# Historical Source91 formal piece 01',1),
        'verification/lean/README.md':lean_header+c.path(HISTORY+'/verification/lean/README.md').read_text(),
        'book/coverage/progress.json':json.dumps(progress,indent=2)+'\n'}
    for name,body in bodies.items():
        raw=body.encode();assert c.path(name).read_bytes() in (c.path(HISTORY+'/'+name).read_bytes(),raw)
    for name,body in bodies.items():
        if c.path(name).read_bytes()!=body.encode():atomic_copy(c.path(name),body.encode())
    h.put(BASE+'/README.md',current_readme.encode())
    c.put('book/coverage/source91-piece02/README.md',b'''# Source91 formal piece02

15 mathematical clauses and five complete leaves in Exercise1.5(ii) pass
independent correspondence review and an actual selected Lean build, a fresh
kernel replay of the new module and all 11,522 theorem axiom checks.
The mixed numerical-warning leaf, part(iii), whole exercise and parent scopes
remain partial/pending. Zero whole exercises become complete.

`ledger-v1.json` and `../../../reports/full-coverage/source91-piece02/completion-v1.json`
record the exact historical Source91 bytes. Current Source92 correspondence is
rebased by exact unchanged exercise and leaf bytes in
`../../solutions/releases/source92-opening-v1/formal-rebase-v1.json`.
The audit contains 1,272 selected modules, including 14 new theorem bodies.
Actual delivery is recorded separately. Full formal coverage remains in progress.
''')
    h.json_put(READY,{'status':'passed_installed_source92_openings_and_partial_formal_piece02_ready',
        'plan':h.ref(BASE+'/plan-v1.json'),'installation':h.ref(BASE+'/installation-v1.json'),
        'reader_QA':h.ref(BASE+'/reader-QA-v1.json'),'arithmetic':h.ref(BASE+'/arithmetic-v1.json'),
        'formal_rebase':h.ref(BASE+'/formal-rebase-v1.json'),'selected_audit':h.ref(AUDIT),
        'native_executions':[h.ref(n) for n in natives],'documents':[c.ref(n) for n in bodies]+[h.ref(BASE+'/README.md')],
        'counts':plan['counts'],'proof_files':1272,'theorems':11522,
        'full_formal_coverage_complete':False,'current_exercise_status':'partial',
        'publication_status':'pending_actual_commit_push_and_delivery'})
    print({'status':'ready','expanded':56,'reassessed':113,'formal_coverage':'partial'})


if __name__=='__main__':main()

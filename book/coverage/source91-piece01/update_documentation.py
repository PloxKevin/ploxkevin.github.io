"""Document the actual completed piece while preserving the historical coverage."""
import common as c
import finish_piece
import sys

sys.path.insert(0, str(c.ROOT/'book/solutions'))
from solution_release import atomic_copy

HISTORY = 'reports/full-coverage/source91-piece01/history/before-piece01-readmes-v1'


def main():
    completed = c.read(finish_piece.REPORT)
    assert completed['status'] == 'passed_source91_piece01_twelve_clauses_seven_leaves_whole_exercise_partial'
    assert completed['proof_files'] == 1271 and completed['public_theorems'] == 11508
    for key in ['ledger', 'independent_source_review', 'audit_export']:
        c.exact(completed[key])
    names = ['README.md', 'verification/lean/README.md', 'reports/full-coverage/README.md']
    for name in names:
        if not c.path(HISTORY+'/'+name).exists():
            c.put(HISTORY+'/'+name, c.path(name).read_bytes())
    original = {n:c.path(HISTORY+'/'+n).read_text() for n in names}

    old = '''The selected proof audit passes 11,472 theorems in 1,267 files with the new asset
fingerprints. The current working Lean tree also contains unselected future
proofs; use the selected Source91 runtime to reproduce this exact bundle.'''
    new = '''Source91 formal piece 01 checks **Exercise 1.5(i)** in the Landscape module:
12 mathematical clauses and seven complete direct leaf units. The whole exercise
remains partial, with parts (ii) and (iii) still pending. The current selected
proof audit passes **11,508 theorems in 1,271 files**: four fresh kernel replays,
1,267 exact prior reuses, a fresh aggregate build and every theorem's axiom audit.
See the [piece ledger](book/coverage/source91-piece01/ledger-v1.json) and
[reproduction and next step](book/coverage/source91-piece01/README.md).
The working Lean tree retains eight unselected future modules; use the frozen
`reports/full-coverage/runtime-source91-piece01-v1` runtime for this exact audit.
The published checkout contains only the selected proofs at their normal paths.'''
    assert original['README.md'].count(old) == 1
    root = original['README.md'].replace(old, new)

    lean = original['verification/lean/README.md']
    start = lean.index('# Safe Learning: local Lean verification')
    lean = '''Source91 formal piece 01 closes **Exercise 1.5(i)** in the Landscape module:
12 mathematical clauses and seven complete direct leaf units, with zero newly
complete whole exercises. Parts (ii)/(iii) and the containing answer/exercise
remain pending. The actual selected bundle has **1,271 files / 11,508 theorems**,
36 newly selected theorem bodies, four fresh kernel replays and 1,267 exact prior
kernel reuses. The aggregate build and every theorem's standard-axiom audit pass.
See [the exact current ledger](../../book/coverage/source91-piece01/ledger-v1.json)
and [native audit](../../reports/full-coverage/source91-piece01/lean-audit/verification-original.json).

The current Source91 inventory has 556 exercises and 14,270 overlapping material
units. Only this exact piece has new current-source completion credit; other
correspondence awaits explicit rebase/review. All 556 student solutions remain
independently depth-reviewed. The historical Source90 counts below remain attached
to their original ledgers and bytes.

Use `reports/full-coverage/runtime-source91-piece01-v1` for the workspace audit.
The canonical working tree retains eight unselected future modules, which the
selected aggregate does not import. In a clean published checkout exactly the
selected sources and aggregate occupy their normal paths, so the reproduction
command below applies directly. This piece's actual commit/push/Pages/live
receipt is recorded separately; full formal coverage remains in progress.

''' + lean[start:]
    lean = lean.replace('Its current selected batch contains 11,472 theorems in 1,267 files.',
                        'Its historical Source90 checkpoint35 batch contains 11,472 theorems in 1,267 files.')
    lean = lean.replace('The inventory contains 556 exercises and 12,774 overlapping material units.',
                        'The historical Source90 inventory contains 556 exercises and 12,774 overlapping material units.')
    lean = lean.replace('and its default\naggregate is not the selected checkpoint35 runtime.',
                        'and its selected piece01\naggregate differs from the historical checkpoint35 runtime.')

    full = original['reports/full-coverage/README.md']
    full = full.replace('Source91 formal correspondence for rewritten answers awaits an explicit rebase.',
                        'Source91 formal correspondence advances in bounded pieces described below.')
    full = full.replace('The publication metadata will be committed and\nchecked separately; formal correspondence for expanded answers remains pending.',
                        'Metadata delivery at `54a8fac0` is complete; see\n[the actual final receipt](../solution-review/source91-publication-finish-v1.json).')
    header = '''# Current Source91 formal piece 01

**Exercise 1.5(i)** in the Landscape module has independent correspondence review
for 12 mathematical clauses and seven complete direct leaf units. Its exact
[ledger](../../book/coverage/source91-piece01/ledger-v1.json) closes only part (i):
zero newly complete whole exercises. Parts (ii)/(iii) and parent scopes remain
pending. Full formal coverage is still in progress.

The selected native audit passes **1,271 proof files and 11,508 theorems**,
including 36 newly selected theorem bodies, four fresh kernel replays and 1,267
exact prior reuses. The aggregate build and all-theorem standard-axiom audit run
again. See the [unaltered actual report](source91-piece01/lean-audit/verification-original.json),
[native execution](source91-piece01/selected-audit-native-v1.json) and
[completed local scope](source91-piece01/completion-v1.json).

Source91 has 556 exercises and 14,270 overlapping material units. Only the exact
piece above has new current-source completion credit; all other entries need
explicit rebase or review. All 556 worked solutions remain independently
student-depth reviewed (251 expanded, 305 retained), and all 31 reader assets
stay unchanged in this formal piece. Historical Source90 totals below are
preserved with their own original source and owner ledgers.

The workspace audit runs in `runtime-source91-piece01-v1`; a published checkout
contains the selected sources at their normal paths. Reproduction instructions,
interruption history and the next part (ii) scope are in
[the piece instructions](../../book/coverage/source91-piece01/README.md).
Actual publication and live delivery are recorded separately from proof completion.

'''
    bodies = {'README.md':root.encode(), 'verification/lean/README.md':lean.encode(),
              'reports/full-coverage/README.md':(header+full).encode()}
    for name, data in bodies.items():
        assert c.path(name).read_bytes() in (original[name].encode(), data), name
    for name, data in bodies.items():
        assert c.path(name).read_bytes() in (original[name].encode(), data), name
        if c.path(name).read_bytes() != data:
            atomic_copy(c.path(name), data)
    assert all(c.path(n).read_bytes() == b for n,b in bodies.items())
    c.json_put('reports/full-coverage/source91-piece01/readmes-v1.json',
        {'status':'passed_exact_current_piece01_readmes', 'completion':c.ref(finish_piece.REPORT),
         'documents':[c.ref(n) for n in names], 'originals':[c.ref(HISTORY+'/'+n) for n in names],
         'formal_coverage_complete':False})
    print({'status':'passed_exact_current_piece01_readmes'})


if __name__ == '__main__':
    main()

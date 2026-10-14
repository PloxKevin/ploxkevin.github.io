"""Bind actual checks, manual self-review and unchanged formal scopes to Source93."""
import copy
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h
from foundation_content import EXERCISES

BASE='book/solutions/releases/source93-foundations-v1'
AUDIT='reports/solution-review/runtime-source93-foundations-v1/reports/lean-verification/verification.json'


def main():
    inventory=h.read(BASE+'/source93-inventory/inventory.json')
    installed=h.read(BASE+'/installation.json')
    audit=h.read(AUDIT)
    native=h.read('reports/solution-review/source93-lean-native-v1.json')
    assert audit['status']=='passed' and audit['proof_file_count']==1272 and audit['theorem_count']==11522
    assert native['actual_exit_code']==0 and native['status']=='passed'
    preparation=h.read(BASE+'/runtime-preparation.json')
    assert audit['source_sha256']==preparation['site_sha256']
    assert audit['proof_sha256']==preparation['proof_sha256']
    for name,digest in audit['source_sha256'].items():assert h.ref(name)['sha256']==digest
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in audit['axiom_dependencies'].values())
    assert h.read(BASE+'/arithmetic-check.json')['status']=='passed'
    assert h.read(BASE+'/book-integration.json')['status']=='PASS'
    browser=h.read('reports/solution-review/source93-installed-browser-v1.json')[0]
    assert browser['status']=='passed' and not browser['errors'] and browser['exerciseCounts']['total']==80
    assert browser['source_sha256']==audit['source_sha256']['SafeLearning/primer-basics.html']
    check=h.read('reports/solution-review/source93-check-mjs-v1.json')[0]
    assert not any(check[k] for k in ('consoleErrors','pageErrors','leftoverDollar','katexErrors','missingAnchors','brokenLinks','mobileOverflow','mobileOverflowExpanded'))

    # Actual manual inspection: eight captured practice panels and two PDF pages.
    visual=h.read('reports/solution-review/source93-practice-visual-v1/manifest.json')
    assert len(visual['shots'])==8 and visual['source_sha256']==browser['source_sha256']
    images=[]
    for row in visual['shots']:
        assert h.ref(row['path'])['sha256']==row['sha256']
        images.append(dict(artifact=h.ref(row['path']),exercise=row['exercise'],width=row['width'],
                           observation='Problem, separate hint and full solution are readable; step labels, mathematical notation and paragraph wrapping match the exercise.'))
    for name,page in [('print-page4.png',4),('print-page100.png',100)]:
        images.append(dict(artifact=h.ref('reports/solution-review/source93-practice-visual-v1/'+name),pdf_page=page,
                           observation='Complete worked answer is readable on A4; fractions/table, step sequence and review link are retained.'))
    h.json_put(BASE+'/visual-review.json',dict(status='passed_selected_actual_visual_samples',source=h.ref('SafeLearning/primer-basics.html'),
        image_reviews=images,automatic_browser=h.ref('reports/solution-review/source93-installed-browser-v1.json'),
        limits='Manual inspection covers eight practice panels and two of the 155 print pages. Whole-page expanded layout and rendering are checked automatically. Wide display mathematics uses the existing horizontal scroll container on narrow screens. No claim of inspecting every print page by eye.'))

    # Exercise-specific checks are bound to the actual solutions, with the review
    # explicitly attributed to this author rather than an invented peer agent.
    arithmetic=h.read(BASE+'/arithmetic-check.json')
    notes=[]
    extra_codes={e['code'] for e in EXERCISES}
    for row in arithmetic['exercise_checks']:
        notes.append(dict(label=row['label'],solution_sha256=row['solution_sha256'],
            review_mode='author_self_review',
            scope='New guided exercise' if row['exercise'].split('0.',1)[-1] in extra_codes else 'Expanded existing answer',
            checked_calculation=row['check'],
            verdict='approved_after_domain_logic_boundary_and_explanation_review'))
    assert len(notes)==80
    h.json_put(BASE+'/mathematical-self-review.json',dict(status='passed_author_self_review',
        source=h.ref('SafeLearning/primer-basics.html'),exercises=notes,
        reviewed_argument_obligations=[
            'Membership versus subset; distinct objects; empty-set vacuity and complement universe.',
            'Quantifier choice order, permitted dependencies, admissible witnesses and strict negations.',
            'Domains/codomains; image witnesses in both directions; preimage versus inverse and zero-denominator cases.',
            'Direct proof, equivalence, counterexample premises, integer witnesses, base cases and noncircular induction.',
            'Finite-sum indexing, positive multipliers, geometric tails, convergence witnesses and sharp integer boundaries.',
            'Upper/lower bound tightness versus attainment, argmin types, parity tails and both minimax choice orders.',
            'Ambient topology, nonempty-domain theorem assumptions, epsilon-delta choices and bounded/global Lipschitz distinctions.',
            'Asymptotic ratios versus finite work, sufficient versus actual stopping budgets and permanent late thresholds.',
            'Sensor/model assumptions, disturbance timing, interval containment and exact actuator disturbance limits.',
            'Cosine monotonicity, contraction hypotheses, logarithm sign reversal and rigorous interval versus rounded numerical estimates.'
        ],arithmetic=h.ref(BASE+'/arithmetic-check.json'),
        independent_review_claimed=False,
        limits='Author mathematical and pedagogical self-review; no new independent agent review, student comprehension study or complete Lean correspondence is claimed.'))

    # Landscape is byte-identical, so all source offsets and unit keys there
    # remain exact even though Block 0 ordinals have moved.
    old_inventory=h.read('book/solutions/releases/source92-opening-v1/source92-inventory/inventory.json')
    old_units={r['key']:r for r in old_inventory['material_source_units']}
    new_units={r['key']:r for r in inventory['material_source_units']}
    landscape=h.path('SafeLearning/landscape.html').read_bytes()
    baseline=h.read(BASE+'/baseline-source92/manifest.json')['files']['SafeLearning/landscape.html']
    assert h.sha(landscape)==baseline['sha256']
    old_ex=next(r for r in old_inventory['exercises'] if r['key']=='landscape.html::exercise-19')
    new_ex=next(r for r in inventory['exercises'] if r['key']==old_ex['key'])
    assert old_ex['source_text']==new_ex['source_text'] and old_ex['text_sha256']==new_ex['text_sha256']
    ledgers=[]
    for number,field in [(1,'complete_leaf_material_units'),(2,'source_units')]:
        prior='book/solutions/releases/source92-opening-v1/formal-rebase-piece'+str(number)+'-v1.json'
        ledger=copy.deepcopy(h.read(prior))
        assert ledger['reader_source']==h.ref('SafeLearning/landscape.html')
        for unit in ledger[field]:
            key=unit['key']
            assert old_units[key]['text_sha256']==new_units[key]['text_sha256']==unit['exact_text_sha256']
            assert h.sha(landscape[unit['start_byte']:unit['end_byte']])==unit['exact_html_sha256']
        ledger.update(source_version='Source93',status='partial_current_source93_exact_correspondence',
            inventory=h.ref(BASE+'/source93-inventory/inventory.json'),audit=h.ref(AUDIT),
            previous_exact_source_ledger=h.ref(prior),
            reader_source_snapshot=baseline,
            rebase=dict(method='Whole landscape page byte-identical; exercise body, all leaf texts, HTML ranges and inventory keys verified against Source92.',
                        new_formal_completion_credit=0),native_execution=h.ref('reports/solution-review/source93-lean-native-v1.json'))
        name=BASE+'/formal-rebase-piece'+str(number)+'.json';h.json_put(name,ledger);ledgers.append(h.ref(name))
    h.json_put(BASE+'/formal-rebase.json',dict(status='passed_exact_source93_unchanged_landscape_rebase',
        inventory=h.ref(BASE+'/source93-inventory/inventory.json'),audit=h.ref(AUDIT),ledgers=ledgers,
        unchanged_scope_counts=dict(proved_mathematical_clauses=27,complete_leaf_units=12,complete_whole_exercises=0),
        exercise_status='partial',part_ii_status='partial_numerical_warning_leaf_pending',
        new_foundations_formal_credit=0,full_formal_coverage_complete=False))
    current_primers={r['label']:r for r in inventory['exercises'] if r['source']=='SafeLearning/primer-basics.html'}
    old_primers={r['label']:r for r in old_inventory['exercises'] if r['source']=='SafeLearning/primer-basics.html'}
    mapping=[]
    for label,row in current_primers.items():
        old=old_primers.get(label)
        mapping.append(dict(label=label,current_key=row['key'],previous_key=old['key'] if old else None,
            question_retained=bool(old),formal_status='expanded_answer_correspondence_pending' if old else 'new_exercise_correspondence_pending',
            new_complete_exercise_credit=0))
    assert len(mapping)==80 and sum(r['question_retained'] for r in mapping)==50
    h.json_put(BASE+'/foundation-formal-status.json',dict(status='explicit_pending_new_or_expanded_correspondence',
        inventory=h.ref(BASE+'/source93-inventory/inventory.json'),exercises=mapping,
        new_exercises=30,expanded_old_answers=50,new_formal_credit=0,
        old_ordinal_keys_must_not_be_carried_by_position=True,
        limits='Compilation of unchanged Lean declarations does not automatically validate new explanations or shifted exercise positions. The remaining 506 exercises have unchanged reader bytes; their previous source-specific lineage is retained, without a new book-wide completion count.'))
    h.json_put(BASE+'/ready.json',dict(status='passed_ready_for_exact_source93_publication',
        source_version='Source93',primer0_exercises=80,book_exercises=586,
        added_exercises=30,expanded_existing_solutions=50,
        checks={name:h.ref(BASE+'/'+name+'.json') for name in ('edit-plan','installation','preservation-check','arithmetic-check','mathematical-self-review','visual-review','book-integration','formal-rebase','foundation-formal-status')},
        browser=h.ref('reports/solution-review/source93-installed-browser-v1.json'),
        mandatory_browser=h.ref('reports/solution-review/source93-check-mjs-v1.json'),
        audit=h.ref(AUDIT),native_audit=h.ref('reports/solution-review/source93-lean-native-v1.json'),
        reader_assets_sha256=audit['source_sha256'],selected_proofs_sha256=audit['proof_sha256'],
        independent_review_claimed=False,full_formal_coverage_complete=False))
    print(dict(status='ready_for_publication',primer0_exercises=80,added_exercises=30,expanded_solutions=50,lean_theorems=11522))


if __name__=='__main__':main()

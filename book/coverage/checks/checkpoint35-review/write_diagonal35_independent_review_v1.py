"""Write a bounded, source-bound independent review; mutate review artifacts only."""
from pathlib import Path
from hashlib import sha256
from datetime import datetime, timezone
import json
import re

ROOT = Path(__file__).resolve().parents[4]
OUT = ROOT / 'book/coverage/checks/checkpoint35-review'


def ref(path):
    p = ROOT / path
    return {'file': path, 'sha256': sha256(p.read_bytes()).hexdigest()}


def read(path):
    return json.loads((ROOT / path).read_text())


def write(name, data):
    (OUT / name).write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')


inventory_path = 'book/coverage/inventory-after-correction90.json'
inventory = read(inventory_path)
units = {u['key']: u for u in inventory['material_source_units']}
owners = {name: read(f'book/coverage/{name}.json') for name in ['core', 'modules']}
baseline_owner_refs = {name: ref(f'book/coverage/{name}.json') for name in owners}
bridge_file = 'verification/lean/SafeLearning/CompleteModulesDiagonalQCChordBridge35.lean'
basis_file = 'verification/lean/SafeLearning/CompleteModulesDiagonalMultiplierBasis35.lean'
bridge = 'SafeLearning.CompleteModulesDiagonalQCChordBridge35.'
basis = 'SafeLearning.CompleteModulesDiagonalMultiplierBasis35.'
qc = 'SafeLearning.CompleteModulesDiagonalQC.'
base = 'SafeLearning.CompleteModulesLipSDP.'
invalid = 'SafeLearning.CompleteModulesInvalidQC.'

declarations = []
for file in [bridge_file, basis_file]:
    text = (ROOT / file).read_text()
    namespace = re.search(r'^namespace (\S+)', text, re.M)[1]
    for match in re.finditer(r'^(def|theorem)\s+(\w+)', text, re.M):
        declarations.append({'name': namespace + '.' + match[2], 'kind': match[1], 'file': file})
assert len(declarations) == 8
assert sum(d['kind'] == 'theorem' for d in declarations) == 6

actual_receipts = []
for name, file in [
    ('diagonal-qc35-standalone-execution-v2', bridge_file),
    ('diagonal-qc35-named-execution-v1', bridge_file),
    ('diagonal-basis35-standalone-execution-v2', basis_file),
    ('diagonal-basis35-named-execution-v1', basis_file),
]:
    path = f'reports/full-coverage/{name}.json'
    receipt = read(path)
    expected = ref(file)['sha256']
    assert receipt['status'] == 'passed' and receipt['actual_exit_code'] == 0
    assert receipt['helper_sha256_before'][file] == expected
    assert receipt['helper_sha256_after'][file] == expected
    assert receipt['log_sha256'] == ref(receipt['log'])['sha256']
    actual_receipts.append({**ref(path), 'actual_exit_code': 0, 'status': 'passed',
                           'log': ref(receipt['log']), 'canonical_source': ref(file)})

retained_failures = []
for name, explanation in [
    ('diagonal-qc35-standalone-execution-v1',
     'The invocation selected Lean 4.35.0 without the project environment and failed to resolve SafeLearning. The same source later compiled using the explicit Lean 4.34.1 project lake environment.'),
    ('diagonal-basis35-standalone-execution-v1',
     'The earlier source had a redundant tactic after simp closed the goal, causing No goals to be solved; unused simp arguments and Fintype also produced warnings. The current corrected source has a different hash and compiled successfully.'),
]:
    path = f'reports/full-coverage/{name}.json'
    receipt = read(path)
    assert receipt['status'] == 'failed' and receipt['actual_exit_code'] == 1
    retained_failures.append({**ref(path), 'status': 'failed', 'actual_exit_code': 1,
                              'log': ref(receipt['log']),
                              'failed_source_sha256': receipt['helper_sha256_before'],
                              'explanation': explanation})

theorem_reviews = [
    {
        'declaration': bridge + 'quotient_definition_iff_all_chords',
        'hypotheses': ['activation : R -> R', 'alpha, beta : R', 'alpha <= beta'],
        'argument': 'For unequal inputs, division by the nonzero input difference constructs the unique chord slope and cancellation reconstructs the output increment. For equal inputs, the output increment is exactly zero and the endpoint alpha is an admissible slope. Conversely an admissible chord slope cancels to the quotient for unequal inputs.',
        'edge_cases': ['Equal inputs never require division.', 'Negative input differences cause no inequality reversal: bounds are assumed on the quotient and only an equality is cancelled.', 'alpha = beta is supported; alpha > beta is excluded by the explicit hypothesis.'],
        'paper_correspondence': 'The website and arXiv v2 impose 0 <= alpha < beta < infinity. The ordered-real theorem covers that entire scope and additionally the degenerate interval; real parameters are finite.',
        'status': 'passed',
    },
    {
        'declaration': bridge + 'quotient_definition_implies_actual_block_qc',
        'hypotheses': ['Finite coordinate type K with decidable equality', 'A shared scalar activation satisfying the unequal-input quotient definition', 'alpha <= beta', 'Each multiplier coordinate is nonnegative', 'Two arbitrary vectors first, second : K -> R'],
        'argument': 'The conclusion uses the actual shared activation differences, not hypothetical hidden increments. The imported block-quadratic identity rewrites exactly to a weighted sum of coordinate scalar QCs. The quotient/chord equivalence supplies the actual chord hypothesis for each coordinate; nonnegative weights preserve the scalar inequalities.',
        'edge_cases': ['Repeated coordinate inputs contribute zero scalar QCs.', 'The empty finite type has a zero quadratic form.', 'The multiplier is diagonal by construction, not an arbitrary PSD matrix.'],
        'paper_correspondence': 'Together with diagonal_qc_matrix_is_stated_block, this is precisely arXiv v2 Lemma 1 equation (9), with T = diagonal(multiplier).',
        'status': 'passed',
    },
    {
        'declaration': bridge + 'all_actual_diagonal_qcs_imply_quotient_definition',
        'hypotheses': ['activation : R -> R', 'alpha <= beta', 'For every pair of scalar inputs and every nonnegative Fin 1 multiplier the actual scalar-coordinate diagonal QC is nonnegative'],
        'argument': 'The all-multipliers equivalence isolates the only coordinate. scalar_qc_iff_admissible_chord recovers an admissible chord, and quotient_definition_iff_all_chords yields every unequal-input quotient bound. The hypothesis uses diagonalQC rather than the block form; diagonal_qc_is_actual_block_quadratic proves those expressions are equal.',
        'edge_cases': ['The use of Fin 1 avoids a vacuous empty-coordinate converse.', 'Equal inputs recover a zero chord; the conclusion quantifies only unequal inputs.', 'Nonnegative weights include the unit coordinate selector.'],
        'paper_correspondence': 'This is a derived converse supporting the exact definition correspondence. It is not attributed as an additional theorem of Fazlyab et al.',
        'status': 'passed',
    },
    {
        'declaration': basis + 'weighted_coordinate_outer_products_are_the_diagonal_matrix',
        'hypotheses': ['Finite coordinate type K with decidable equality', 'Arbitrary real coordinate weights; no sign assumption'],
        'argument': 'coordinateVector k is Pi.single k 1, exactly the coordinate vector e_k. The entrywise proof handles equal and unequal indices, establishing sum_k weight_k e_k e_k^T = diagonal(weight) as an equality of actual matrices.',
        'edge_cases': ['Negative weights still give the algebraic diagonal identity.', 'The empty sum is the zero diagonal matrix.'],
        'paper_correspondence': 'This matches the literal coordinate outer-product sum in arXiv v2 equation (8) and in the website multiplier cone.',
        'status': 'passed',
    },
    {
        'declaration': basis + 'nonnegative_weights_are_exactly_positive_semidefinite_diagonal_matrices',
        'hypotheses': ['Coordinate type K with decidable equality', 'Real coordinate weights'],
        'argument': 'Matrix.posSemidef_diagonal_iff proves exactly that a diagonal matrix is PSD iff each coordinate weight is nonnegative. Its proof tests a unit coordinate vector in the converse. Fintype is intentionally omitted; for finite K the library finite-support definition agrees with the usual quadratic-form PSD condition.',
        'edge_cases': ['Zero entries are allowed.', 'Negative entries are excluded.', 'The theorem says nothing about admissibility of a general non-diagonal PSD multiplier.'],
        'paper_correspondence': 'This justifies the diagonal and positive semidefinite qualification of the displayed multiplier cone, in both directions.',
        'status': 'passed',
    },
    {
        'declaration': basis + 'printed_multiplier_sum_is_positive_semidefinite',
        'hypotheses': ['Finite coordinate type K with decidable equality', 'Each real weight is nonnegative'],
        'argument': 'Rewriting the printed coordinate outer-product sum by the actual matrix identity reduces directly to the diagonal PSD equivalence. No coupled outer products or arbitrary-PSD admissibility are introduced.',
        'edge_cases': ['Zero weights and zero sums are included.'],
        'paper_correspondence': 'Completes the parenthetical PSD assertion attached to the printed T sum.',
        'status': 'passed',
    },
]

qc_decls = [
    bridge + 'quotient_definition_iff_all_chords',
    bridge + 'quotient_definition_implies_actual_block_qc',
    qc + 'diagonal_qc_matrix_is_stated_block',
    qc + 'diagonal_qc_is_actual_block_quadratic',
    qc + 'diagonal_qc_from_actual_activations',
    basis + 'weighted_coordinate_outer_products_are_the_diagonal_matrix',
    basis + 'nonnegative_weights_are_exactly_positive_semidefinite_diagonal_matrices',
    basis + 'printed_multiplier_sum_is_positive_semidefinite',
]
characterization_decls = [
    qc + 'scalar_qc_factorization',
    qc + 'scalar_qc_iff_admissible_chord',
    qc + 'all_diagonal_qcs_iff_coordinate_qcs',
    qc + 'all_diagonal_qcs_iff_independent_diagonal_slopes',
    qc + 'diagonal_qc_matrix_is_stated_block',
    qc + 'diagonal_qc_is_actual_block_quadratic',
    basis + 'weighted_coordinate_outer_products_are_the_diagonal_matrix',
    basis + 'nonnegative_weights_are_exactly_positive_semidefinite_diagonal_matrices',
]
mathematical_hypotheses = [
    'Real scalar activation, shared elementwise across a finite coordinate set.',
    'The printed scope 0 <= alpha < beta < infinity implies the theorem hypothesis alpha <= beta; the proofs do not narrow the printed scope.',
    'Every unequal-input quotient belongs to [alpha, beta].',
    'T is the printed coordinate-outer-product sum with nonnegative real coefficients, hence exactly a nonnegative diagonal matrix.',
    'Both input vectors are arbitrary; coordinates with equal inputs have zero output increment.',
]
characterization_hypotheses = [
    'Finite coordinate set with real input/output increment vectors u and w.',
    'alpha <= beta; the surrounding printed nonnegative strict interval supplies this.',
    'The QC is required for every member of the nonnegative diagonal multiplier cone.',
    'No actual activation, base point, network bias, or simultaneously reachable pattern is assumed for the abstract pair.',
]

proposals = []


def existing_rows(key):
    return [
        {'owner': owner, 'id': c['id'], 'status': c['status']}
        for owner, ledger in owners.items()
        for c in ledger['material_claims']
        if key in c.get('source_unit_keys', [])
    ]


def proposal(key, status, decls, hypotheses, correspondence, action='promote_exact_whole_unit'):
    unit = units[key]
    assert sha256(unit['source_text'].encode()).hexdigest() == unit['text_sha256']
    assert sha256((ROOT / unit['source']).read_bytes()).hexdigest() == unit['source_sha256']
    proposals.append({
        'material_unit_key': key,
        'source_unit_keys': [key],
        'owner': 'core' if key.startswith('formulas.html') else 'modules',
        'status': status,
        'action': action,
        'lean_declarations': decls,
        'hypotheses': hypotheses,
        'correspondence': correspondence,
        'remaining_gaps': [],
        'source': unit['source'],
        'source_sha256': unit['source_sha256'],
        'line': unit['line'],
        'source_text': unit['source_text'],
        'text_sha256': unit['text_sha256'],
        'source_text_sha256': unit['text_sha256'],
        'whole_exact_unit_reviewed': True,
        'baseline_owner_rows': existing_rows(key),
    })


proposal('lipsdp.html::node-237', 'proved', [
    bridge + 'quotientSlopeRestricted',
    bridge + 'quotient_definition_iff_all_chords',
    bridge + 'all_actual_diagonal_qcs_imply_quotient_definition',
], ['This expression is the definition of a property of an activation; it does not assert that every activation has the property.', 'alpha <= beta; the containing definition has 0 <= alpha < beta.'],
         'quotientSlopeRestricted is exactly the displayed forall unequal-input quotient condition. quotient_definition_iff_all_chords proves its equivalence to the chord predicate used by the existing development, including zero chords without division. The derived converse recovers this exact property from all actual diagonal QCs. The antiderivative statement in containing node-233 is outside this exact formula unit and remains pending.')

proposal('lipsdp.html::node-269', 'proved', [
    bridge + 'quotient_definition_iff_all_chords',
    qc + 'scalar_qc_factorization',
    qc + 'scalar_qc_iff_admissible_chord',
], ['The unequal-input case u != 0 is in the preceding Step 1.', 's = w/u with alpha <= s <= beta.', 'u^2 is nonnegative.'],
         'The reviewed bridge cancels the nonzero denominator to reconstruct w = s*u, and scalar_qc_iff_admissible_chord explicitly rewrites the scalar QC as (2*u^2)*((s-alpha)*(beta-s)). Together with scalar_qc_factorization this is the precise denominator-clearing step instructed here; no sign assumption on u is needed.')

for key in ['formulas.html::node-98', 'formulas.html::node-100', 'formulas.html::node-539', 'formulas.html::node-541']:
    proposal(key, 'proved', qc_decls, mathematical_hypotheses,
             'The whole literal definition/lemma is covered. The quotient predicate is exactly the unequal-input printed definition and is equivalent to all admissible chords. For the actual shared elementwise activation, quotient_definition_implies_actual_block_qc proves the nonnegative printed quadratic form for every pair of input vectors. diagonal_qc_matrix_is_stated_block identifies all four actual blocks, and diagonal_qc_is_actual_block_quadratic identifies the scalar weighted expansion. The coordinate outer-product sum is exactly Matrix.diagonal(weight); its nonnegative weights are exactly the diagonal PSD condition, proving the parenthetical diagonal/PSD qualification. The proof covers the entire stricter printed real interval. The citation refers to current arXiv v2 Lemma 1, independently verified; no coupled multipliers, potential-function equivalence, network-bound optimization, or research-paper completion is inferred.')

for key in ['formulas.html::node-542', 'formulas.html::node-544']:
    proposal(key, 'proved', characterization_decls, characterization_hypotheses,
             'The actual block form equals the weighted coordinate QC, and the printed coordinate-sum cone is exactly all nonnegative diagonal matrices. all_diagonal_qcs_iff_coordinate_qcs tests unit coordinate weights, and scalar_qc_iff_admissible_chord handles u_i != 0 by w_i/u_i and u_i = 0 by forcing w_i = 0. all_diagonal_qcs_iff_independent_diagonal_slopes then gives exactly w = diagonal(d)*u with each d_i in the interval. Its existential slopes are independent per coordinate and refer only to the increment pair, with no activation or base points in the relation. This is precisely the explanatory abstraction/forgetting scope of the whole literal; it does not claim every chosen pattern occurs in an actual network.')

proposal('lipsdp.html::node-287', 'proved', characterization_decls + [
    invalid + 'positive_semidefiniteness_does_not_make_coupled_qc_valid',
], characterization_hypotheses,
         'The whole literal body, including both proof directions and the explanatory prose, is covered. The printed outer-product cone equals the nonnegative diagonal cone. Unit coordinate weights isolate each scalar QC; scalar_qc_factorization and scalar_qc_iff_admissible_chord establish the displayed product and handle the zero-input case. all_diagonal_qcs_iff_independent_diagonal_slopes proves the complete set-valued map with independent interval coordinates. This characterization contains only increments, not the activation/base points or reachable network patterns. The already reviewed actual two-input ReLU counterexample demonstrates the stated failure of a coupled PSD multiplier. The prose concerns that loss of information and its cost as an abstraction, not a quantified claim about optimal LipSDP gaps.')

for key, explanation in [
    ('formulas.html::node-99', 'Names the slope-restriction/diagonal-multiplier topic and cites Definition 1 and Lemma 1. No formula, quantified assertion, endpoint restriction, or guarantee occurs in this exact label.'),
    ('formulas.html::node-540', 'Names the diagonal-multiplier topic and cites Lemma 1. The mathematical lemma resides in the separately reviewed containing/body units.'),
    ('formulas.html::node-543', 'A descriptive heading announces what the QC records and discards, without asserting the characterization or any quantified consequence.'),
    ('lipsdp.html::node-280', 'Identifies a lemma about diagonal multipliers and its current arXiv citation. This exact label states no mathematical conclusion; the containing lemma and formula are reviewed separately.'),
]:
    proposal(key, 'not_a_formal_claim', [], [], explanation,
             action='independent_literal_semantic_classification')

for key in ['lipsdp.html::node-279', 'lipsdp.html::node-282']:
    proposal(key, 'proved', qc_decls, mathematical_hypotheses,
             'Refresh the existing proved mapping with the exact quotient-definition bridge and coordinate outer-product/PSD proofs. The actual block and nonnegative weighted scalar sum remain the same; the new basis proofs explicitly cover the printed multiplier representation and parenthetical PSD qualification. This refresh is not a new completed unit.',
             action='refresh_existing_proved_mapping_without_new_completion_credit')
proposal('lipsdp.html::node-285', 'proved', characterization_decls + [
    invalid + 'positive_semidefiniteness_does_not_make_coupled_qc_valid',
], characterization_hypotheses,
         'Refresh the existing whole proposition with the reviewed correspondence for its exact body node-287 and with the coordinate outer-product/diagonal cone identity. The whole conclusion and proof remain the imported all-coordinate/all-independent-slope equivalences. This existing proved ancestor earns no new completed-unit credit.',
         action='refresh_existing_proved_mapping_without_new_completion_credit')

withheld = []
for key, gaps in [
    ('lipsdp.html::node-233', ['The whole ancestor contains equivalence to alpha-strong convexity and beta-smoothness of an antiderivative, with derivative/integral, continuity, and converse arguments. The six reviewed theorems do not prove these clauses.']),
    ('lipsdp.html::node-239', ['Integral/derivative, continuity/Lipschitz, convexity, strong-convexity, smoothness, and reverse implication remain unproved by these sources.']),
    ('formulas.html::node-535', ['The whole containing box includes the antiderivative strong-convexity/smoothness equivalence.']),
    ('formulas.html::node-537', ['The whole body includes the antiderivative strong-convexity/smoothness equivalence.']),
    ('formulas.html::node-95', ['The S-procedure sufficiency and weighted block assembly are additional whole-unit scope; this review does not inspect their full theorem interface.']),
    ('formulas.html::node-97', ['The S-procedure sufficiency and weighted block assembly are additional whole-unit scope; this review does not inspect their full theorem interface.']),
    ('lipsdp.html::node-292', ['Global contraction/equilibrium local QC scope, DeepSDP/Reach-SDP admissibility, and the cited research scope exceed the new scalar/diagonal proofs.']),
    ('lipsdp.html::node-304', ['The loop transformation, architecture bypass, and feedback normalization claims are additional whole-unit scope.']),
]:
    unit = units[key]
    withheld.append({'material_unit_key': key, 'action': 'leave_all_pending_whole_rows_pending',
                     'text_sha256': unit['text_sha256'], 'source_sha256': unit['source_sha256'],
                     'remaining_gaps': gaps, 'baseline_owner_rows': existing_rows(key)})

assert len([p for p in proposals if p['status'] == 'proved' and p['action'] == 'promote_exact_whole_unit']) == 9
assert len([p for p in proposals if p['status'] == 'not_a_formal_claim']) == 4
assert len([p for p in proposals if p['action'].startswith('refresh_')]) == 3
for p in proposals:
    rows = p['baseline_owner_rows']
    if p['action'].startswith('refresh_'):
        assert any(r['status'] == 'proved' for r in rows)
    else:
        assert any(r['status'] == 'pending' for r in rows)

source_review = {
    'schema_version': 1,
    'status': 'approved',
    'reviewer': '/root/review_diagonal35',
    'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
    'review_type': 'independent_source_theorem_and_exact_material_correspondence_review',
    'errors': [],
    'findings': [],
    'inventory': ref(inventory_path),
    'baseline_owner_refs': baseline_owner_refs,
    'source_refs': [ref('SafeLearning/lipsdp.html'), ref('SafeLearning/formulas.html')],
    'proof_sources': [ref(bridge_file), ref(basis_file)],
    'reviewed_import_sources': [
        ref('verification/lean/SafeLearning/CompleteModulesDiagonalQC.lean'),
        ref('verification/lean/SafeLearning/CompleteModulesLipSDP.lean'),
        ref('verification/lean/SafeLearning/CompleteModulesLipSDPNetwork.lean'),
        ref('verification/lean/SafeLearning/CompleteModulesInvalidQC.lean'),
        ref('verification/lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean'),
    ],
    'declarations': declarations,
    'declaration_count': 8,
    'theorem_count': 6,
    'theorem_reviews': theorem_reviews,
    'actual_compilation_receipts': actual_receipts,
    'retained_prior_failures': retained_failures,
    'external_primary_source_review': {
        'url': 'https://arxiv.org/html/1906.04893v2',
        'pdf_url': 'https://arxiv.org/pdf/1906.04893v2',
        'paper_version': 'arXiv:1906.04893v2, 14 January 2023',
        'reviewed_sections': ['Section 2.2, Definition 1, equations (3), (6), (7)', 'Section 2.2, Lemma 1, equations (8), (9)', 'Appendix A.3, proof of Lemma 1'],
        'correspondence': 'Definition 1 supplies an ordered finite real interval. Lemma 1 defines only nonnegative coordinate outer-product sums and applies the printed block inequality to arbitrary actual shared elementwise activation differences. Appendix A.3 expands the block form into nonnegative weighted scalar forms. This scope matches the reviewed quotient bridge and multiplier basis. The function-property converse is a local derived result, not attributed to the paper.',
        'scope_limits': ['No coupled incremental multiplier validity is claimed.', 'Appendix A.8 repeated-nonlinearity/non-incremental claims were not promoted.', 'The convex-potential equivalence in the surrounding paper/site prose remains outside these proofs.'],
    },
    'whole_unit_rule': 'An exact pending whole row is promoted only when every assertion in its own text is covered; proved components do not override any remaining pending ancestor or overlap.',
    'scope_limits': ['This review approves only the two exact proof-source hashes and the enumerated literal material correspondences.', 'Successful compilation receipts are verified against actual sources and logs; no new compiler run was represented as executed by this reviewer.', 'Root must inspect candidate changes and complete independent installed-mapping checks before freezing checkpoint35.', 'Canonical proofs, site files, owner ledgers, selection, progress and publication files were not edited by this reviewer.', 'No full-book coverage or aggregate compilation success is inferred.'],
    'coverage_complete': False,
}
review_name = 'diagonal35-independent-source-review-v1.json'
write(review_name, source_review)
mapping = {
    'schema_version': 1,
    'status': 'approved_mapping_proposal_not_installed',
    'reviewer': '/root/review_diagonal35',
    'created_at_utc': datetime.now(timezone.utc).isoformat(),
    'errors': [],
    'inventory': ref(inventory_path),
    'baseline_owner_refs': baseline_owner_refs,
    'independent_source_review': ref('book/coverage/checks/checkpoint35-review/' + review_name),
    'proof_sources': [ref(bridge_file), ref(basis_file)],
    'source_refs': [ref('SafeLearning/lipsdp.html'), ref('SafeLearning/formulas.html')],
    'material_mappings': proposals,
    'counts': {'new_whole_mathematical_units': 9, 'literal_topic_citation_labels': 4,
               'refresh_existing_proved_units_no_completion_credit': 3,
               'total_mapping_proposals': 16},
    'overlapping_or_adjacent_whole_units_retained_pending': withheld,
    'pending_semantics': 'Any pending active row associated with a material key keeps that key pending, even when a broad proved component also mentions it.',
    'installation_scope': 'Update only enumerated exact material keys and corresponding exact active rows; attach this source-bound independent review. Root controls canonical proof selection and owner installation.',
    'coverage_complete': False,
    'owner_ledgers_selection_progress_publication_mutated': False,
}
write('diagonal35-exact-material-mapping-proposal-v1.json', mapping)
print(json.dumps({'review': ref('book/coverage/checks/checkpoint35-review/' + review_name),
                  'proposal': ref('book/coverage/checks/checkpoint35-review/diagonal35-exact-material-mapping-proposal-v1.json'),
                  'counts': mapping['counts'], 'status': source_review['status']}))

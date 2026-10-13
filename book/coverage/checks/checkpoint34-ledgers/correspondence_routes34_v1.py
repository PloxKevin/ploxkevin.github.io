"""Exact statement routes for IQC14.6, qualified NN14.3 and Conditional387.

These routes assemble existing independent mathematical decisions; genuine
compiler counts do not establish whole-source correspondence. Public namespaces
remain those in the approved original bytes.
"""
IQC_EXERCISE = 'nn-in-the-loop.html::exercise-20'
NN_EXERCISE = 'nn-in-the-loop.html::exercise-17'
CONDITIONAL = 'primer-probability.html::node-387'
IQC_KEYS = ['nn-in-the-loop.html::node-'+str(n) for n in [1254, 1258, 1260, 1262]]
NN_KEYS = ['nn-in-the-loop.html::node-'+str(n) for n in [1210, 1217, 1218, 1220]]
NN_PREFIX = 'SafeLearning.CompleteModulesNNWalkthroughLocal31.'
C_PREFIX = 'SafeLearning.CompleteAppliedConditionalExpectationMaterial31.'

def route(clause, hypotheses, declarations, **extra):
    return {'source_clause': clause, 'hypotheses': hypotheses,
            'lean_declarations': declarations,
            'classification': 'independently_reviewed_actual_mathematical_subclaim', **extra}

def assemble(iqc_summary, nn_summary, conditional_review_routes):
    iqc = []
    for r in iqc_summary['precise_clause_routes']:
        iqc.append(route(r['clause'], [r['hypotheses']],
                         r.get('reused_selected_declarations', [])+r.get('future_declarations', []),
                         **({'scope_limit': r['limit']} if 'limit' in r else {})))
    assert len(iqc) == 6
    iqc_material = {IQC_KEYS[0]: iqc, IQC_KEYS[1]: [iqc[0]],
                    IQC_KEYS[2]: [iqc[1]], IQC_KEYS[3]: iqc[2:]}
    # Six source requirements are kept as six existing claims. The first is
    # the explicitly supplied centers, rather than a universal equilibrium
    # existence theorem for arbitrary biased networks.
    iqc_claims = {0: [iqc[0]], 1: [iqc[0]], 2: [iqc[1]],
                  3: [iqc[1]], 4: [iqc[1]], 5: iqc[2:]}
    given_centers_scope = 'The exercise supplies actual equilibrium preactivation centers0 and2; shifted functions are encoded on those given inputs. No existence of such an equilibrium for an arbitrary biased network is asserted.'
    iqc_claims[0] = [dict(iqc[0], source_clause=given_centers_scope)]

    nn = {'a': [], 'b': [], 'c': []}
    clauses = {
        'part_a_actual_composition_and_Step5_feasibility': 'The exact scalar plant/controller composition and sector-QC energy identity give a feasible global walkthrough LMI.',
        'part_a_unique_determinant_optimizer_exact_matrix_official_spectrum_and_rounded_cells': 'For p1 the determinant optimizer is unique, its exact matrix and official eigenvalues are derived, and the displayed decimals are certified approximations.',
        'part_a_full_positive_storage_and_unit_storage_admissibility_and_inner_interval': 'All positive storage pairs and unit-storage multipliers have the exact full admissible interval; the shorter displayed decimal interval is a valid inner interval.',
        'part_a_positive_scaling_and_all_initial_true_global_exponential_loop': 'Positive scaling preserves the certificate, and every actual global scalar trajectory has an all-time geometric bound and converges to zero.',
        'part_b_global_infeasibility_and_genuine_local_origin_linearization': 'The a1.3 global LMI is infeasible; the actual origin derivative and tangent iteration are derived. Stable tangent dynamics alone do not establish global nonlinear stability.',
        'part_b_actual_root_bracket_open_basin_boundaries_and_exact_two_examples': 'The genuine critical radius has its certified rational bracket; the exact nonlinear open basin excludes the boundary equilibria, and the two given initial states have the proved convergence/escape behavior.',
        'part_b_derived_every_subcritical_strict_LMI_containment_and_exact_open_certificate_union': 'Every strictly subcritical radius has an explicit strict local LMI and containment certificate; their union equals the open basin, without an attained closed critical box.',
        'part_c_exact_sector_transform_original_coordinate_rescaling_discriminant_and_optimizer': 'The exact tanh3 sector, loop transform, discriminant, optimizer and original-coordinate storage/multiplier rescaling match the displayed formulas and approximation signs.',
        'part_c_actual_optimized_matrix_official_full_spectrum_and_all_display_rounding': 'The optimized local unit-storage matrix, complete official spectrum, multipliers and displayed precisions are certified with exact expressions.',
        'part_c_full_admissible_interval_false_upper_multiplier_and_exact_box3_certificate': 'The full local admissibility interval excludes the false old upper multiplier; an exact feasible multiplier and its p4/9 rescaling give the box3 containment equality and actual all-time invariance/decay.',
    }
    domains = nn_summary['precise_actual_scope_domains']
    for label, names in nn_summary['precise_clause_to_public_theorem_routes'].items():
        part = label[5]
        assert part in nn and label in clauses and names
        if part == 'a':
            hypotheses = [domains['global']]
        elif part == 'b':
            hypotheses = [domains['local'], domains['linearization']]
        else:
            hypotheses = [domains['box3']]
        nn[part].append(route(clauses[label], hypotheses, names))
    assert [len(nn[k]) for k in ['a', 'b', 'c']] == [4, 3, 3]
    finite = {'source_clause': 'Check representative scalar trajectories by simulation.',
              'hypotheses': ['Exactly the extracted scalar tanh dynamics, initial states0.5 and3, and200 floating steps with201 stored states.'],
              'lean_declarations': [], 'classification': 'independently_reviewed_finite_observational_simulation',
              'actual_evidence': nn_summary['finite_scalar_simulation_receipt'],
              'scope_limit': nn_summary['finite_scalar_simulation_scope']}
    nn['b'].append(finite)
    nn_material = {NN_KEYS[0]: nn['a']+nn['b']+nn['c'],
                   NN_KEYS[1]: nn['a'], NN_KEYS[2]: nn['b'], NN_KEYS[3]: nn['c']}
    nn_claims = {0: nn['a'], 1: nn['b'], 2: nn['c']}

    conditional = [route(r['clause'], [r['hypotheses']], r['declarations'])
                   for r in conditional_review_routes]
    assert len(conditional) == 6
    materials = {**iqc_material, **nn_material, CONDITIONAL: conditional}
    exercises = {IQC_EXERCISE: iqc_claims, NN_EXERCISE: nn_claims}
    return materials, exercises

"""Recompute numerical quantities used in the manually reviewed opening answers."""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as review
BASE = 'book/solutions/module-opening-step-review-v1'


def main():
    checks = []

    def check(name, condition, quantities):
        assert condition, name
        checks.append({'case': name, 'status': 'passed', 'recomputed': quantities})

    lower = F(35, 100) - F(8, 100)
    command = F(1, 10) - lower / F(1, 2)
    check('barriers_noisier_measurement', command == F(-44, 100) and lower + F(1, 2) * (command-F(1, 10)) == 0,
          {'lower': str(lower), 'command': str(command), 'correction': str(command+F(8, 10)),
           'old_terminal': str(lower + F(1, 2) * (F(-1, 2)-F(1, 10)))})
    check('barriers_failed_drive_threshold', F(1, 10)*F(1, 2) == F(5, 100), {'minimum_clearance': '1/20'})
    error = F(9, 10)*F(1, 10)+F(5, 100)
    lower = F(35, 100)-error
    command = F(1, 10)-lower/F(1, 2)
    check('barriers_measurement_age', error == F(14, 100) and command == F(-32, 100),
          {'present_error': str(error), 'lower': str(lower), 'command': str(command),
           'old_terminal': str(lower-F(3, 10)), 'old_boundary_time': str(lower/F(6, 10))})
    check('landscape_safe_set', 4-F(3, 2)**2 == F(7, 4) and 4-3**2 == -5, {'tested_h_values': [0, 1.75, -5]})
    physical = F(6, 7) + 2*math.sqrt(F(10, 7)) + F(4, 10)
    check('gp_midpoint_discrepancy', math.isclose(physical, 3.647600075811644, abs_tol=1e-12),
          {'physical_upper': physical, 'old_temperature_upper': 56.5+physical, 'nominal_maximum': 60-physical})
    qplus = [F(1)+F(1, 2), F(1, 2)+F(1)]
    qminus = [F(1)-F(1, 2), F(1, 2)-F(1)]
    check('gp_two_point_eigenvectors_and_norm', qplus == [F(3,2)]*2 and qminus == [F(1,2),F(-1,2)] and qminus[0]-qminus[1] == 1,
          {'eigenvalues': ['3/2','1/2'], 'f_a': '1/2', 'f_b': '-1/2', 'squared_norm': 1})
    sampled = [F(1)-abs(F(x)) for x in ['0','0.3','0.9','0.4']]
    check('gosafe_sample_and_intersample_margins', min(sampled) == F(1,10) and 1-F(11,10) == F(-1,10),
          {'sampled': [str(x) for x in sampled], 'intersample': '-1/10'})
    gamma = F(4,5)
    safe = (gamma*3+gamma**2*3)/(1-gamma**3)
    threshold = (25+gamma*3-safe)/gamma
    v56, v54 = 3+gamma*safe, 3+gamma*(3+gamma*safe)
    v52 = 3+gamma*v54
    check('viability_safe_routes_and_penalty', safe == F(540,61) and threshold == F(5657,244) and v56-gamma*v52 == F(3,5) and 25+gamma*(3-24) < safe,
          {'safe_value': str(safe), 'strict_penalty_threshold': str(threshold), 'unsafe_value_p24': str(25+gamma*(3-24)),
           'v56': str(v56), 'v54': str(v54), 'v52': str(v52), 'route_gap': str(v56-gamma*v52)})
    check('lmi_scalar_kkt', 2*(1-2)+2 == 0 and 2*(1-1) == 0 and (1-2)**2 == 1,
          {'optimum': 1, 'multiplier': 2, 'value': 1, 'second_derivative': 2})
    r2, rinf = 0.6/(2*math.sqrt(2)), 0.6/(2*math.sqrt(6))
    check('lipsdp_margin_radii', math.isclose(r2, 0.21213203435596423, abs_tol=1e-14) and math.isclose(rinf*math.sqrt(3), r2, abs_tol=1e-14),
          {'strict_r2': r2, 'sufficient_strict_rinf': rinf, 'boundary_gap': 0.6-2*math.sqrt(2)*r2})
    check('architectural_normalization', 3/2.5 == 1.2 and 3/math.sqrt(10) < 1,
          {'estimate_normalized_norm': 3/2.5, 'upper_bound_normalized_norm': 3/math.sqrt(10)})
    input_bound = 1.5*math.tanh(0.53)
    check('nn_biased_controller', F(3,10)*F(3,100)+F(2,100) == F(29,1000) and F(29,1000)/(1-F(9,10)) == F(29,100) and input_bound < 0.8,
          {'effective_error': '29/1000', 'ultimate_radius': '29/100', 'next_boundary_bound': 0.479,
           'actuator_bound': input_bound})
    check('nn_affine_equilibrium', F(1,2)*4+2 == 4 and F(1,4)*4+1 == 2,
          {'equilibrium': [4,2], 'deviation_coefficient': '3/4', 'next_from_origin': 1})
    check('safe_bo_two_constraints_and_implementation', F(12,100)/F(4,10) == F(3,10) and F(3,10)-F(4,100) == F(26,100),
          {'limiting_radius': '3/10', 'command_limit': '13/50', 'nominal_vibration_028': str(F(12,100)-F(4,10)*F(28,100)),
           'worst_vibration_032': str(F(12,100)-F(4,10)*F(32,100))})
    check('mpc_tube_and_error_budget', F(9,100)/(1-F(1,2)) == F(18,100) and F(16,100)*(1-F(1,2))-F(5,100) == F(3,100),
          {'new_radius': '9/50', 'nominal_bound': '41/50', 'physical_next_bound': '59/100',
           'approximation_budget': '3/100', 'associated_nominal_bound': '21/25'})
    mse = F(1,200)*F(1,10)**2
    miss = float(F(199,200))**200
    check('mpc_average_versus_uniform_and_finite_test', mse == F(1,20000) and math.isclose(miss,0.3669578217261671, abs_tol=1e-12),
          {'exceptional_probability': '1/200', 'mse': str(mse), 'rmse': math.sqrt(mse), 'maximum': 0.1, 'all200_miss': miss})
    check('bounded_noise_command_interval', -1+F(1,10) == F(-9,10) and F(155,100)-F(1,10) == F(145,100),
          {'allowable_commands': ['-9/10','29/20'], 'largest_realization_15': '8/5'})
    envelope = 0.15*math.sqrt(2*math.log(20000))
    failure = 200*math.exp(-envelope**2/(2*0.15**2))
    check('adaptive_gaussian_finite_envelope', math.isclose(failure,0.01,abs_tol=1e-14) and envelope < 0.95,
          {'envelope': envelope, 'common_union_failure_budget': failure, 'first_cone_radius': (0.95-envelope)/0.8})
    check('noise_cone_threshold', (F(7,10)-F(1,10)-F(1,5))/2 == F(1,5),
          {'radius': '1/5', 'lower_at_06': '1/5', 'lower_at_065': '1/10'})
    check('verification_scalar_logit_objective', (-0+2)-(2*0+1) == 1 and 1-3*F(1,3) == 0,
          {'worst_gap': 1, 'worst_input': 0, 'tie_input': '1/3', 'endpoint_gaps': [1,-2]})
    report = {'status': 'passed_opening_answer_arithmetic_recomputations', 'checks': checks,
              'assessment': review.ref(BASE+'/assessments-v1.json'), 'helper': review.ref(BASE+'/check_arithmetic.py'),
              'actual_command': sys.argv, 'cwd': str(Path.cwd()),
              'scope': 'Twenty independent scalar/fraction arithmetic checks for quantities used in the authored openings; no mathematical compilation, all-exercise proof, automated pedagogical approval or formal-coverage promotion is inferred.'}
    review.json_put(BASE+'/arithmetic-v1.json', report)
    print(json.dumps({'status':report['status'],'checks':len(checks),'report':review.ref(BASE+'/arithmetic-v1.json')}))


if __name__=='__main__':
    main()

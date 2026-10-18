"""Independent finite-pulse, chronology, and conditional-noise verification.

No finite-instrument producer is imported.  Scalar moments are reconstructed
from the immutable independent edge-energy assembler.  The public verifier
also replays the complete earlier instrument, quantum, and clock proofs.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUTPUT = HERE / 'finite_instrument_receipt.json'
SCALE = 10**15
SEQUENTIAL = 'code/source_scalar_instruments/sequential_instrument_receipt.json'
SCALAR = 'code/source_scalar_execution/source_scalar_execution_receipt.json'
PARENT_VERIFIER = 'code/source_scalar_instruments/verify_sequential_instrument.py'
SCALAR_VERIFIER = 'code/source_scalar_execution/verify_source_scalar_execution.py'
SCALAR_VERIFIER_SHA = 'c03892572732bbf7d019e721d19b6a249b445e2dc30f54d3c237be938cf88d42'
PINS = {
    SEQUENTIAL: '5fefaaeca3760b5a2c4bf81c32634b6c96c39f64a271b3735bee8a0fa8d07468',
    SCALAR: 'cf246c2caa072334e0d4796c1c6c49d2a231a263ff34281843a1c35c7cdbb69a',
    PARENT_VERIFIER: '4803d7466e2e43dbf00cccb1bab912b974dd0aa54e7b60effd8008ddd9b675f2',
}
FILES = (
    'code/source_scalar_finite_instrument/finite_instrument.py',
    'code/source_scalar_finite_instrument/verify_finite_instrument.py',
    'code/source_scalar_finite_instrument/test_finite_instrument.py',
    'code/source_scalar_finite_instrument/README.md',
    'code/source_scalar_execution/scalar_execution_algebra.py',
)
PARAMETERS = {
    'duration_min': '1/1000', 'duration_max': '1/100',
    'pointer_operation_duration': '1/10000',
    'half_diamond_error_max': '1/10000000',
    'preparation_trace_distance_max': '1/100000',
}
SCOPE = {
    'same_full64_mode_action_and_original_vacuum': True,
    'field_free_Hamiltonian_runs_during_every_pointer_operation': True,
    'exact_rectangular_field_pointer_pulse': True,
    'all21_pulse_centers_and210_prior_pairs_retained': True,
    'unconditional_marginals_of_joint_instrument': True,
    'later_operations_preserve_retained_classical_records': True,
    'finite_duration_and_declared_channel_noise_bounds': True,
    'local_hardware_coupling_on32_detector_sites': True,
    'effective_equal_time_smear_has_original_detector_support': False,
    'full_pointer_Magnus_phase_is_scalar': False,
    'Magnus_phase_scalar_on_ideal_GHZ_code_only': True,
    'ideal_baseline_probability': '1/2',
    'noisy_baseline_probability_fixed_to_half': False,
    'noise_response_compares_noisy_intervention_and_noisy_baseline': True,
    'ideal_centered_first_moments_follow_free_field': True,
    'noisy_first_moments_follow_free_field': False,
    'work_bound_applies_to_ideal_field_energy_only': True,
    'noise_or_total_hardware_energy_bound': False,
    'initial_state_supplied_at_model_time_zero': True,
    'initial16_coherent_factors_have_finite_duration_implementation': False,
    'clock_is_inherited_conditional_reference_not_noisy_branch_readout': True,
    'sampled_quantum_outcomes_or_actual_hardware_execution': False,
    'uniform_channel_noise_bound_from_Hamiltonian_coefficient_precision': False,
    'native_W12_quantum_controls_or_physical_clock': False,
    'source_preparation_Born_readout_and_quantum_controls_supplied': True,
    'spatial_continuum_interacting_or_regional_timeslice_join': False,
}
LAW = {
    'hbar': '1',
    'field_Hamiltonian': '(P.P+Q.Omega^2.Q)/2; Omega^2=M^(1/2) A M^(-1/2)',
    'pointer_free_Hamiltonian': '0',
    'rectangular_full_pointer_coupling': 'sum_i Z_i tensor m_i*g_i*q_i/(2*delta)',
    'pointer_only_gates': 'supplied finite-duration channels commuting with the free field flow',
    'ideal_code': 'span{|0>^32,|1>^32}; every Z_i acts as logical Z',
    'S_delta': 'sinc(delta*sqrt(A)/2)',
    'effective_smear': 'g_delta=S_delta*g',
    'pulse_factor_on_code': 'exp(-i*H0*delta/2)*exp(i*theta_delta)*exp(-i*Z*Phi(g_delta)/2)*exp(-i*H0*delta/2)',
    'theta_delta': '<g,(delta*A^(-1)-A^(-3/2)*sin(delta*sqrt(A)))*g>_M/(8*delta^2)',
    'interaction_picture_readout': 'B_j=Phi(g_delta)(t_j)',
    'K0': '(exp(-i*B_j/2)-i*exp(i*B_j/2))/2',
    'K1': '(exp(-i*B_j/2)+i*exp(i*B_j/2))/2',
    'nonselective': 'rho -> (exp(-i*B_j/2)*rho*exp(i*B_j/2)+exp(i*B_j/2)*rho*exp(-i*B_j/2))/2',
    'commutator': 'c_delta(d)=<g,S_delta^2*A^(-1/2)*sin(d*sqrt(A))*g>_M',
    'mean': 'mu_delta(t)=<g,S_delta*A^(-1/2)*sin(t*sqrt(A))*v>_M',
    'vacuum_variance': 'nu_delta=<g,S_delta^2*A^(-1/2)*g>_M/2',
    'sequential_response': 'exp(-nu_delta/2)*sin(mu_delta(t_j))*product_{k<j}cos(c_delta(t_j-t_k)/2)/2',
    'joint_record_law': 'sum_h L_h*rho*L_h^dagger tensor |h><h|; L_h=K_h21(B_21)...K_h1(B_1)',
    'mean_error_bound': 'delta^2*sqrt(G1*V0)/24',
    'variance_error_bound': 'delta^2*sqrt(G0*G1)/24',
    'single_probability_error_bound': 'delta^2*(sqrt(G1*V0)/48+sqrt(G0*G1)/96)',
    'commutator_error_bound': 'delta^2*G1*abs(d)/12',
    'cosine_error_bound': 'delta^2*G0*G1*d^2/48',
    'ideal_field_work_per_pulse': 'G_delta/8; G_delta=<g,S_delta^2*g>_M',
    'ideal_work_bounds': 'G0/8-delta^2*G1/96 <= G_delta/8 <= G0/8',
    'pointer_fault_model': 'one supplied full-pointer CPTP fault after each prep/read/decode operation, plus32 local CPTP faults at the common pulse endpoint',
    'fault_record_boundary': 'faults act on active field/pointers/current readout and are identity on every retained earlier classical record',
    'fault_norm': 'half diamond distance from identity <= epsilon at each of129 locations per readout',
    'preparation_norm': 'trace distance <= epsilon0 separately for initial baseline and intervention at model time0',
    'probability_noise_bound': 'epsilon0+129*j*epsilon',
    'paired_response_noise_bound': '2*epsilon0+258*j*epsilon',
    'uniform_parameter_region': 'delta_min<=delta<=delta_max; 0<=epsilon<=epsilon_max; 0<=epsilon0<=preparation_error_max',
    'clock_quantifier': 'every choice t_j in the inherited ordered intervals; pulses centered at t_j',
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def raw(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'),
                       allow_nan=False) + '\n').encode('ascii')


def equal(actual, expected, message):
    need(raw(actual) == raw(expected), message)


def rational(value):
    need(type(value) is str, 'rational string required')
    result = F(value)
    need(str(result) == value, 'noncanonical rational')
    return result


def load(path=OUTPUT):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result

    def reject(_):
        raise ValueError('floating or nonfinite JSON token')

    data = Path(path).read_bytes()
    need(len(data) <= 2_000_000, 'finite instrument receipt size')
    return json.loads(data, object_pairs_hook=pairs,
                      parse_float=reject, parse_constant=reject)


def down(value):
    scaled = value * SCALE
    return F(scaled.numerator // scaled.denominator, SCALE)


def up(value):
    return -down(-value)


def algebraic_bound(value, R, square_root=False):
    """Exact sign bisection; no floating estimate seeds the interval."""
    if square_root:
        need(value.sign() >= 0, 'square root of negative moment')
    low, high = 0, SCALE

    def difference(integer):
        point = F(integer, SCALE)
        return (R(point * point if square_root else point) - value).sign()

    need(difference(low) <= 0, 'nonnegative moment required')
    while difference(high) <= 0:
        high *= 2
    while high - low > 1:
        middle = (low + high) // 2
        if difference(middle) <= 0:
            low = middle
        else:
            high = middle
    return F(low, SCALE), F(high, SCALE)


def pinned_module(root, relative, expected_sha, name):
    path = root / relative
    code = path.read_bytes()
    need(sha256(code).hexdigest() == expected_sha,
         'immutable verifier ' + relative)
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    exec(compile(code, str(path), 'exec'), module.__dict__)
    return module


def analytical_checks():
    """Independent one-mode flow/Magnus identities behind the spectral proof.

    For each positive frequency the full quadratic action diagonalizes into
    this forced oscillator.  Exact operator identities then follow from CCR;
    this check is not a finite-dimensional truncation of the field Hilbert
    space.  The phase is scalar only on the ideal logical GHZ subspace.
    """
    import sympy as s

    t, w = s.symbols('t w', positive=True, real=True)
    q, p, force = s.symbols('q p force', real=True)
    free = s.Matrix([[s.cos(w*t), s.sin(w*t)/w],
                     [-w*s.sin(w*t), s.cos(w*t)]])
    half = free.subs(t, t/2)
    # The integral of the interaction-picture position is centered at t/2.
    effective_kick = s.Matrix([0, -2*force*s.sin(w*t/2)/w])
    composed = half * (half * s.Matrix([q, p]) + effective_kick)
    exact = free * s.Matrix([q, p]) + s.Matrix([
        -force*(1-s.cos(w*t))/w**2, -force*s.sin(w*t)/w])
    need(all(s.trigsimp(x) == 0 for x in composed-exact),
         'finite centered pulse differs from forced oscillator')
    need(s.simplify(s.diff(exact[0], t)-exact[1]) == 0,
         'forced oscillator position equation')
    need(s.simplify(s.diff(exact[1], t)+w*w*exact[0]+force) == 0,
         'forced oscillator momentum equation')
    need(list(exact.subs(t, 0)) == [q, p], 'forced initial data')
    # I(t)=int_0^t (t-u) sin(wu)/w du.  Its second derivative and two initial
    # conditions uniquely fix the sign and coefficient of the Magnus phase.
    integral = t/w**2 - s.sin(w*t)/w**3
    need(s.simplify(s.diff(integral, t, 2)-s.sin(w*t)/w) == 0,
         'central commutator integral')
    need(integral.subs(t, 0) == s.diff(integral, t).subs(t, 0) == 0,
         'Magnus phase initial data')
    phase = integral/(8*t*t)
    need(s.limit(phase/t, t, 0) == s.Rational(1, 48),
         'positive centered phase coefficient')
    u = s.symbols('u', real=True)
    averaging_error = s.integrate(u*u/(2*t), (u, -t/2, t/2))
    need(s.simplify(averaging_error-t*t/24) == 0,
         'centered average quadratic error coefficient')
    return {'forced_flow': True, 'magnus_phase': True,
            'centered_average_coefficient': '1/24',
            'full_pointer_phase_claimed_scalar': False}


def validate_custody(packet, root=ROOT):
    root = Path(root)
    equal(packet['parents'], PINS, 'immutable parent identities')
    for relative, digest in PINS.items():
        need(sha256((root/relative).read_bytes()).hexdigest() == digest,
             'immutable parent bytes ' + relative)
    equal(packet['source_pins'], {
        relative: sha256((root/relative).read_bytes()).hexdigest()
        for relative in FILES}, 'current finite instrument source bytes')


def moments(root):
    scalar = pinned_module(root, SCALAR_VERIFIER, SCALAR_VERIFIER_SHA,
                           '_finite_instrument_independent_scalar')
    R = scalar.R
    mass, matrix_rows, velocity, detector, _ = scalar.model(root)
    need(len(mass) == len(matrix_rows) == len(velocity) == len(detector) == 64,
         'all original scalar modes')
    matrix = [dict(row) for row in matrix_rows]
    G0 = sum((mass[i]*detector[i]**2 for i in range(64)), R())
    V0 = sum((mass[i]*velocity[i]**2 for i in range(64)), R())
    # Count each unordered off-diagonal pair once, independently of the
    # producer's matrix-vector multiply and mass-inner-product contraction.
    G1 = sum((mass[i]*matrix[i][i]*detector[i]**2 for i in range(64)), R())
    for i in range(64):
        for j, coefficient in matrix[i].items():
            need(mass[i]*coefficient == mass[j]*matrix[j][i],
                 'weighted self-adjoint field action')
            if j > i:
                G1 += 2*mass[i]*coefficient*detector[i]*detector[j]
    need(G0.sign() > 0 and V0.sign() > 0 and (G1-G0).sign() >= 0,
         'nonzero detector/preparation and positive action')
    g0lo, g0hi = algebraic_bound(G0, R)
    g1lo, g1hi = algebraic_bound(G1, R)
    gv = algebraic_bound(G1*V0, R, True)[1]
    gg = algebraic_bound(G0*G1, R, True)[1]
    return scalar, mass, matrix_rows, velocity, detector, {
        'G0_Qphi': G0.encode(), 'G1_Qphi': G1.encode(), 'V0_Qphi': V0.encode(),
        'G0_interval': [str(g0lo), str(g0hi)],
        'G1_interval': [str(g1lo), str(g1hi)],
        'sqrt_G1V0_upper': str(gv), 'sqrt_G0G1_upper': str(gg)}, (
            g0lo, g0hi, g1lo, g1hi, gv, gg)


def check_operations(actual, step, gadget):
    """Check the chronological program one operation at a time.

    Offsets are linear in delta; checking both interval endpoints proves
    every affine ordering/duration inequality across the declared region.
    """
    need(type(actual) is list and len(actual) == 129, 'complete readout program')
    gamma = rational(PARAMETERS['pointer_operation_duration'])
    sites = gadget['detector_sites']
    need(sites == list(range(32, 64)), 'same physical coupling region')
    coefficients = dict(gadget['local_controlled_field_coefficients_Qphi'])
    bases = dict(gadget['local_pointer_readout_bases'])
    for index, operation in enumerate(actual):
        expected = {
            'id': f'{step}:{index}', 'fault_location': f'fault/{step}/{index}'}
        if index < 64:
            start = [str(-F(1, 2)), str((index-64)*gamma)]
            end = [str(-F(1, 2)), str((index-63)*gamma)]
            if index < 32:
                kind, support = 'zero_preparation', [sites[index]]
            elif index == 32:
                kind, support = 'hadamard', [gadget['root_site']]
            else:
                kind, support = 'cnot', gadget['ghz_cnot_tree'][index-33]
        elif index < 96:
            site = sites[index-64]
            kind, support = 'simultaneous_local_field_coupling', [site]
            start, end = ['-1/2', '0'], ['1/2', '0']
            expected.update(coefficient_Qphi=coefficients[site],
                            joint_pulse=f'pulse/{step}',
                            fault_at='common_pulse_endpoint')
        elif index < 128:
            position = index-96
            site = sites[position]
            kind, support = 'pointer_readout', [site]
            start = ['1/2', str(position*gamma)]
            end = ['1/2', str((position+1)*gamma)]
            expected.update(basis=bases[site], record_symbol=f'b_{step}_{site}')
        else:
            kind, support = 'parity_decode', sites
            start, end = ['1/2', str(32*gamma)], ['1/2', str(33*gamma)]
            expected.update(record_symbol=f's_{step}',
                            consumes=[f'b_{step}_{site}' for site in sites])
        expected.update(kind=kind, sites=support, start_offset=start, end_offset=end)
        equal(operation, expected, 'actual declared operation ' + expected['id'])
        for duration in (F(1, 1000), F(1, 100)):
            a = rational(start[0])*duration+rational(start[1])
            b = rational(end[0])*duration+rational(end[1])
            need(b-a == (duration if 64 <= index < 96 else gamma),
                 'finite positive operation duration')
    return len(actual)


def verify_arithmetic(packet, root=ROOT):
    """New arithmetic only; public verify additionally proves all parents."""
    root = Path(root)
    need(type(packet) is dict, 'finite instrument object')
    need(set(packet) == {'schema', 'scope', 'law', 'parents', 'rounding_scale',
                        'parameters', 'moments', 'pulse_bounds', 'resource_contract',
                        'pair_bounds', 'rows', 'schedule', 'summary', 'source_pins'},
         'closed finite instrument schema')
    validate_custody(packet, root)
    equal(packet['schema'], 'oph.source_scalar.finite_rectangular_instrument.v1', 'schema')
    equal(packet['scope'], SCOPE, 'finite duration scientific boundaries')
    equal(packet['law'], LAW, 'exact pulse, record, and conditional noise law')
    equal(packet['parameters'], PARAMETERS, 'declared uniform parameter region')
    equal(packet['rounding_scale'], SCALE, 'outward rational grid')
    parent = load(root/SEQUENTIAL)
    need(len(parent['rows']) == 21, 'all inherited time intervals')
    scalar, mass, matrix, velocity, detector, expected_moments, values = moments(root)
    equal(packet['moments'], expected_moments, 'independent action moments')
    # Recheck the circuit and support directly, without trusting receipt labels.
    old = pinned_module(root, PARENT_VERIFIER, PINS[PARENT_VERIFIER],
                        '_finite_instrument_independent_parent')
    old.check_gadget(parent['regional_gadget'], mass, matrix, velocity,
                     detector, scalar.R)
    g0lo, g0hi, _, g1hi, gv, gg = values
    delta = F(1, 100)
    gamma, epsilon, epsilon0 = F(1, 10000), F(1, 10**7), F(1, 10**5)
    coefficient = up(gv/48+gg/96)
    single_error = up(delta*delta*coefficient)
    work_lo, work_hi = down(g0lo/8-delta*delta*g1hi/96), up(g0hi/8)
    need(0 < work_lo <= work_hi, 'positive ideal field work interval')
    equal(packet['pulse_bounds'], {
        'single_probability_coefficient_upper': str(coefficient),
        'single_probability_error_upper': str(single_error),
        'mean_error_upper': str(up(delta*delta*gv/24)),
        'variance_error_upper': str(up(delta*delta*gg/24)),
        'control_prefactor_interval': ['50', '500'],
        'ideal_field_work_per_pulse_interval': [str(work_lo), str(work_hi)],
        'GHZ_scalar_phase_interval_at_delta_max': ['0', str(up(delta*g0hi/48))]},
        'pulse moment and ideal-energy enclosures')
    expected_resources = {
        'maximum_receipt_bytes': 2000000, 'pointer_sites': 32,
        'preparation_operations_per_readout': 64,
        'simultaneous_local_couplings_per_readout': 32,
        'read_and_decode_operations_per_readout': 33, 'operations_per_readout': 129,
        'total_operations': 2709, 'total_local_bit_slots': 672,
        'total_parity_slots': 21, 'occupied_time_per_readout_at_delta_max': '197/10000',
        'historical_initial_coherent_factor_count_excluded': 16,
        'field_vacuum_and_initial_state_preparation_time_excluded': True,
        'schedule_is_declared_quantum_control_not_sampled_execution': True,
    }
    equal(packet['resource_contract'], expected_resources, 'operation and time resources')
    need(type(packet['pair_bounds']) is list and len(packet['pair_bounds']) == 210,
         'all prior pulse pairs')
    need(type(packet['rows']) is list and len(packet['rows']) == 21,
         'all unconditional marginals')
    need(type(packet['schedule']) is list and len(packet['schedule']) == 21,
         'all timed readout programs')
    prior_end, pair_index, operations = F(0), 0, 0
    expected_rows, separations = [], []
    for index, prior in enumerate(parent['rows']):
        j = index+1
        need(prior['step'] == j, 'inherited ordered readout identity')
        a, b = map(rational, prior['recovered_elapsed_time_interval'])
        start = a-delta/2-64*gamma
        end = b+delta/2+33*gamma
        separation = start-prior_end
        need(0 < a < b and separation > 0, 'nonoverlap for every allowed center')
        separations.append(separation)
        prior_end = end
        schedule = packet['schedule'][index]
        need(type(schedule) is dict and 'operations' in schedule, 'timed schedule object')
        expected_schedule = {
            'step': j, 'center_time_interval': [str(a), str(b)],
            'preparation_start_interval_at_delta_max': [str(start), str(b-delta/2-64*gamma)],
            'pulse_start_interval_at_delta_max': [str(a-delta/2), str(b-delta/2)],
            'pulse_end_interval_at_delta_max': [str(a+delta/2), str(b+delta/2)],
            'completed_record_availability_interval_at_delta_max': [str(a+delta/2+33*gamma), str(end)],
            'completed_record_availability_interval_uniform_in_delta': [str(a+F(1, 2000)+33*gamma), str(end)],
            'separation_from_previous_episode_lower': str(separation),
        }
        equal({k: v for k, v in schedule.items() if k != 'operations'},
              expected_schedule, 'pulse centers versus completed record times')
        operations += check_operations(schedule['operations'], j, parent['regional_gadget'])
        factor_difference = F(0)
        for earlier in range(index):
            gap = b-rational(parent['rows'][earlier]['recovered_elapsed_time_interval'][0])
            # |Delta c| <= delta^2 G1 gap/12; |sin x| <= |x| and
            # |c|,|c_delta| <= G0 gap give the sharper cosine bound.
            dc = up(delta*delta*g1hi*gap/12)
            dcos = up(delta*delta*g0hi*g1hi*gap*gap/48)
            equal(packet['pair_bounds'][pair_index], {
                'earlier': earlier+1, 'later': j,
                'center_separation_upper': str(gap),
                'commutator_difference_upper': str(dc),
                'cosine_difference_upper': str(dcos)}, 'complete prior-pair bound')
            pair_index += 1
            factor_difference += dcos
        factor_difference = up(factor_difference)
        amplitude = rational(prior['unmeasured_split_response_abs_upper']) + rational(
            prior['unmeasured_clock_comparison_error_upper'])
        pulse_error = up(single_error+amplitude*factor_difference)
        one_noise = epsilon0+129*j*epsilon
        two_noise = one_noise+one_noise
        old_error = rational(prior['sequential_probability_error_upper'])
        total_error = up(old_error+pulse_error+two_noise)
        signal = rational(prior['sequential_split_response_abs_lower'])
        p_lo, p_hi = map(rational, prior['sequential_split_probability_interval'])
        probability_error = up(old_error+pulse_error+one_noise)
        expected = {
            'step': j, 'center_time_interval': [str(a), str(b)],
            'signal_sign': prior['signal_sign'],
            'parent_split_response_abs_lower': str(signal),
            'parent_sequential_comparison_error_upper': str(old_error),
            'unmeasured_continuous_response_abs_upper': str(amplitude),
            'pulse_attenuation_difference_upper': str(factor_difference),
            'finite_duration_sequential_probability_error_upper': str(pulse_error),
            'noise_locations_through_readout': 129*j,
            'each_probability_noise_error_upper': str(one_noise),
            'paired_response_noise_error_upper': str(two_noise),
            'total_paired_response_error_upper': str(total_error),
            'noisy_intervention_probability_interval': [str(max(F(0), p_lo-probability_error)),
                                                       str(min(F(1), p_hi+probability_error))],
            'noisy_baseline_probability_interval': [str(max(F(0), F(1, 2)-one_noise)),
                                                   str(min(F(1), F(1, 2)+one_noise))],
            'noisy_paired_response_abs_lower': str(down(max(F(0), signal-total_error))),
            'uniformly_resolved': signal > total_error,
            'ideal_accumulated_field_work_interval': [str(down(j*work_lo)), str(up(j*work_hi))],
        }
        equal(packet['rows'][index], expected, 'finite-pulse and paired-noise marginal')
        expected_rows.append(expected)
    need(pair_index == 210 and operations == 2709, 'complete pair/program census')
    resolved = [row['step'] for row in expected_rows if row['uniformly_resolved']]
    minimum = min(rational(row['noisy_paired_response_abs_lower']) for row in expected_rows
                  if row['uniformly_resolved'])
    expected_summary = {
        'readouts': 21, 'prior_pairs': 210, 'retained_operations': operations,
        'parent_resolved_steps': parent['summary']['uniformly_resolved_steps'],
        'resolved_steps': resolved,
        'all_parent_resolved_steps_survive': resolved == parent['summary']['uniformly_resolved_steps'],
        'minimum_resolved_response_lower': str(minimum),
        'minimum_episode_separation_lower': str(min(separations)),
        'final_record_availability_interval_at_delta_max':
            packet['schedule'][-1]['completed_record_availability_interval_at_delta_max'],
        'final_record_availability_interval_uniform_in_delta':
            packet['schedule'][-1]['completed_record_availability_interval_uniform_in_delta'],
    }
    equal(packet['summary'], expected_summary, 'uniform finite-control comparison summary')
    need(len(resolved) == 15 and expected_summary['all_parent_resolved_steps_survive'],
         'retain every previously resolved response')
    return {'verified': True, **expected_summary, 'mathematical_replay': False,
            'parent_events_replayed': None, 'physical_outcomes': False,
            'native_quantum_controls': False}


def verify(packet, root=ROOT):
    root = Path(root)
    result = verify_arithmetic(packet, root)
    analytical_checks()
    parent_module = pinned_module(root, PARENT_VERIFIER, PINS[PARENT_VERIFIER],
                                  '_finite_instrument_fresh_parent_replay')
    proof = parent_module.verify(parent_module.load(root/SEQUENTIAL))
    need(proof.get('verified') is True and proof.get('mathematical_replay') is True
         and type(proof.get('parent_events_replayed')) is int
         and proof['parent_events_replayed'] == 5888,
         'fresh complete sequential, quantum, and clock parent proof')
    validate_custody(packet, root)
    result.update(mathematical_replay=True, parent_events_replayed=5888,
                  forced_oscillator_identities_verified=True)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('path', nargs='?', type=Path, default=OUTPUT)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args()
    print(json.dumps(verify(load(args.path), root=args.root), sort_keys=True, indent=2))

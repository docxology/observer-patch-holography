"""Finite rectangular quantum readout pulses with exact rational bounds.

This emits a certificate and a declared operation schedule, not sampled bits
or a simulated field-state trajectory. Parent scientific artifacts are fixed.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / 'source_scalar_execution'))
from scalar_execution_algebra import Q, parse, rational_bounds

OUTPUT = HERE / 'finite_instrument_receipt.json'
SEQUENTIAL = 'code/source_scalar_instruments/sequential_instrument_receipt.json'
SCALAR = 'code/source_scalar_execution/source_scalar_execution_receipt.json'
PARENT_VERIFIER = 'code/source_scalar_instruments/verify_sequential_instrument.py'
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
SCALE = 10**15
DELTA_MIN, DELTA_MAX = F(1, 1000), F(1, 100)
GAMMA, EPSILON, PREPARATION = F(1, 10000), F(1, 10**7), F(1, 10**5)


def raw(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False) + '\n').encode('ascii')


def down(value):
    return F((value * SCALE).numerator // (value * SCALE).denominator, SCALE)


def up(value):
    return -down(-value)


def sqrt_upper(value):
    """Exact sign bisection; decimal approximations do not define bounds."""
    if value.sign() < 0:
        raise ValueError('nonnegative square-root argument required')
    lo, hi = 0, SCALE
    while (Q(F(hi, SCALE)**2) - value).sign() < 0:
        hi *= 2
    while hi - lo > 1:
        mid = (hi + lo) // 2
        if (Q(F(mid, SCALE)**2) - value).sign() < 0:
            lo = mid
        else:
            hi = mid
    return F(hi, SCALE)


def source(path, root=ROOT):
    data = (root / path).read_bytes()
    if sha256(data).hexdigest() != PINS[path]:
        raise ValueError('immutable parent ' + path)
    return json.loads(data)


def scope():
    return {
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


def law():
    return {
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


def timed_operations(step, gadget):
    """Symbolic offsets alpha*delta+beta retain the complete schedule."""
    operations = []

    def add(kind, sites, start, end, **extra):
        k = len(operations)
        operations.append({'id': f'{step}:{k}', 'kind': kind, 'sites': sites,
                           'start_offset': list(map(str, start)),
                           'end_offset': list(map(str, end)),
                           'fault_location': f'fault/{step}/{k}', **extra})

    preparations = [('zero_preparation', [i]) for i in gadget['detector_sites']]
    preparations += [('hadamard', [gadget['root_site']])]
    preparations += [('cnot', edge) for edge in gadget['ghz_cnot_tree']]
    for k, (kind, sites) in enumerate(preparations):
        add(kind, sites, (-F(1, 2), (k-64)*GAMMA), (-F(1, 2), (k-63)*GAMMA))
    for site, coefficient in gadget['local_controlled_field_coefficients_Qphi']:
        add('simultaneous_local_field_coupling', [site], (-F(1, 2), F(0)), (F(1, 2), F(0)),
            coefficient_Qphi=coefficient, joint_pulse=f'pulse/{step}',
            fault_at='common_pulse_endpoint')
    for k, (site, basis) in enumerate(gadget['local_pointer_readout_bases']):
        add('pointer_readout', [site], (F(1, 2), k*GAMMA), (F(1, 2), (k+1)*GAMMA),
            basis=basis, record_symbol=f'b_{step}_{site}')
    add('parity_decode', gadget['detector_sites'], (F(1, 2), 32*GAMMA), (F(1, 2), 33*GAMMA),
        record_symbol=f's_{step}', consumes=[f'b_{step}_{i}' for i in gadget['detector_sites']])
    if len(operations) != 129:
        raise ValueError('operation census')
    return operations


def produce(root=ROOT):
    parent, scalar = source(SEQUENTIAL, root), source(SCALAR, root)
    if sha256((root/PARENT_VERIFIER).read_bytes()).hexdigest() != PINS[PARENT_VERIFIER]:
        raise ValueError('immutable parent verifier')
    mass = list(map(parse, scalar['mass_Qphi']))
    detector = list(map(parse, scalar['detector_Qphi']))
    velocity = list(map(parse, scalar['initial_velocity_Qphi']))
    action = [[(j, parse(a)) for j, a in row] for row in scalar['action_rows_Qphi']]
    applied = [sum((a*detector[j] for j, a in row), Q()) for row in action]
    g0 = sum((m*g*g for m, g in zip(mass, detector)), Q())
    g1 = sum((m*g*a for m, g, a in zip(mass, detector, applied)), Q())
    v0 = sum((m*v*v for m, v in zip(mass, velocity)), Q())
    g0l, g0u = map(F, rational_bounds(g0, SCALE))
    g1l, g1u = map(F, rational_bounds(g1, SCALE))
    rgv, rgg = sqrt_upper(g1*v0), sqrt_upper(g0*g1)
    coefficient = up(rgv/48+rgg/96)
    single = up(DELTA_MAX**2*coefficient)
    work_lo = down(g0l/8-DELTA_MAX**2*g1u/96)
    work_hi = up(g0u/8)
    pairs, rows, schedule = [], [], []
    previous_end = F(0)
    for j, old in enumerate(parent['rows'], 1):
        a, b = map(F, old['recovered_elapsed_time_interval'])
        start, end = a-DELTA_MAX/2-64*GAMMA, b+DELTA_MAX/2+33*GAMMA
        gap = start-previous_end
        if gap <= 0:
            raise ValueError('overlapping operation windows')
        previous_end = end
        loss = F(0)
        for k, earlier in enumerate(parent['rows'][:j-1], 1):
            separation = b-F(earlier['recovered_elapsed_time_interval'][0])
            bracket_difference = up(DELTA_MAX**2*g1u*separation/12)
            cosine_difference = up(DELTA_MAX**2*g0u*g1u*separation**2/48)
            loss += cosine_difference
            pairs.append({'earlier': k, 'later': j, 'center_separation_upper': str(separation),
                          'commutator_difference_upper': str(bracket_difference),
                          'cosine_difference_upper': str(cosine_difference)})
        response_upper = F(old['unmeasured_split_response_abs_upper'])+F(old['unmeasured_clock_comparison_error_upper'])
        attenuation = up(loss)
        pulse_error = up(single+response_upper*attenuation)
        one_noise = PREPARATION+129*j*EPSILON
        paired_noise = 2*one_noise
        old_error = F(old['sequential_probability_error_upper'])
        total = up(old_error+pulse_error+paired_noise)
        signal = F(old['sequential_split_response_abs_lower'])
        lo, hi = map(F, old['sequential_split_probability_interval'])
        probability_error = up(old_error+pulse_error+one_noise)
        probability_interval = [max(F(0), lo-probability_error), min(F(1), hi+probability_error)]
        baseline_interval = [max(F(0), F(1, 2)-one_noise), min(F(1), F(1, 2)+one_noise)]
        rows.append({
            'step': j, 'center_time_interval': [str(a), str(b)], 'signal_sign': old['signal_sign'],
            'parent_split_response_abs_lower': str(signal),
            'parent_sequential_comparison_error_upper': str(old_error),
            'unmeasured_continuous_response_abs_upper': str(response_upper),
            'pulse_attenuation_difference_upper': str(attenuation),
            'finite_duration_sequential_probability_error_upper': str(pulse_error),
            'noise_locations_through_readout': 129*j,
            'each_probability_noise_error_upper': str(one_noise),
            'paired_response_noise_error_upper': str(paired_noise),
            'total_paired_response_error_upper': str(total),
            'noisy_intervention_probability_interval': list(map(str, probability_interval)),
            'noisy_baseline_probability_interval': list(map(str, baseline_interval)),
            'noisy_paired_response_abs_lower': str(down(max(F(0), signal-total))),
            'uniformly_resolved': signal > total,
            'ideal_accumulated_field_work_interval': [str(down(j*work_lo)), str(up(j*work_hi))],
        })
        schedule.append({
            'step': j, 'center_time_interval': [str(a), str(b)],
            'preparation_start_interval_at_delta_max': [str(a-DELTA_MAX/2-64*GAMMA), str(b-DELTA_MAX/2-64*GAMMA)],
            'pulse_start_interval_at_delta_max': [str(a-DELTA_MAX/2), str(b-DELTA_MAX/2)],
            'pulse_end_interval_at_delta_max': [str(a+DELTA_MAX/2), str(b+DELTA_MAX/2)],
            'completed_record_availability_interval_at_delta_max': [str(a+DELTA_MAX/2+33*GAMMA), str(end)],
            'completed_record_availability_interval_uniform_in_delta': [str(a+DELTA_MIN/2+33*GAMMA), str(end)],
            'separation_from_previous_episode_lower': str(gap),
            'operations': timed_operations(j, parent['regional_gadget']),
        })
    resolved = [r['step'] for r in rows if r['uniformly_resolved']]
    return {
        'schema': 'oph.source_scalar.finite_rectangular_instrument.v1',
        'scope': scope(), 'law': law(), 'parents': PINS, 'rounding_scale': SCALE,
        'parameters': {'duration_min': str(DELTA_MIN), 'duration_max': str(DELTA_MAX),
                       'pointer_operation_duration': str(GAMMA),
                       'half_diamond_error_max': str(EPSILON), 'preparation_trace_distance_max': str(PREPARATION)},
        'moments': {'G0_Qphi': g0.encode(), 'G1_Qphi': g1.encode(), 'V0_Qphi': v0.encode(),
                    'G0_interval': list(map(str, [g0l, g0u])), 'G1_interval': list(map(str, [g1l, g1u])),
                    'sqrt_G1V0_upper': str(rgv), 'sqrt_G0G1_upper': str(rgg)},
        'pulse_bounds': {'single_probability_coefficient_upper': str(coefficient),
                         'control_prefactor_interval': [str(1/(2*DELTA_MAX)), str(1/(2*DELTA_MIN))],
                         'single_probability_error_upper': str(single),
                         'mean_error_upper': str(up(DELTA_MAX**2*rgv/24)),
                         'variance_error_upper': str(up(DELTA_MAX**2*rgg/24)),
                         'ideal_field_work_per_pulse_interval': list(map(str, [work_lo, work_hi])),
                         'GHZ_scalar_phase_interval_at_delta_max': ['0', str(up(DELTA_MAX*g0u/48))]},
        'resource_contract': {'maximum_receipt_bytes': 2000000, 'pointer_sites': 32,
                              'preparation_operations_per_readout': 64, 'simultaneous_local_couplings_per_readout': 32,
                              'read_and_decode_operations_per_readout': 33, 'operations_per_readout': 129,
                              'total_operations': 2709, 'total_local_bit_slots': 672, 'total_parity_slots': 21,
                              'occupied_time_per_readout_at_delta_max': str(DELTA_MAX+97*GAMMA),
                              'historical_initial_coherent_factor_count_excluded': 16,
                              'field_vacuum_and_initial_state_preparation_time_excluded': True,
                              'schedule_is_declared_quantum_control_not_sampled_execution': True},
        'pair_bounds': pairs, 'rows': rows, 'schedule': schedule,
        'summary': {'readouts': 21, 'prior_pairs': len(pairs), 'retained_operations': sum(len(r['operations']) for r in schedule),
                    'parent_resolved_steps': parent['summary']['uniformly_resolved_steps'],
                    'resolved_steps': resolved, 'all_parent_resolved_steps_survive': resolved==parent['summary']['uniformly_resolved_steps'],
                    'minimum_resolved_response_lower': min((r['noisy_paired_response_abs_lower'] for r in rows if r['uniformly_resolved']), key=F),
                    'minimum_episode_separation_lower': str(min(F(r['separation_from_previous_episode_lower']) for r in schedule)),
                    'final_record_availability_interval_at_delta_max': schedule[-1]['completed_record_availability_interval_at_delta_max'],
                    'final_record_availability_interval_uniform_in_delta': schedule[-1]['completed_record_availability_interval_uniform_in_delta']},
        'source_pins': {p: sha256((root/p).read_bytes()).hexdigest() for p in FILES},
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    packet = produce()
    data = raw(packet)
    if len(data) > 2000000:
        raise SystemExit('receipt byte bound exceeded')
    if args.write:
        OUTPUT.write_bytes(data)
    if args.check and OUTPUT.read_bytes() != data:
        raise SystemExit('finite instrument producer parity failure')
    print(json.dumps(packet['summary'], indent=2))

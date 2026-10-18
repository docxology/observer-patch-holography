"""Exact centered-pointer marginals for the existing scalar action and clock.

This constructs a quantum instrument mathematically. It emits no sampled
outcomes and does not identify deterministic field writes with quantum records.
"""
from __future__ import annotations

import argparse
from collections import deque
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE.parent/'source_scalar_execution'))
from scalar_execution_algebra import Q, parse, rational_bounds

OUTPUT = HERE/'sequential_instrument_receipt.json'
SCALAR = 'code/source_scalar_execution/source_scalar_execution_receipt.json'
CLOCK = 'code/source_scalar_clock_quantum/clock_quantum_receipt.json'
PINS = {
    SCALAR: 'cf246c2caa072334e0d4796c1c6c49d2a231a263ff34281843a1c35c7cdbb69a',
    CLOCK: '26ffdec55a41554af735c39f2198cad2858f9ad24a13c9868bde8b1d7b9697d9',
}
FILES = (
    'code/source_scalar_instruments/sequential_instrument.py',
    'code/source_scalar_instruments/verify_sequential_instrument.py',
    'code/source_scalar_instruments/test_sequential_instrument.py',
    'paper/tex_fragments/SOURCE_SCALAR_SEQUENTIAL_INSTRUMENT.tex',
)
SCALE = 10**15


def raw(x):
    return (json.dumps(x, sort_keys=True, separators=(',', ':'), allow_nan=False)+'\n').encode('ascii')


def down(x):
    return F((x*SCALE).numerator//(x*SCALE).denominator, SCALE)


def up(x):
    return -down(-x)


def scope():
    return {
        'same_full64_mode_action_preparation_and_detector': True,
        'exact_quantum_instrument_with_joint_classical_record_algebra': True,
        'reported_probabilities_are_unconditional_sequential_marginals': True,
        'all21_positive_readout_times_retained': True,
        'reference': 'same continuous finite action with the same centered instrument at every prior readout',
        'clock_quantifier': 'every ordered choice of times inside the inherited recovered intervals',
        'unconditional_first_moments_preserved': True,
        'branch_conditioned_clock_reconstructed': False,
        'binary_records_are_original_classical_field_writes': False,
        'instantaneous_ideal_instrument': True,
        'controlled_field_kicks_entangling_gates_reset_and_pointer_readout_supplied': True,
        'born_instrument_probability_law_supplied': True,
        'original_vacuum_and_coherent_preparation_supplied': True,
        'finite_gate_duration_or_noise_enclosed': False,
        'sampled_quantum_outcome_histories': False,
        'source_selected_quantum_operations': False,
        'physical_clock_or_observed_outcomes': False,
        'spatial_continuum_or_interacting_quantum_limit': False,
        'all_depth_instrument_theorems_formalized_in_lean': False,
    }


def source_packet(relative):
    data = (ROOT/relative).read_bytes()
    if sha256(data).hexdigest() != PINS[relative]:
        raise ValueError('immutable parent '+relative)
    return json.loads(data)


def gadget(mass, action, velocity, detector):
    sites = [i for i,g in enumerate(detector) if g != Q()]
    root = min(sites)
    seen = {root}; todo = deque([root]); tree = []
    while todo:
        i = todo.popleft()
        for j,a in action[i]:
            if j in sites and j not in seen and a != Q():
                seen.add(j); todo.append(j); tree.append([i,j])
    assert seen == set(sites)
    n = len(sites)
    return {
        'detector_sites': sites, 'root_site': root,
        'coherent_preparation_sites': [i for i,v in enumerate(velocity) if v != Q()],
        'local_controlled_field_coefficients_Qphi': [[i,(mass[i]*detector[i]).encode()] for i in sites],
        'ghz_cnot_tree': tree,
        'local_pointer_readout_bases': [[i,'Y' if i == root else 'X'] for i in sites],
        'pointer_initial_state': 'all zero; H on root then the ordered CNOT tree',
        'interaction': 'exp(-i Z_i tensor m_i*g_i*q_i/2) at each detector site',
        'binary_record': 'XOR of all local pointer outcome bits; bit0 is positive eigenvalue',
        'fine_record_kraus_factor_squared': str(F(1,2**(n-1))),
        'fine_records_per_parity': 2**(n-1),
        'ideal_operations_per_readout': {
            'zero_preparations': n, 'hadamards': 1, 'edge_cnots': n-1,
            'controlled_local_field_kicks': n, 'local_pointer_readouts': n,
            'parity_decodes': 1, 'total': 4*n+1,
        },
        'readout_count': 21, 'total_ideal_readout_operations': 21*(4*n+1),
        'additional_initial_coherent_preparation_kicks': sum(v != Q() for v in velocity),
        'operation_counts_bound_physical_time': False,
    }


def produce():
    scalar = source_packet(SCALAR); clock = source_packet(CLOCK)
    mass = list(map(parse, scalar['mass_Qphi']))
    detector = list(map(parse, scalar['detector_Qphi']))
    velocity = list(map(parse, scalar['initial_velocity_Qphi']))
    action = [[(j,parse(a)) for j,a in row] for row in scalar['action_rows_Qphi']]
    tau = Q(F(-1,35),F(2,35)); tau2 = F(1,245)
    g0 = sum((m*g*g for m,g in zip(mass,detector)),Q())
    g0u = F(rational_bounds(g0,SCALE)[1])
    previous = [Q() for _ in detector]; current = [tau*g for g in detector]
    brackets = []
    for d in range(1,21):
        c = sum((m*g*x for m,g,x in zip(mass,detector,current)),Q())
        bounds = rational_bounds(c,SCALE)
        square_upper = F(rational_bounds(c*c,SCALE)[1])
        assert 0 <= square_upper < 8
        brackets.append({'separation_steps': d, 'commutator_over_i_Qphi': c.encode(),
                         'commutator_interval': bounds, 'square_upper': str(square_upper)})
        applied = [sum((a*current[j] for j,a in row),Q()) for row in action]
        previous,current = current,[2*x-tau2*y-z for x,y,z in zip(current,applied,previous)]
    rows = []; discrete_lower = F(1)
    for j,parent in enumerate(clock['rows'],1):
        assert parent['step'] == j
        if j > 1:
            discrete_lower = down(discrete_lower*(1-F(brackets[j-2]['square_upper'])/8))
        lo,hi = map(F,parent['split_probability_interval'])
        response_upper = max(abs(lo-F(1,2)),abs(hi-F(1,2)))
        tmax = F(parent['recovered_elapsed_time_interval'][1])
        gaps = [tmax-F(p['recovered_elapsed_time_interval'][0]) for p in clock['rows'][:j-1]]
        continuous_loss = up(g0u*g0u*sum((d*d for d in gaps),F(0))/8)
        assert 0 <= continuous_loss < 1
        if j > 1:
            assert F(clock['rows'][j-2]['recovered_elapsed_time_interval'][1]) < F(parent['recovered_elapsed_time_interval'][0])
        factor_error = max(1-discrete_lower,continuous_loss)
        extra = up(factor_error*response_upper)
        error = up(F(parent['total_probability_error_upper'])+extra)
        signal = down(discrete_lower*F(parent['split_response_abs_lower']))
        lower,upper = lo-F(1,2),hi-F(1,2)
        corners = [d*x for d in (discrete_lower,F(1)) for x in (lower,upper)]
        probabilities = [down(F(1,2)+min(corners)),up(F(1,2)+max(corners))]
        rows.append({
            'step': j, 'recovered_elapsed_time_interval': parent['recovered_elapsed_time_interval'],
            'nominal_time_Qphi': parent['nominal_time_Qphi'], 'signal_sign': parent['signal_sign'],
            'discrete_attenuation_interval': [str(discrete_lower),'1'],
            'continuous_attenuation_interval': [str(1-continuous_loss),'1'],
            'attenuation_difference_upper': str(factor_error),
            'unmeasured_split_response_abs_upper': str(response_upper),
            'unmeasured_clock_comparison_error_upper': parent['total_probability_error_upper'],
            'disturbance_from_unmeasured_split_upper': str(up((1-discrete_lower)*response_upper)),
            'sequential_comparison_extra_error_upper': str(extra),
            'sequential_probability_error_upper': str(error),
            'sequential_split_probability_interval': list(map(str,probabilities)),
            'sequential_split_response_abs_lower': str(signal),
            'continuous_sequential_response_abs_lower': str(max(F(0),signal-error)),
            'uniformly_resolved': signal > error,
        })
    return {
        'schema': 'oph.source_scalar.centered_sequential_instrument.v1',
        'scope': scope(), 'parents': PINS, 'rounding_scale': SCALE,
        'instrument': {
            'pointer_state': '|+X>', 'unitary': 'exp(-i Z tensor Phi(g)/2)',
            'outcome0': '+Y', 'K0': '(exp(-i Phi/2)-i exp(i Phi/2))/2',
            'K1': '(exp(-i Phi/2)+i exp(i Phi/2))/2',
            'effect0': '(I+sin(Phi(g)))/2',
            'nonselective_map': '(W(-g/2) rho W(g/2)+W(g/2) rho W(-g/2))/2',
            'joint_record_state': 'sum_h L_h rho L_h* tensor |h><h|; L_h=K_h21 S ... K_h1 S',
            'baseline_sequential_probability': '1/2',
            'all_record_marginals_independent': False,
        },
        'detector_mass_norm_squared_Qphi': g0.encode(),
        'detector_mass_norm_squared_upper': str(g0u),
        'energy_injected_per_readout_Qphi': (g0/8).encode(),
        'total_readout_injected_work_Qphi': (21*g0/8).encode(),
        'regional_gadget': gadget(mass,action,velocity,detector),
        'cross_time_brackets': brackets, 'rows': rows,
        'summary': {'readout_times': 21, 'prior_pair_brackets': 210,
                    'distinct_positive_separations': 20,
                    'uniformly_resolved_steps': [r['step'] for r in rows if r['uniformly_resolved']]},
        'source_pins': {f: sha256((ROOT/f).read_bytes()).hexdigest() for f in FILES},
    }


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--write',action='store_true'); ap.add_argument('--check',action='store_true')
    args = ap.parse_args(); packet = produce(); data = raw(packet)
    if args.write: OUTPUT.write_bytes(data)
    if args.check and OUTPUT.read_bytes() != data: raise SystemExit('sequential instrument producer parity failure')
    print(json.dumps(packet['summary'],indent=2))

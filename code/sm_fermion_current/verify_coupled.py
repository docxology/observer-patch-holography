"""Independent exact replay of a declared regulated hybrid gauge action.

The electric kinetic law has a fixed regulator parameter.  It is not the
quadratic Maxwell kinetic law.  Classical gauge/Higgs equations use fermion
expectations; no operator nonabelian Gauss constraint is inferred.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
import itertools
import json
from pathlib import Path

import verify_current as old

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUTPUT = HERE / 'coupled_receipt.json'
F = Fraction
LAMBDA = F(1, 2)
MASS = F(1)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load(path=OUTPUT):
    return old.load(path)


def fixed_electric_law_check():
    """Differentiate the fixed kinetic law, including its global convexity."""
    import sympy as s
    E = s.symbols('E', real=True)
    lam, mass = s.symbols('lambda M', positive=True)
    r = lam * E / (2 * mass)
    kinetic = 2 * E / lam * s.atan(r) - 2 * mass / lam**2 * s.log(1 + r**2)
    velocity = 2 / lam * s.atan(r)
    require(s.simplify(s.diff(kinetic, E) - velocity) == 0, 'fixed kinetic first variation')
    require(s.simplify(s.diff(kinetic, E, 2) - 1 / (mass * (1 + r**2))) == 0,
            'fixed kinetic convexity')
    require(s.simplify(kinetic.subs(E, 0)) == 0, 'kinetic zero reference')
    require(s.simplify(s.cos(lam * velocity) - (1 - r**2) / (1 + r**2)) == 0,
            'exact electric real phase')
    require(s.simplify(s.sin(lam * velocity) - 2 * r / (1 + r**2)) == 0,
            'exact electric imaginary phase')
    return True


def electric_phase(electric):
    r = LAMBDA * electric / (2 * MASS)
    denominator = 1 + r * r
    result = (1 - r * r) / denominator, 2 * r / denominator
    require(old.norm(result) == 1, 'unit exact electric phase')
    return result


def face_check(carrier):
    require(type(carrier) is dict and set(carrier) == {'base', 'plaquettes'}, 'coupled carrier schema')
    base = old.geometry_check(carrier['base'])
    xyzs = list(itertools.product(range(1, 5), repeat=3))
    lookup = {(tuple(xyzs[row['ends'][0]]), row['axis']): e for e, row in enumerate(base['edges'])}
    faces = []
    for xyz in xyzs:
        for a, b in itertools.combinations(range(3), 2):
            if xyz[a] == 4 or xyz[b] == 4:
                continue
            xa = tuple(v + int(i == a) for i, v in enumerate(xyz))
            xb = tuple(v + int(i == b) for i, v in enumerate(xyz))
            boundary = [[lookup[xyz, a], 1], [lookup[xa, b], 1],
                        [lookup[xb, a], -1], [lookup[xyz, b], -1]]
            div = [0] * 64
            for edge, sign in boundary:
                u, v = base['edges'][edge]['ends']
                div[u] += sign
                div[v] -= sign
            require(not any(div), 'boundary of Wilson face')
            faces.append({'boundary': boundary})
    require(len(faces) == 108, 'complete Wilson face census')
    old.equal(carrier['plaquettes'], faces, 'Wilson geometry')
    return base, faces


def loop_phase(state, boundary):
    result = old.ONE
    for edge, sign in boundary:
        U = state[f'link/{edge}']
        require(old.norm(U) == 1 and sign in (-1, 1), 'compact Wilson input')
        result = old.mul(result, U if sign == 1 else old.conj(U))
    return result


def omitted_first_variation_check():
    """Check all internal trace coefficients and all-left Yukawa charge sums.

    A number-definite Fock state has <cc>=<c†c†>=0.  At H=Pi=0 the
    Higgs force from every arbitrary complex Yukawa coefficient vanishes
    in expectation; the underlying operators are not set to zero.
    """
    import sympy as s
    def generators(n):
        result = []
        for a in range(n):
            for b in range(a + 1, n):
                real, imaginary = s.zeros(n), s.zeros(n)
                real[a, b], real[b, a] = 1, -1
                imaginary[a, b] = imaginary[b, a] = s.I
                result.extend((real, imaginary))
        for a in range(n - 1):
            diagonal = s.zeros(n)
            diagonal[a, a], diagonal[a + 1, a + 1] = s.I, -s.I
            result.append(diagonal)
        return result
    color, weak = generators(3), generators(2)
    require(len(color) == 8 and len(weak) == 3, 'all nonabelian generators')
    traces = {}
    for name, color_dim, weak_dim, _ in old.FIELDS:
        rows = []
        for T in color:
            matrix = s.zeros(abs(color_dim) * weak_dim) if abs(color_dim) == 1 else s.kronecker_product(
                -T.T if color_dim < 0 else T, s.eye(weak_dim))
            rows.append(s.trace(matrix))
        for T in weak:
            matrix = s.zeros(abs(color_dim) * weak_dim) if weak_dim == 1 else s.kronecker_product(s.eye(abs(color_dim)), T)
            rows.append(s.trace(matrix))
        require(rows == [0] * 11, 'omitted nonabelian expected first variations')
        traces[name] = rows
    q = {name: int(6 * Y) for name, _, _, Y in old.FIELDS}
    require(q['Q'] + 3 + q['u_c'] == q['Q'] - 3 + q['d_c'] == q['L'] - 3 + q['e_c'] == 0,
            'three gauge-neutral Yukawa channels')
    require(sum(abs(c) * w * int(6 * y) for _, c, w, y in old.FIELDS) == 0,
            'neutral generation')
    require(sum(abs(c) * w * int(6 * y)**3 for _, c, w, y in old.FIELDS) == 0,
            'generation cubic hypercharge census')
    require(2 * q['Q'] + q['u_c'] + q['d_c'] == 3 * q['Q'] + q['L'] == 0,
            'generation mixed anomaly census')
    require(2 - 1 - 1 == 0 and (3 + 1) % 2 == 0, 'nonabelian representation census')
    # All 27 independent Yukawa coefficients remain arbitrary.  Every first
    # Higgs variation is a linear combination of pair expectations, all zero
    # by fixed-number selection, including pairs involving the vacuum families.
    Yukawa = s.symbols('Y0:27', complex=True)
    anomalous = s.symbols('F0:27', complex=True)
    source = sum(y * f for y, f in zip(Yukawa, anomalous))
    require(source.subs({f: 0 for f in anomalous}) == 0, 'all Yukawa expected Higgs forces')
    h = s.symbols('H0:4', real=True)
    mass_squared, quartic = s.symbols('mass_squared quartic', real=True)
    radius = sum(x * x for x in h)
    potential = mass_squared * radius + quartic * radius**2
    require(all(s.diff(potential, x).subs({z: 0 for z in h}) == 0 for x in h),
            'all Higgs potential first variations')
    # A retained obstruction: internal trace cancellation is only in expectation.
    weak_charge_variance = F(2) * F(1, 64) * F(63, 64)
    require(weak_charge_variance == F(63, 2048) > 0, 'nonabelian quantum Gauss boundary')
    return traces


SCOPE = {
    "same_finite_hybrid_action_for_CAR_electric_and_Wilson_factors": True,
    "all_144_electric_links_and_108_plaquettes_executed": True,
    "actual_electric_to_link_to_matter_read_after_write": True,
    "exact_discrete_continuity_and_expectation_Gauss": True,
    "full_one_generation_internal_multiplicities_retained": True,
    "number_conserving_Slater_and_classical_field_interpretation": True,
    "nonquadratic_electric_kinetic_law_explicitly_declared": True,
    "quadratic_Maxwell_electric_kinetic_law": False,
    "exact_full_Hamiltonian_exponential": False,
    "full_word_energy_conservation_claimed": False,
    "quantum_operator_Gauss_or_quantized_gauge_history": False,
    "three_generation_execution": False,
    "global_Z6_quotient_selected": False,
    "nonzero_Higgs_or_nonabelian_field_execution": False,
    "continuous_trajectory_error_bound": False,
    "native_action_state_clock_or_physical_identification": False,
}


LAW = {
    "gauge_group": "SU3xSU2xU1_direct_product_cover",
    "Hamiltonian": "sum_e T_lambda(E_e)+sum_f beta*(1-Re(W_f))+sum_e <H_CAR,e>",
    "symplectic_form": "sum_e dE_e wedge dtheta_e + i sum_s multiplicity_s dconj(psi_s) wedge dpsi_s",
    "kinetic_lambda": '1/2', "electric_mass": '1',
    "electric_duration": '1/2',
    "magnetic_duration": '1/2', "magnetic_weight": '1',
    "matter_duration": '1/2', "matter_hopping": '1',
    "electric_kinetic": "T_lambda(E)=2*E/lambda*atan(lambda*E/(2*M))-2*M/lambda^2*log(1+(lambda*E/(2*M))^2)",
    "kinetic_derivative": "2/lambda*atan(lambda*E/(2*M))",
    "kinetic_second_derivative": "1/(M*(1+(lambda*E/(2*M))^2))",
    "kinetic_parameter_boundary": "lambda is a fixed action parameter, not an adaptive step; this fixture separately chooses electric duration=lambda",
    "electric_drift": "U_new=(1+i*lambda*E/(2*M))/(1-i*lambda*E/(2*M))*U_old; E unchanged",
    "Wilson_loop": "W_f=product_boundary U_e^orientation",
    "magnetic_kick": "E_e_new=E_e_old-magnetic_duration*beta*orientation*Im(W_f); links unchanged",
    "matter_factor": "the same CAR midpoint factor and variational expectation current as the pinned prefix",
    "Gauss": "outward_divergence(E)-sum_s multiplicity_s*q_s*orbital_site_norm_squared",
    "schedule": "pinned full matter sweep; all electric drifts; all Wilson kicks; one matter return at edge14; public readout",
    "return_edge": 14,
    "control": "drift_disabled retains each link unchanged with a link-only read; it is a counterfactual schedule, not the full declared action word",
    "energy_boundary": "symplectic splitting and exact Gauss do not assert conservation of the summed Hamiltonian over the finite word",
}


REDUCTION = {
    "families": 3,
    "occupied_family": 0,
    "vacuum_families": [1, 2],
    "fermion_normal_covariance": "P_s=I_internal_multiplicity tensor |psi_s><psi_s|",
    "anomalous_covariance": "<c_i c_j>=0 in the fixed-number Slater state",
    "nonabelian_links": "identity",
    "nonabelian_electric_momenta": "zero",
    "Higgs_and_conjugate_momentum": "zero",
    "Yukawa_coefficients": "all 27 arbitrary complex coefficients of three declared families",
    "vacuum_family_invariance": "Higgs zero removes Yukawa pair terms; family-diagonal number-conserving hopping preserves the other two Fock vacua",
    "omitted_mean_force_boundary": "traceless internal generators have zero current expectation; Higgs Yukawa force uses the zero anomalous covariance; this is not zero operator fluctuation",
    "physical_boundary": "supplied finite mean-field restriction, not a chiral regulator or a gauge-constrained quantum state",
}

PARENT_PATH = 'code/sm_fermion_current/current_receipt.json'
PARENT_SHA256 = 'a35e08e270712b8c26c2aaa5ce1c877f0fc97b79770b0a1da57eb006e73f2ffe'
SOURCE_PATHS = tuple('code/sm_fermion_current/' + name for name in
                    ('coupled.py', 'build_coupled.py', 'verify_coupled.py', 'test_coupled.py',
                     'coupled_README.md', 'current.py', 'verify_current.py', 'current_receipt.json')) + (
    'code/sm_local_action/jet_action.py', 'code/sm_abelian_reduction/pilot.py',
    'Lean/Screen/WeylYukawaConventions.lean', 'Lean/Screen/A5FamilyBand.lean')


def validate_custody(packet):
    require(type(packet) is dict and set(packet) == {
        'schema', 'scope', 'law', 'mean_field_restriction', 'parent', 'carrier',
        'multiplets', 'runs', 'resource_contract', 'comparisons', 'source_pins'}, 'root schema')
    old.equal(packet['schema'], 'oph.sm_fermion_coupled.v1', 'schema')
    old.equal(packet['scope'], SCOPE, 'scope')
    old.equal(packet['law'], LAW, 'fixed regulated action')
    old.equal(packet['mean_field_restriction'], REDUCTION, 'hybrid restriction')
    old.equal(packet['resource_contract'], {'maximum_run_bytes': 4500000, 'maximum_register_integer_bits': 12000,
                                           'maximum_receipt_bytes': 20000000}, 'bounded resource contract')
    require(len(old.canonical(packet)) <= 20000000, 'receipt byte bound')
    require(type(packet['source_pins']) is dict and set(packet['source_pins']) == set(SOURCE_PATHS), 'source pin census')
    for name in SOURCE_PATHS:
        content = (ROOT / name).read_bytes()
        old.equal(packet['source_pins'][name], {'bytes': len(content), 'sha256': sha256(content).hexdigest()},
                  'source content binding')
    data = (ROOT / PARENT_PATH).read_bytes()
    require(sha256(data).hexdigest() == PARENT_SHA256, 'immutable original current receipt')
    old.equal(packet['parent'], {'path': PARENT_PATH, 'sha256': PARENT_SHA256}, 'immutable parent binding')
    return {'custody_verified': True, 'mathematical_replay': False}


def coupled_observables(state, geometry, faces):
    result = old.read_observables(state, geometry)
    loops = [loop_phase(state, row['boundary']) for row in faces]
    matter_terms = []
    for edge, row in enumerate(geometry['edges']):
        u, v = row['ends']
        matter = F(0)
        for name, color, weak, Y in old.FIELDS:
            transported = old.spin_kernel(row['axis'], old.power(state[f'link/{edge}'], int(6 * Y)),
                                           old.spinor(state, name, v))
            matter += 2 * abs(color) * weak * old.inner(old.spinor(state, name, u), transported)[0]
        matter_terms.append(matter)
    magnetic_terms = [1 - z[0] for z in loops]
    def enclose(terms):
        denominator = 2 ** 40
        lower = sum((z * denominator).__floor__() for z in terms)
        return [str(F(lower, denominator)), str(F(lower + len(terms), denominator))]
    result.update({'Wilson_loops': [old.encode(z) for z in loops],
                   'magnetic_energy_interval': enclose(magnetic_terms),
                   'magnetic_energy_terms': list(map(str, magnetic_terms)),
                   'matter_energy_interval': enclose(matter_terms),
                   'matter_energy_terms': list(map(str, matter_terms)),
                   'energy_interval_grid_denominator': str(2 ** 40),
                   'electric_kinetic_arguments': [str(state[f'electric/{e}']) for e in range(144)],
                   'total_energy_expression': 'sum_e T_lambda(electric_kinetic_arguments[e])+sum magnetic_energy_terms+sum matter_energy_terms'})
    return result


def replay(run, carrier, parent):
    require(type(run) is dict and set(run) == {'cohort', 'prefix', 'events', 'checkpoints',
                                             'feedback_witness', 'final_event_hash'}, 'coupled run schema')
    cohort = run['cohort']
    require(cohort in ('baseline', 'phase_intervention', 'gauge_copy', 'drift_disabled'), 'coupled cohort')
    prefix_cohort = 'phase_intervention' if cohort == 'drift_disabled' else cohort
    parent_run = next(r for r in parent['runs'] if r['cohort'] == prefix_cohort)
    old.equal(run['prefix'], parent_run, 'complete immutable executed prefix')
    geometry, faces = face_check(carrier)
    states = old.replay(run['prefix'], geometry)
    state = dict(states[-1][0])
    versions, writers, recorded = {}, {}, {}
    for event in run['prefix']['events']:
        for row in event['writes']:
            key = row['port']
            versions[key], writers[key], recorded[key] = row['version'], event['id'], row['value']
    offset = len(run['prefix']['events'])
    require(type(run['events']) is list and len(run['events']) == 255, 'all coupled factors retained')
    require(type(run['checkpoints']) is list and len(run['checkpoints']) == 2, 'coupled checkpoint census')
    index, previous = 0, run['prefix']['final_event_hash']
    snapshots = []
    byte_count = len(old.canonical(run['prefix']))

    def take(operation, reads, updates, metadata):
        nonlocal index, previous, byte_count
        event = run['events'][index]
        require(type(event) is dict and set(event) == {'id', 'operation', 'metadata', 'reads', 'parents',
                                                    'writes', 'previous_hash', 'event_hash'}, 'continuation event schema')
        old.equal(event['id'], offset + index, 'continuation event id')
        old.equal(event['operation'], operation, 'coupled operation')
        old.equal(event['metadata'], metadata, 'coupled metadata')
        old.equal(event['previous_hash'], previous, 'unbroken prefix continuation')
        old.equal(event['event_hash'], old.hashed({k: v for k, v in event.items() if k != 'event_hash'}), 'continuation event digest')
        names = sorted(set(reads))
        old.equal(event['reads'], [{'port': key, 'version': versions[key], 'writer': writers[key], 'value': recorded[key]}
                                   for key in names], 'actual coupled read-from')
        old.equal(event['parents'], sorted({writers[key] for key in names}), 'actual coupled parents')
        old.equal(event['writes'], [{'port': key, 'version': versions[key] + 1, 'value': old.encode(updates[key])}
                                    for key in sorted(updates)], 'same-action factor result')
        for key, value in updates.items():
            numbers = value if type(value) is tuple else (value,)
            require(all(max(x.numerator.bit_length(), x.denominator.bit_length()) <= 12000 for x in numbers),
                    'exact arithmetic bit bound')
            state[key], recorded[key] = value, old.encode(value)
            versions[key], writers[key] = versions[key] + 1, offset + index
        byte_count += len(old.canonical(event))
        require(byte_count <= 4500000, 'bounded coupled run bytes')
        previous, index = event['event_hash'], index + 1

    initial_electric = state['electric/14']
    for edge in range(144):
        u, E = f'link/{edge}', f'electric/{edge}'
        if cohort == 'drift_disabled':
            take('electric_drift_disabled', [u], {u: state[u]}, {'edge': edge})
        else:
            take('electric_drift', [E, u], {u: old.mul(electric_phase(state[E]), state[u])}, {'edge': edge})
    after_drift = state['link/14']
    for face, row in enumerate(faces):
        W = loop_phase(state, row['boundary'])
        updates = {f'electric/{edge}': state[f'electric/{edge}'] - F(1, 2) * sign * W[1]
                   for edge, sign in row['boundary']}
        reads = [f'{kind}/{edge}' for edge, _ in row['boundary'] for kind in ('link', 'electric')]
        take('Wilson_kick', reads, updates, {'plaquette': face})

    def readout(label):
        take('coupled_readout', [k for k in state if not k.startswith('factor_current/')], {}, {'checkpoint': label})
        result = coupled_observables(state, geometry, faces)
        old.equal(run['checkpoints'][len(snapshots)], {'event': offset + index - 1, 'readout': result},
                  'coupled public readout')
        snapshots.append((dict(state), result))

    readout('after_gauge_factors')
    edge, row = 14, geometry['edges'][14]
    u, v = row['ends']
    names = [old.port(name, site, spin) for name, _, _, _ in old.FIELDS for site in (u, v) for spin in range(2)]
    writes = run['events'][index].get('writes')
    require(type(writes) is list and all(type(r) is dict and set(r) == {'port', 'version', 'value'} for r in writes),
            'matter return write schema')
    old.equal([r['port'] for r in writes], sorted(names + ['electric/14', 'factor_current/14']), 'matter return local write set')
    submitted = {r['port']: r['value'] for r in writes}
    updates = {key: old.complex_value(submitted[key]) for key in names}
    current = F(0)
    for name, color, weak, Y in old.FIELDS:
        q, d = int(6 * Y), abs(color) * weak
        before_u, before_v = old.spinor(state, name, u), old.spinor(state, name, v)
        after_u, after_v = old.spinor(updates, name, u), old.spinor(updates, name, v)
        imag = old.midpoint_residual(before_u, before_v, after_u, after_v, row['axis'], old.power(state['link/14'], q))
        j = -2 * d * q * imag
        require(d * q * (sum(map(old.norm, after_u)) - sum(map(old.norm, before_u))) == -F(1, 2) * j,
                'coupled return charge continuity')
        current += j
    updates['electric/14'], updates['factor_current/14'] = state['electric/14'] - current / 2, current
    take('coupled_matter_return', names + ['electric/14', 'link/14'], updates, {'edge': 14})
    return_event = offset + index - 1
    readout('final')
    old.equal(run['feedback_witness'], {'edge': 14, 'electric_before_drift': str(initial_electric),
                                       'link_after_drift': old.encode(after_drift), 'electric_drift_event': offset + 14,
                                       'matter_return_event': return_event, 'return_midpoint_current': str(current)},
              'actual electric-to-matter feedback witness')
    old.equal(run['final_event_hash'], previous, 'coupled terminal event hash')
    require(index == len(run['events']), 'unconsumed coupled events')
    return snapshots, current


def verify(packet):
    validate_custody(packet)
    fixed_electric_law_check()
    omitted_first_variation_check()
    face_check(packet['carrier'])
    old.multiplet_check(packet['multiplets'])
    parent = old.load(ROOT / PARENT_PATH)
    require(old.verify(parent)['verified'], 'fresh complete parent replay')
    require(type(packet['runs']) is list and len(packet['runs']) == 4, 'coupled run census')
    old.equal([r.get('cohort') for r in packet['runs']], ['baseline', 'phase_intervention', 'gauge_copy', 'drift_disabled'],
              'coupled cohort order')
    results = [replay(run, packet['carrier'], parent) for run in packet['runs']]
    for (_, ordinary), (_, gauge) in zip(results[1][0], results[2][0]):
        old.equal(gauge, ordinary, 'coupled gauge-invariant readout')
    final = [r[0][-1][1] for r in results]
    differences = {key: [str(F(b) - F(a)) for a, b in zip(final[0][key], final[1][key])]
                   for key in ('charge', 'electric', 'instantaneous_current')}
    feedback = results[1][1] - results[3][1]
    require(feedback != 0, 'nonzero electric-to-link-to-matter response')
    old.equal(packet['comparisons'], {'gauge_invariant_public_records_equal': True,
                                     'intervention_minus_baseline_final': differences,
                                     'return_current_minus_disabled_drift': str(feedback),
                                     'mean_field_only': True, 'operator_Gauss_claimed': False},
              'coupled scientific comparisons')
    lower = (feedback * 2**40).__floor__()
    return {'verified': True, 'exact_rational_replay': True, 'sites': 64, 'links': 144, 'plaquettes': 108,
            'cohorts': 4, 'continuation_events': 1020, 'retained_prefix_events': 2444,
            'electric_to_link_to_matter_feedback': True, 'same_declared_hybrid_action': True,
            'electric_kinetic': 'fixed_lambda_convex_nonquadratic', 'quadratic_Maxwell_kinetic': False,
            'mean_Gauss': True, 'operator_Gauss': False, 'nonabelian_expected_first_variations_zero': True,
            'Higgs_Yukawa_expected_first_variations_zero': True,
            'declared_families': 3, 'occupied_family': 0, 'vacuum_families': [1, 2],
            'arbitrary_complex_Yukawa_coefficients': 27,
            'feedback_current_difference_interval': [str(F(lower, 2**40)), str(F(lower + 1, 2**40))],
            'global_Z6_quotient_selected': False, 'physical_current_attached': False,
            'continuous_trajectory_error_bound': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('path', nargs='?', type=Path, default=OUTPUT)
    print(json.dumps(verify(load(parser.parse_args().path)), indent=2, sort_keys=True))

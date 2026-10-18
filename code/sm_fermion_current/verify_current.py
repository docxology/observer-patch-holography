"""Independent exact replay of the finite CAR hypercharge current receipt.

The verifier uses Gaussian rational pairs and the midpoint equation itself,
not the producer's Cayley implementation.  The Slater projector certifies a
fermionic state; its Gauss assertion concerns expectations with classical
electric records, never the operator constraint of quantum gauge theory.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUTPUT = HERE / 'current_receipt.json'
F = Fraction
ZERO = (F(0), F(0))
ONE = (F(1), F(0))
IMAG = (F(0), F(1))
DT = F(1, 2)
FIELDS = [('Q', 3, 2, F(1, 6)), ('u_c', -3, 1, F(-2, 3)),
          ('d_c', -3, 1, F(1, 3)), ('L', 1, 2, F(-1, 2)),
          ('e_c', 1, 1, F(1))]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'),
                       allow_nan=False) + '\n').encode()


def hashed(value):
    return sha256(canonical(value)).hexdigest()


def equal(actual, expected, label):
    """Equality includes scalar types, so booleans cannot replace integers."""
    require(type(actual) is type(expected), label + ': type')
    if isinstance(expected, dict):
        require(actual.keys() == expected.keys(), label + ': keys')
        for key in expected:
            equal(actual[key], expected[key], label + '/' + key)
    elif isinstance(expected, (list, tuple)):
        require(len(actual) == len(expected), label + ': length')
        for a, b in zip(actual, expected):
            equal(a, b, label)
    else:
        require(actual == expected, label + ': value')


def fraction(value):
    require(type(value) is str and len(value) <= 12000, 'canonical fraction string')
    try:
        result = F(value)
    except (ValueError, ZeroDivisionError):
        raise ValueError('invalid rational') from None
    require(str(result) == value, 'noncanonical rational')
    return result


def complex_value(value):
    require(type(value) is list and len(value) == 2, 'Gaussian rational pair')
    return tuple(fraction(x) for x in value)


def encode(value):
    return [str(x) for x in value] if type(value) is tuple else str(value)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def neg(a):
    return -a[0], -a[1]


def sub(a, b):
    return add(a, neg(b))


def scale(c, a):
    return c * a[0], c * a[1]


def mul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def conj(a):
    return a[0], -a[1]


def norm(a):
    return a[0] ** 2 + a[1] ** 2


def power(a, exponent):
    require(type(exponent) is int, 'integer compact charge')
    require(norm(a) == 1, 'unit compact link')
    if exponent < 0:
        a, exponent = conj(a), -exponent
    result = ONE
    for _ in range(exponent):
        result = mul(result, a)
    return result


def inner(a, b):
    return tuple(sum(x[k] for x in (mul(conj(u), v) for u, v in zip(a, b)))
                 for k in range(2))


def spin_kernel(axis, transport, vector, adjoint=False):
    """Apply i sigma_axis U; obtain its adjoint independently by conjugation."""
    require(axis in (0, 1, 2), 'axis')
    x, y = vector
    if axis == 0:
        answer = mul(IMAG, y), mul(IMAG, x)
    elif axis == 1:
        answer = y, neg(x)
    else:
        answer = mul(IMAG, x), neg(mul(IMAG, y))
    if adjoint:
        return tuple(neg(mul(conj(transport), z)) for z in answer)
    return tuple(mul(transport, z) for z in answer)


def midpoint_residual(old_u, old_v, new_u, new_v, axis, transport):
    """Zero is exactly i delta psi = dt h psi_mid for the Hermitian edge."""
    middle_u = tuple(scale(F(1, 2), add(a, b)) for a, b in zip(old_u, new_u))
    middle_v = tuple(scale(F(1, 2), add(a, b)) for a, b in zip(old_v, new_v))
    right_u = spin_kernel(axis, transport, middle_v)
    right_v = spin_kernel(axis, transport, middle_u, adjoint=True)
    for old, new, rhs in zip(old_u + old_v, new_u + new_v, right_u + right_v):
        require(mul(IMAG, sub(new, old)) == scale(DT, rhs), 'midpoint stationarity')
    require(sum(map(norm, old_u + old_v)) == sum(map(norm, new_u + new_v)),
            'edge unitarity')
    return inner(middle_u, right_u)[1]


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def load(path=OUTPUT):
    path = Path(path)
    require(path.stat().st_size <= 40000000, 'receipt size')
    def reject(_):
        raise ValueError('nonintegral JSON number')
    return json.loads(path.read_text(), object_pairs_hook=unique,
                      parse_float=reject, parse_constant=reject)


SCOPE = {
    'finite_CAR_bilinear_and_occupied_Slater_orbitals': True,
    'complete_one_generation_representation_census': True,
    'hypercharge_edge_factors_on_prepared_q5_sites': True,
    'same_midpoint_variational_current_and_electric_feedback': True,
    'exact_discrete_charge_continuity_and_expectation_Gauss': True,
    'authenticated_register_read_write_replay': True,
    'nonabelian_gauge_or_Yukawa_dynamics': False,
    'operator_Gauss_constraint_or_quantized_electric_field': False,
    'continuous_time_trajectory_error_bound': False,
    'quantum_anomaly_cancellation_from_regulator_or_measure': False,
    'source_selected_action_population_or_clock': False,
    'physical_spin_signal_order_or_laboratory_identification': False,
    'inherited_Cartan_scalar_or_Whitney_trajectory_bound': False,
}
PREMISES = [
    'Prepared q5 golden addresses, oriented nearest-neighbor graph and fixed Pauli frame.',
    'Registered all-left-Weyl multiplets with one generation; CAR and occupied Slater state are supplied.',
    'Uniform hopping k=1 and local Cayley duration dt=1/2 are declared independently of scalar conductances.',
    'Compact U1 link acts with integer charge q=6Y; its angle and electric momentum use that declared normalization.',
    'Only number-conserving hypercharge hopping factors evolve; Higgs, Yukawa, gauge-electric and plaquette factors are absent.',
    'Electric momentum is a classical mean-field coordinate driven by the CAR expectation current.',
    'Exact rational arithmetic, protected records and classical read/write access are supplied.',
]
LAW = {
    'step': '1/2', 'hopping': '1',
    'spin_link': 'K_e=i*sigma_axis*U_e^q, with Pauli axes x,y,z',
    'Hamiltonian_factor': 'k*(c_u^dagger*K_e*c_v+c_v^dagger*K_e^dagger*c_u)',
    'one_particle_equation': 'i*(psi_new-psi_old)/dt=H_e*(psi_new+psi_old)/2',
    'orbital_state': 'one normalized occupied orbital for each distinct internal component; 15 orthogonal blocks',
    'midpoint_covariance': 'sum of midpoint orbital outer products, a positive contraction; not a normalized 15-particle Slater state or a continuous-time midpoint',
    'electric_feedback': 'E_new=E_old-dt*J_mid, J_mid=d_theta<E_mid> with U->exp(i*theta)*U',
    'current': '-2*k*sum_species(multiplicity*q*Im(mid_u^dagger*K_e*mid_v))',
    'charge': 'sum_species(multiplicity*q*norm_squared(orbital_at_site))',
    'gauss': 'outward_divergence(E)-expectation_charge',
    'charge_variance': 'sum_species(multiplicity*q^2*p_site*(1-p_site)); electric field is a number',
    'schedule': 'one ascending sweep over all 144 edges; each factor consumes the current endpoint orbitals',
    'initial_orbital_at_each_site': [['3/40', '0'], ['1/10', '0']],
    'intervention': {'multiplet': 'e_c', 'site': 21, 'phase': ['3/5', '4/5']},
    'gauge_rule': 'g_site=phase^(site_mod_3_minus_1); psi->g^q*psi; U_uv->g_u*U_uv*conj(g_v)',
    'operator_boundary': 'nonzero local charge variance excludes operator Gauss for the declared classical E',
    'readout_current': 'instantaneous current uses checkpoint orbitals; factor_current registers use that edge factor midpoint',
}
SOURCE_PATHS = tuple('code/sm_fermion_current/' + name for name in
                    ('current.py', 'build_current.py', 'verify_current.py', 'test_current.py', 'README.md')) + (
    'code/sm_local_action/jet_action.py', 'code/sm_abelian_reduction/pilot.py',
    'Lean/Screen/WeylYukawaConventions.lean', 'Lean/Screen/A5FamilyBand.lean')
PARENT_HASHES = {
    'code/sm_local_action/jet_action.py': 'bb9fdb42ca749b8752971b373ef3401eaeced44c7f4e1b91f53942d84ee84309',
    'code/sm_abelian_reduction/pilot.py': 'babf18861777c821f684c6e9d6c91af72b2c31779a06dc169fccda7e5e30a9c9',
    'Lean/Screen/WeylYukawaConventions.lean': '0fd0afdcbce58336979dcd1bdf8fc7f39bfa5c7bf42c8f2625324faebb9d7ef6',
    'Lean/Screen/A5FamilyBand.lean': '69254937a0f80d9ccb92c1dfc23c44f30e6b68c86b7d82eba8f26c39111f5964',
}


def validate_custody(packet):
    require(type(packet) is dict and set(packet) == {
        'schema', 'scope', 'premises', 'law', 'geometry', 'multiplets',
        'source_pins', 'runs', 'comparisons'}, 'root schema')
    equal(packet['schema'], 'oph.sm_fermion_current.v1', 'schema')
    equal(packet['scope'], SCOPE, 'scope')
    equal(packet['premises'], PREMISES, 'premises')
    equal(packet['law'], LAW, 'law')
    require(type(packet['source_pins']) is dict and set(packet['source_pins']) == set(SOURCE_PATHS),
            'source pin census')
    for path in SOURCE_PATHS:
        data = (ROOT / path).read_bytes()
        equal(packet['source_pins'][path], {'bytes': len(data), 'sha256': sha256(data).hexdigest()},
              'source pin content')
        if path in PARENT_HASHES:
            require(sha256(data).hexdigest() == PARENT_HASHES[path], 'immutable parent identity')
    return {'custody_verified': True, 'mathematical_replay': False}


def multiplet_check(received):
    expected = [{'name': n, 'color_dimension_signed': c, 'weak_dimension': w,
                 'multiplicity': abs(c) * w, 'hypercharge': str(y), 'integer_charge': int(6 * y)}
                for n, c, w, y in FIELDS]
    equal(received, expected, 'complete generation')
    return expected


def geometry_check(received):
    # Exact q=5 orbit, derived without importing the scalar geometry producer.
    orbit = [(0, 0), (-3, 2), (-6, 4), (-1, 1), (-4, 3)]
    xyzs = list(itertools.product(range(1, 5), repeat=3))
    ids = {xyz: i for i, xyz in enumerate(xyzs)}
    sites, edges = [], []
    for i, xyz in enumerate(xyzs):
        addresses = [orbit[k] for k in xyz]
        a, b = zip(*addresses)
        z = [b[1] - a[0], b[1] + a[0], b[2] - a[1], b[2] + a[1],
             b[0] - a[2], b[0] + a[2]]
        half = sum(z) // 2
        currents = [-z[5], half - z[0], half - z[2] - z[3],
                    half - z[1] - z[4] - z[5], half - z[2] - z[3] - z[4], z[3]]
        sites.append({'index': list(xyz), 'address_Qphi': [list(a) for a in addresses],
                      'source_record': z, 'source_seam_currents': currents})
        for axis in range(3):
            if xyz[axis] < 4:
                neighbor = tuple(n + int(k == axis) for k, n in enumerate(xyz))
                edges.append({'ends': [i, ids[neighbor]], 'axis': axis})
    expected = {'q': 5, 'orbit_order': [0, 2, 4, 1, 3], 'sites': sites, 'edges': edges,
                'parent_geometry_scope': 'same golden sites and oriented adjacency; scalar masses, conductances and plaquette law are not reused'}
    equal(received, expected, 'geometry')
    require(len(sites) == 64 and len(edges) == 144, 'geometry census')
    return expected


def port(name, site, spin):
    return f'orbital/{name}/{site}/{spin}'


def spinor(state, name, site):
    return tuple(state[port(name, site, a)] for a in range(2))


def probability(state, name, site):
    return sum(map(norm, spinor(state, name, site)))


def read_observables(state, geometry):
    charge, variance, orbital_norms = [F(0)] * 64, [F(0)] * 64, {}
    for name, color, weak, Y in FIELDS:
        multiplicity, q = abs(color) * weak, int(6 * Y)
        probabilities = [probability(state, name, site) for site in range(64)]
        orbital_norms[name] = str(sum(probabilities))
        require(sum(probabilities) == 1 and all(0 <= p <= 1 for p in probabilities),
                'occupied Slater projector normalization/Pauli bound')
        for site, p in enumerate(probabilities):
            charge[site] += multiplicity * q * p
            variance[site] += multiplicity * q * q * p * (1 - p)
    require(sum(charge) == 0, 'global charge conservation')
    gauss = [-p for p in charge]
    electric, currents = [], []
    for edge, row in enumerate(geometry['edges']):
        u, v = row['ends']
        E, U = state[f'electric/{edge}'], state[f'link/{edge}']
        require(norm(U) == 1, 'unit compact link')
        gauss[u] += E
        gauss[v] -= E
        current = F(0)
        for name, color, weak, Y in FIELDS:
            q, m = int(6 * Y), abs(color) * weak
            transported = spin_kernel(row['axis'], power(U, q), spinor(state, name, v))
            current -= 2 * m * q * inner(spinor(state, name, u), transported)[1]
        currents.append(str(current))
        electric.append(str(E))
    require(not any(gauss), 'expectation Gauss constraint')
    return {'charge': list(map(str, charge)), 'charge_variance': list(map(str, variance)),
            'electric': electric, 'gauss_residual': list(map(str, gauss)),
            'instantaneous_current': currents, 'orbital_norms': orbital_norms}


def replay(run, geometry):
    require(type(run) is dict and set(run) == {'cohort', 'events', 'checkpoints', 'final_event_hash'}, 'run schema')
    cohort = run['cohort']
    require(cohort in ('baseline', 'phase_intervention', 'gauge_copy'), 'cohort')
    event_count = 610 + int(cohort != 'baseline') + int(cohort == 'gauge_copy')
    require(type(run['events']) is list and len(run['events']) == event_count, 'complete event census')
    require(type(run['checkpoints']) is list and len(run['checkpoints']) == 2, 'checkpoint census')
    state, recorded, versions, writers = {}, {}, {}, {}
    index, previous = 0, '0' * 64
    snapshots = []

    def take(operation, reads, writes, metadata):
        nonlocal index, previous
        ev = run['events'][index]
        require(type(ev) is dict and set(ev) == {'id', 'operation', 'metadata', 'reads', 'parents',
                                              'writes', 'previous_hash', 'event_hash'}, 'event schema')
        equal(ev['id'], index, 'event id')
        equal(ev['operation'], operation, 'operation')
        equal(ev['metadata'], metadata, 'metadata')
        equal(ev['previous_hash'], previous, 'event chain')
        equal(ev['event_hash'], hashed({k: v for k, v in ev.items() if k != 'event_hash'}), 'event digest')
        names = sorted(set(reads))
        equal(ev['reads'], [{'port': k, 'version': versions[k], 'writer': writers[k], 'value': recorded[k]}
                            for k in names], 'actual read versions/writers/values')
        equal(ev['parents'], sorted({writers[k] for k in names}), 'actual semantic parents')
        equal(ev['writes'], [{'port': k, 'version': versions.get(k, -1) + 1, 'value': encode(writes[k])}
                             for k in sorted(writes)], 'operation writes')
        for key, value in writes.items():
            state[key], recorded[key] = value, encode(value)
            versions[key], writers[key] = versions.get(key, -1) + 1, index
        previous, index = ev['event_hash'], index + 1

    for name, _, _, _ in FIELDS:
        for site in range(64):
            take('prepare_orbital', [], {port(name, site, 0): (F(3, 40), F(0)),
                                        port(name, site, 1): (F(1, 10), F(0))},
                 {'multiplet': name, 'site': site})
    for edge in range(144):
        take('prepare_link', [], {f'link/{edge}': ONE, f'electric/{edge}': F(0)}, {'edge': edge})
    phase = (F(3, 5), F(4, 5))
    if cohort != 'baseline':
        names = [port('e_c', 21, a) for a in range(2)]
        take('phase_intervention', names, {k: mul(phase, state[k]) for k in names},
             {'multiplet': 'e_c', 'site': 21})
    if cohort == 'gauge_copy':
        updates = {}
        g = [power(phase, site % 3 - 1) for site in range(64)]
        for name, _, _, Y in FIELDS:
            for site in range(64):
                for spin in range(2):
                    key = port(name, site, spin)
                    updates[key] = mul(power(g[site], int(6 * Y)), state[key])
        for edge, row in enumerate(geometry['edges']):
            u, v = row['ends']
            key = f'link/{edge}'
            updates[key] = mul(mul(g[u], state[key]), conj(g[v]))
        take('gauge_transform', list(updates), updates, {'site_exponent_rule': 'site_mod_3_minus_1'})

    def readout(label):
        take('readout', [k for k in state if not k.startswith('factor_current/')], {}, {'checkpoint': label})
        expected = read_observables(state, geometry)
        equal(run['checkpoints'][len(snapshots)], {'event': index - 1, 'readout': expected}, 'public readout')
        snapshots.append((dict(state), expected))

    readout('initial')
    for edge, row in enumerate(geometry['edges']):
        u, v = row['ends']
        names = [port(name, site, spin) for name, _, _, _ in FIELDS for site in (u, v) for spin in range(2)]
        expected_ports = sorted(names + [f'electric/{edge}', f'factor_current/{edge}'])
        rows = run['events'][index].get('writes')
        require(type(rows) is list and all(type(r) is dict and set(r) == {'port', 'version', 'value'} for r in rows),
                'edge write schema')
        equal([r['port'] for r in rows], expected_ports, 'edge local write set')
        supplied = {r['port']: r['value'] for r in rows}
        updates = {key: complex_value(supplied[key]) for key in names}
        current, rho_delta = F(0), F(0)
        for name, color, weak, Y in FIELDS:
            q, multiplicity = int(6 * Y), abs(color) * weak
            old_u, old_v = spinor(state, name, u), spinor(state, name, v)
            new_u, new_v = spinor(updates, name, u), spinor(updates, name, v)
            imag = midpoint_residual(old_u, old_v, new_u, new_v, row['axis'], power(state[f'link/{edge}'], q))
            j = -2 * multiplicity * q * imag
            delta = multiplicity * q * (sum(map(norm, new_u)) - sum(map(norm, old_u)))
            require(delta == -DT * j, 'same-current local continuity')
            current += j
            rho_delta += delta
        updates[f'factor_current/{edge}'] = current
        updates[f'electric/{edge}'] = state[f'electric/{edge}'] - DT * current
        require(updates[f'electric/{edge}'] - state[f'electric/{edge}'] == rho_delta,
                'every-factor Gauss preservation')
        take('edge_factor', names + [f'link/{edge}', f'electric/{edge}'], updates, {'edge': edge})
    readout('final')
    equal(run['final_event_hash'], previous, 'terminal hash')
    require(index == len(run['events']), 'unconsumed events')
    return snapshots


def verify(packet):
    validate_custody(packet)
    multiplet_check(packet['multiplets'])
    geometry = geometry_check(packet['geometry'])
    require(type(packet['runs']) is list and len(packet['runs']) == 3, 'run census')
    equal([r.get('cohort') for r in packet['runs']], ['baseline', 'phase_intervention', 'gauge_copy'], 'cohort order')
    baseline, active, gauge = [replay(run, geometry) for run in packet['runs']]
    for (a, ar), (g, gr) in zip(active, gauge):
        equal(gr, ar, 'gauge-invariant public readout')
        phase = (F(3, 5), F(4, 5))
        for name, _, _, Y in FIELDS:
            for site in range(64):
                factor = power(phase, (site % 3 - 1) * int(6 * Y))
                for spin in range(2):
                    key = port(name, site, spin)
                    require(g[key] == mul(factor, a[key]), 'gauge-covariant occupied orbital')
    differences = {key: [str(F(b) - F(a)) for a, b in zip(baseline[-1][1][key], active[-1][1][key])]
                   for key in ('charge', 'electric', 'instantaneous_current')}
    require(any(F(x) for x in differences['electric']), 'nonzero intervention electric response')
    initial_variance = sum(abs(c) * w * int(6 * y) ** 2 for _, c, w, y in FIELDS) * F(1, 64) * F(63, 64)
    require(initial_variance == F(945, 512), 'nonzero quantum charge variance')
    for cohort in (baseline, active, gauge):
        equal(cohort[0][1]['charge_variance'], ['945/512'] * 64, 'initial local variance')
    charges = [int(6 * y) for _, _, _, y in FIELDS]
    expected = {'gauge_invariant_public_records_equal': True,
                'intervention_minus_baseline_final': differences,
                'initial_local_charge_variance': str(initial_variance),
                'generation_anomaly_sums_integer_charge': {
                    'mixed_gravity_U1': sum(abs(c) * w * int(6 * y) for _, c, w, y in FIELDS),
                    'U1_cubed': sum(abs(c) * w * int(6 * y) ** 3 for _, c, w, y in FIELDS),
                    'SU3_squared_U1_twice_Dynkin': 2 * charges[0] + charges[1] + charges[2],
                    'SU2_squared_U1_twice_Dynkin': 3 * charges[0] + charges[3],
                    'SU2_doublet_count': 4,
                    'SU3_cubed': 0,
                    'SU2_global_parity': 0,
                }}
    equal(packet['comparisons'], expected, 'scientific comparison')
    return {'verified': True, 'exact_rational_replay': True, 'sites': 64, 'links': 144,
            'one_particle_modes': 64 * 2 * 15, 'occupied_fermions': 15,
            'multiplets': 5, 'events': 1833, 'local_factors': 432,
            'endpoint_Slater_projector_rank': 15, 'initial_local_charge_variance': str(initial_variance),
            'expectation_Gauss': True, 'operator_Gauss': False,
            'continuous_time_error_bound': False, 'physical_current_attached': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('path', nargs='?', type=Path, default=OUTPUT)
    print(json.dumps(verify(load(parser.parse_args().path)), sort_keys=True, indent=2))

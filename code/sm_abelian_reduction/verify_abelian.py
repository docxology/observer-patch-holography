"""Producer-free symbolic reduction and high-precision operation replay.

The exact algebraic theorem and the numerical execution checks are separate.
No numerical tolerance is a continuous-time or floating-roundoff enclosure.
"""
import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path
from types import ModuleType
import mpmath as mp
import sympy as s

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUTPUT = HERE/'abelian_receipt.json'
PARENT_COMMIT = '78f71f4f6f8dc94f80a7e20fe8dd5ea497775e0c'
PARENT_HASHES = {'code/sm_local_action/jet_action.py': 'bb9fdb42ca749b8752971b373ef3401eaeced44c7f4e1b91f53942d84ee84309', 'code/sm_local_action/local_action_receipt.json': '98f767a0cbec83d5aac34bb2cd6458d382b023a5ec6073e0a62c768afe4532ea', 'paper/tex_fragments/LOCAL_SM_JET_ACTION.tex': '32e5db604305f454d628079e601be84a4f0f658dab710af44ea95f59da87736f', 'code/source_scalar_packet/source_common_scalar.py': '7eb6dbaef13a1cf677160eecd443008c50878f37f160c60613c0363866b5f02e', 'code/causal_refinement/source_net_causet.py': 'c5301509c585234db36840abcb4ab2609e0455a81413223a115348496492e2d0', 'code/causal_refinement/verify_source_net_causet.py': '11a3fe8ddfc8142217bdc6dbc46aa1ea8cb494b5c1f3ad3fe947a5ce328034b4', 'Lean/Screen/PrimitivePortFrameQuotient.lean': '7691fe7b9536e81a2839a85d28c42bb123d10f4e107c58c0577dac323abc316f', 'Lean/Screen/SeamCurrentCarrierQuotient.lean': '8c14d65c66f4ffdc1f8c303168d1b302760b36ce726ec6f3a1f91ceb7e4aa2cb', 'Lean/Screen/PortFrameGram.lean': 'c232cb5cc82423c29ccd6fc4b71193d32e6067fcdd134c7cf45948277f389616'}
SOURCE_PATHS = tuple('code/sm_abelian_reduction/'+p for p in
                    ('reduction.py', 'pilot.py', 'build_abelian.py', 'verify_abelian.py', 'test_abelian.py', 'README.md'))+(
                    'paper/tex_fragments/CARTAN_SCALAR_REDUCTION.tex', 'Lean/Screen/CartanScalarReduction.lean')
SCOPE = {'local_classical_full_action_reduction': True,
         'discrete_log_plaquette_chart_required': True,
         'prepared_golden_addresses_same_tensor_weights': True,
         'nonzero_variational_current_and_electric_feedback': True,
         'ideal_split_gauss_preservation': True, 'numerical_local_operation_replay': True,
         'continuous_history_error_enclosure': False, 'inherited_q233_detector_error': False,
         'native_action_population_routing_or_clock_selected': False,
         'physical_units_or_electromagnetic_identification': False,
         'global_compact_subgroup_or_quantum_truncation': False,
         'full_SM_fermion_dynamics_executed': False,
         'audit_serial_order_is_signal_order': False,
         'count_clock_attached_to_field_substeps': False}
UNITS = {'position': 'x/L with L=2/sqrt(phi+2)', 'time': 'declared c*t/L',
         'step': '1/200', 'completed_window': ['0', '1/100'],
         'charge': 'reduced scalar charge 1; no laboratory calibration',
         'connections': 'real unwrapped link integrals; not compact phase records',
         'field_normalization': 'Lagrangian scalar kinetic coefficient 1',
         'precision': 'binary64 history; independent 60-decimal operation replay, not an enclosure'}
LAW = {'kappa_1': '1', 'kappa_2': '1', 'd': '3/8', 'w_standard': ['4/3', '2/3'],
       'm_squared': '1', 'lambda': '1/4', 'higgs': '(psi,0)',
       'electric_mass': '(1/d)*transverse_dual_area/edge_gap',
       'magnetic_weight': '(1/d)*normal_dual_length/plaquette_area',
       'scalar_momentum': 'pi=mass*D0(psi); symplectic form 2 Re(d(conj(pi)) wedge d(psi))',
       'edge_energy': 'conductance*abs(exp(i*a)*psi_j-psi_i)^2',
       'current': '-2*conductance*Im(conj(psi_i)*exp(i*a)*psi_j)',
       'charge': '2*Im(conj(psi_i)*pi_i)', 'gauss': 'charge+outward_divergence(P)',
       'schedule': 'two steps: potential half-kick, scalar and electric drift, potential half-kick',
       'boundary': 'fixed zero scalar on cube boundary; no external charged source; internal gauge edges only',
       'semantics': 'reads consume exact latest writer/version; static geometry is the immutable law input',
       'log_chart': 'abs((4/3)*curl(a))<2*pi on every internal plaquette'}


def require(ok, label):
    if not ok: raise ValueError(label)


def canonical(x):
    return (json.dumps(x, sort_keys=True, separators=(',', ':'), allow_nan=False)+'\n').encode()


def hashed(x): return hashlib.sha256(canonical(x)).hexdigest()


def unique(pairs):
    answer = {}
    for k, v in pairs:
        require(k not in answer, 'duplicate JSON key'); answer[k] = v
    return answer


def load(path=OUTPUT):
    path = Path(path); require(path.stat().st_size <= 18000000, 'receipt size')
    def finite(token):
        number = float(token); require(math.isfinite(number), 'nonfinite JSON number'); return number
    return json.loads(path.read_text(), object_pairs_hook=unique,
                      parse_float=finite,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))


def same(a, b, label):
    """Exact schema and scalar typing, with numeric tolerance only for mp values."""
    if isinstance(b, (mp.mpf, mp.mpc)):
        if isinstance(b, mp.mpc):
            require(type(a) is list and len(a) == 2, label+' complex shape')
            same(a[0], b.real, label); same(a[1], b.imag, label)
        else:
            require(type(a) is float and math.isfinite(a), label+' finite float')
            require(abs(mp.mpf(a)-b) <= mp.mpf('5e-12')*(1+abs(b)), label+' numerical value')
    elif isinstance(b, dict):
        require(type(a) is dict and set(a) == set(b), label+' keys')
        for k in b: same(a[k], b[k], label+'/'+k)
    elif isinstance(b, (list, tuple)):
        require(type(a) is list and len(a) == len(b), label+' length')
        for x, y in zip(a, b): same(x, y, label)
    else: require(type(a) is type(b) and a == b, label+' exact value')


def validate_custody(packet):
    keys = {'schema', 'scope', 'units', 'law', 'parent_commit', 'parent_pins', 'source_pins',
            'reduction', 'geometry', 'runs', 'exact_first_edge_control', 'producer_only_diagnostic'}
    require(type(packet) is dict and set(packet) == keys, 'root schema')
    same(packet['schema'], 'oph.cartan-scalar-current.v1', 'schema')
    same(packet['scope'], SCOPE, 'scientific scope'); same(packet['units'], UNITS, 'units')
    same(packet['law'], LAW, 'law'); same(packet['parent_commit'], PARENT_COMMIT, 'parent commit')
    require(len(PARENT_HASHES) == 9, 'immutable parent census')
    for field, paths in [('parent_pins', tuple(PARENT_HASHES)), ('source_pins', SOURCE_PATHS)]:
        require(type(packet[field]) is dict and set(packet[field]) == set(paths), 'source pin set')
        for path in paths:
            data = (ROOT/path).read_bytes(); digest = hashlib.sha256(data).hexdigest()
            same(packet[field][path], {'sha256': digest, 'bytes': len(data)}, 'source pins')
            if field == 'parent_pins': require(digest == PARENT_HASHES[path], 'immutable parent identity')
    diag = packet['producer_only_diagnostic']
    require(type(diag) is dict and set(diag) == {'reverse_potential_order_final_max_difference', 'independently_replayed'}, 'diagnostic schema')
    require(diag['independently_replayed'] is False, 'producer diagnostic boundary')
    v = diag['reverse_potential_order_final_max_difference']
    require(type(v) is float and math.isfinite(v) and v >= 0, 'producer diagnostic finite')
    return {'accepted_custody': True, 'mathematical_replay': False}


def reduction_check(row):
    a, b = s.symbols('k1 k2', positive=True)
    # Direct generator traces determine the kinetic coefficients independently.
    tw, ty = s.I*s.diag(1, -1)/2, s.Matrix([[s.I]])
    kw, ky = -2*b*s.trace(tw*tw), -2*a*s.trace(ty*ty)
    require(kw == b and ky == 2*a, 'trace normalization')
    denom = s.factor(s.Rational(1, 4)/kw+s.Rational(1, 4)/ky)
    weights = [s.factor(1/(2*kw*denom)), s.factor(1/(2*ky*denom))]
    require(s.simplify(sum(weights)/2-1) == 0, 'unit reduced charge')
    require(s.simplify(kw*weights[0]-ky*weights[1]) == 0, 'omitted Cartan equation')
    require(s.simplify(kw*weights[0]**2+ky*weights[1]**2-1/denom) == 0, 'reduced Maxwell normalization')
    code_d = 1/(4*b)+s.Rational(1, 4)/(2*a)
    require(s.simplify(code_d-denom) == 0, 'code basis normalization')
    x, y, u, v = s.symbols('x y u v', real=True)
    H = s.Matrix([x+s.I*y, 0]); D = s.Matrix([u+s.I*v, 0])
    ts = [s.I*s.Matrix([[0, 1], [1, 0]])/2, s.Matrix([[0, 1], [-1, 0]])/2,
          tw, s.I*s.eye(2)/2]
    currents = [s.expand(2*s.re((D.conjugate().T*T*H)[0])) for T in ts]
    require(currents[:2] == [0, 0] and currents[2] == currents[3], 'omitted weak currents')
    # The polynomial identities hold with arbitrary scalar values/first jets.
    require(all((T*H)[1] == 0 for T in ts[2:]), 'lower Higgs invariant line')
    for T in ts[:2]:
        require(s.trace(tw*T) == 0 and s.trace(tw*(tw*T-T*tw)) == 0, 'off-Cartan gauge trace')
    # Finite diagonal holonomies, not only an infinitesimal zero connection.
    r, t, z, k = s.symbols('r t z k', real=True)
    diagonal = s.diag(r+s.I*t, r-s.I*t)
    U = (z+s.I*k)*diagonal
    diff = U*H-D
    for T in ts[:2]:
        for variation in (T*U, U*T):
            require(s.expand(2*s.re(((variation*H).conjugate().T*diff)[0])) == 0,
                    'finite-link omitted weak current')
            require(s.trace(tw*variation) == 0, 'finite-link omitted gauge trace')
    parent = load(ROOT/'code/sm_local_action/local_action_receipt.json')
    ys = [v for k, v in parent['action_coefficients'].items() if k.startswith('Y_')]
    require(len(ys) == 54 and all(len(mask) == 2 for terms in ys for mask, _ in terms), 'fermionic Yukawa degree')
    expected = {'standard_q': ['1/2', '1/2'], 'standard_K': ['k2', '2*k1'],
                'code_q': ['1', '1/2'], 'code_K': ['4*k2', '2*k1'],
                'd': str(denom), 'w': [str(w) for w in weights], 'identities': ['0']*8,
                'weak_and_hypercharge_currents': [str(c) for c in currents],
                'unrestricted_complex_yukawa_slots': 27, 'retained_yukawa_real_sectors': 54,
                'yukawa_monomial_degree': 2,
                'hypercharge_only_orthogonal_gauge_defect_at_k1_k2_1': '-4',
                'omitted_equations': ['color', 'weak_1', 'weak_2', 'lower_Higgs', 'fermions_and_independent_conjugates', 'orthogonal_Cartan'],
                'local_log_plaquette_condition': 'abs(w_weak * curl(A)) < 2*pi',
                'general_coefficients': 'k1,k2 positive constants; m_squared,lambda real; Yukawas complex'}
    same(row, expected, 'reduction')
    # Exact generic edge kick: current is the derivative, and both end Gauss
    # constraints cancel. Unit phase is represented by cos/sin of real a.
    xi, yi, xj, yj, angle, c, h = s.symbols('xi yi xj yj angle c h', real=True)
    z, w, U = xi+s.I*yi, xj+s.I*yj, s.exp(s.I*angle)
    V = s.expand_complex(c*s.conjugate(U*w-z)*(U*w-z))
    J = -s.diff(V, angle)
    fi, fj = c*(U*w-z), c*(s.conjugate(U)*z-w)
    require(s.simplify(s.expand_complex(2*s.im(s.conjugate(z)*fi)+J)) == 0, 'first endpoint continuity')
    require(s.simplify(s.expand_complex(2*s.im(s.conjugate(w)*fj)-J)) == 0, 'second endpoint continuity')


def geometry_check(received):
    phi = (1+mp.sqrt(5))/2
    orbit = sorted([(b, int(mp.floor(b*phi))) for b in range(5)],
                   key=lambda pair: pair[0]*phi-pair[1])
    order = [b for b, _ in orbit]
    x = [b*phi-floor for b, floor in orbit]+[mp.mpf(1)]
    dx = [x[k+1]-x[k] for k in range(5)]
    m = [(dx[k]+dx[k+1])/2 for k in range(4)]
    indices = list(itertools.product(range(1, 5), repeat=3)); ids = {v: k for k, v in enumerate(indices)}
    # Authenticated owning verifier supplies the independent 12-port incidence
    # and all 36 source-Gram identities; no producer helper is imported.
    path = ROOT/'code/causal_refinement/verify_source_net_causet.py'
    parent = ModuleType('_abelian_source_basis'); parent.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), parent.__dict__)
    left, right, positive, axes = parent.source_basis()
    sites = []
    for xyz in indices:
        b = [orbit[j][0] for j in xyz]; a = [-orbit[j][1] for j in xyz]
        currents = [-a[2]-b[0], a[0]+b[0]+b[2], b[0]+b[1]-b[2],
                    -a[0]-b[0]+b[2], a[2]+b[1]-b[2], a[1]+b[2]]
        loads = [0]*12
        for seam, value in zip((5, 8, 12, 13, 22, 24), currents):
            loads[left[seam]] -= value; loads[right[seam]] += value
        z = [loads[j]-loads[11-j] for j in positive]
        for k in range(3):
            coeff = [sum(z[j]*axes[j][k][l] for j in range(6))/4 for l in range(2)]
            require(coeff == [a[k]+b[k]/2, b[k]/2], 'source readback')
        mass = mp.fprod(m[j-1] for j in xyz); boundary = mp.mpf(0)
        for axis in range(3):
            if xyz[axis] == 1: boundary += mp.fprod(m[xyz[j]-1] for j in range(3) if j != axis)/dx[0]
            if xyz[axis] == 4: boundary += mp.fprod(m[xyz[j]-1] for j in range(3) if j != axis)/dx[4]
        sites.append({'index': list(xyz), 'address_Qphi': [[a[k], b[k]] for k in range(3)],
                      'source_record': z, 'source_seam_currents': currents,
                      'mass': mass, 'dirichlet_stiffness': boundary})
    edges = []; lookup = {}
    for i, xyz in enumerate(indices):
        for axis in range(3):
            if xyz[axis] < 4:
                nxt = list(xyz); nxt[axis] += 1
                c = mp.fprod(m[xyz[j]-1] for j in range(3) if j != axis)/dx[xyz[axis]]
                lookup[xyz, axis] = len(edges)
                edges.append({'ends': [i, ids[tuple(nxt)]], 'axis': axis, 'conductance': c, 'electric_mass': c*8/3})
    faces = []
    for xyz in indices:
        for a, b in itertools.combinations(range(3), 2):
            if xyz[a] == 4 or xyz[b] == 4: continue
            xa = tuple(v+int(j == a) for j, v in enumerate(xyz))
            xb = tuple(v+int(j == b) for j, v in enumerate(xyz))
            boundary = [[lookup[xyz, a], 1], [lookup[xa, b], 1], [lookup[xb, a], -1], [lookup[xyz, b], -1]]
            balance = [0]*64
            for e, sign in boundary:
                i, j = edges[e]['ends']; balance[i] += sign; balance[j] -= sign
            require(not any(balance), 'boundary of boundary')
            faces.append({'boundary': boundary, 'magnetic_weight': mp.mpf(8)/3*m[xyz[3-a-b]-1]/(dx[xyz[a]]*dx[xyz[b]])})
    geo = {'q': 5, 'fibonacci_index': 5, 'orbit_order': order, 'sites': sites, 'edges': edges, 'plaquettes': faces}
    same(received, geo, 'geometry'); return geo


def replay(run, geo):
    """Independent 60-digit states plus exact serialized read-from custody."""
    require(type(run) is dict, 'run object')
    name = run.get('cohort'); require(name in ('baseline', 'phase_intervention', 'gauge_copy'), 'cohort')
    require(set(run) == {'cohort', 'events', 'checkpoints', 'final_event_hash'}, 'run schema')
    require(type(run['events']) is list and len(run['events']) == 1892+int(name != 'baseline'), 'event census')
    require(type(run['checkpoints']) is list and len(run['checkpoints']) == 4, 'checkpoint census')
    exact = {}; recorded = {}; writers = {}; versions = {}; index = 0; previous = '0'*64
    max_error = mp.mpf(0); max_gauss = mp.mpf(0); snapshots = []
    def take(op, reads, writes, meta):
        nonlocal index, previous, max_error, max_gauss
        require(index < len(run['events']), 'missing operation')
        ev = run['events'][index]
        require(set(ev) == {'id', 'operation', 'metadata', 'reads', 'parents', 'writes', 'previous_hash', 'event_hash'}, 'event schema')
        same(ev['id'], index, 'event id'); same(ev['operation'], op, 'operation'); same(ev['metadata'], meta, 'metadata')
        same(ev['previous_hash'], previous, 'audit chain')
        require(ev['event_hash'] == hashed({k: v for k, v in ev.items() if k != 'event_hash'}), 'event digest')
        names = sorted(set(reads))
        same(ev['reads'], [{'port': k, 'version': versions[k], 'writer': writers[k], 'value': recorded[k]} for k in names], 'actual read-from')
        same(ev['parents'], sorted({writers[k] for k in names}), 'semantic parents')
        expect = [{'port': k, 'version': versions.get(k, -1)+1, 'value': writes[k]} for k in sorted(writes)]
        same(ev['writes'], expect, 'operation result')
        for row in ev['writes']:
            k = row['port']; recorded[k] = row['value']; exact[k] = writes[k]
            writers[k] = index; versions[k] = row['version']
            val = mp.mpc(*row['value']) if isinstance(row['value'], list) else mp.mpf(row['value'])
            max_error = max(max_error, abs(val-writes[k]))
        # Every operation after preparation preserves every Gauss component.
        if len(exact) == 416:
            g = [2*mp.im(mp.conj(exact[f'psi/{i}'])*exact[f'pi/{i}']) for i in range(64)]
            for e, r in enumerate(geo['edges']):
                i, j = r['ends']; g[i] += exact[f'P/{e}']; g[j] -= exact[f'P/{e}']
            max_gauss = max(max_gauss, max(map(abs, g)))
            if any(k.startswith('a/') for k in writes):
                for face in geo['plaquettes']:
                    curl = sum(sign*exact[f'a/{e}'] for e, sign in face['boundary'])
                    require(abs(4*curl/3) < 1, 'every-operation logarithm chart')
        previous = ev['event_hash']; index += 1
    def readout(step, phase):
        take('readout', list(exact), {}, {'step': step, 'phase': phase})
        row = run['checkpoints'][len(snapshots)]
        require(set(row) == {'event', 'step', 'phase', 'values', 'observables'}, 'checkpoint schema')
        same(row['event'], index-1, 'checkpoint join'); same(row['step'], step, 'checkpoint step'); same(row['phase'], phase, 'checkpoint phase')
        same(row['values'], recorded, 'decoded checkpoint values')
        expected = read_observables(geo, exact)
        same(row['observables'], expected, 'physical readout')
        require(expected['max_weak_plaquette_angle'] < 1, 'logarithmic chart margin')
        snapshots.append((dict(exact), expected))
    for i in range(64): take('prepare_site', [], {f'psi/{i}': mp.mpc(1)/5, f'pi/{i}': mp.mpc(0)}, {'site': i})
    for e in range(144): take('prepare_link', [], {f'a/{e}': mp.mpf(0), f'P/{e}': mp.mpf(0)}, {'edge': e})
    if name != 'baseline':
        keys = ['psi/21', 'pi/21']; writes = {k: exact[k]*mp.mpc(3, 4)/5 for k in keys}
        if name == 'gauge_copy':
            for e, row in enumerate(geo['edges']):
                i, j = row['ends']
                if 21 in (i, j):
                    k = f'a/{e}'; keys.append(k); writes[k] = exact[k]+mp.atan(mp.mpf(4)/3)*(int(i == 21)-int(j == 21))
        take(name, keys, writes, {'site': 21, 'unit_phase': ['3/5', '4/5'], 'gauge_parameter': 'atan2(4,3)' if name == 'gauge_copy' else None})
    def kick(step, part):
        for e, row in enumerate(geo['edges']):
            i, j = row['ends']; c = row['conductance']
            qi, qj, pi, pj, a, P = f'psi/{i}', f'psi/{j}', f'pi/{i}', f'pi/{j}', f'a/{e}', f'P/{e}'
            U = mp.exp(mp.j*exact[a]); fi = c*(U*exact[qj]-exact[qi]); fj = c*(mp.conj(U)*exact[qi]-exact[qj])
            current = 2*c*mp.im(mp.conj(U*exact[qj])*exact[qi])
            take('edge_kick', [qi, qj, pi, pj, a, P], {pi: exact[pi]+fi/400, pj: exact[pj]+fj/400, P: exact[P]+current/400}, {'edge': e, 'step': step, 'part': part})
        for i, row in enumerate(geo['sites']):
            q, p = f'psi/{i}', f'pi/{i}'; norm = mp.re(exact[q])**2+mp.im(exact[q])**2
            grad = (row['mass']*(1+norm/2)+row['dirichlet_stiffness'])*exact[q]
            take('onsite_kick', [q, p], {p: exact[p]-grad/400}, {'site': i, 'step': step, 'part': part})
        for f, row in enumerate(geo['plaquettes']):
            circ = sum(sign*exact[f'a/{e}'] for e, sign in row['boundary'])
            keys = [f'{p}/{e}' for e, _ in row['boundary'] for p in ('a', 'P')]
            take('magnetic_kick', keys, {f'P/{e}': exact[f'P/{e}']-sign*row['magnetic_weight']*circ/400 for e, sign in row['boundary']}, {'plaquette': f, 'step': step, 'part': part})
    readout(0, 'initial')
    for step in (1, 2):
        kick(step, 'first')
        if step == 1: readout(step, 'first_kick')
        for i, row in enumerate(geo['sites']):
            q, p = f'psi/{i}', f'pi/{i}'
            take('scalar_drift', [q, p], {q: exact[q]+exact[p]/(200*row['mass'])}, {'site': i, 'step': step})
        for e, row in enumerate(geo['edges']):
            a, P = f'a/{e}', f'P/{e}'
            take('electric_drift', [a, P], {a: exact[a]+exact[P]/(200*row['electric_mass'])}, {'edge': e, 'step': step})
        kick(step, 'last'); readout(step, 'completed')
    require(index == len(run['events']) and len(snapshots) == len(run['checkpoints']), 'extra events/checkpoints')
    same(run['final_event_hash'], previous, 'final event digest')
    require(max_gauss < mp.mpf('1e-50'), 'independent Gauss drift')
    return snapshots, max_error, max_gauss


def read_observables(geo, state):
    q = [state[f'psi/{i}'] for i in range(64)]; p = [state[f'pi/{i}'] for i in range(64)]
    charge = [2*mp.im(mp.conj(x)*y) for x, y in zip(q, p)]; gauss = charge.copy(); js = []; energy = mp.mpf(0)
    for i, row in enumerate(geo['sites']):
        r = abs(q[i])**2
        energy += abs(p[i])**2/row['mass']+(row['mass']+row['dirichlet_stiffness'])*r+row['mass']*r*r/4
    for e, row in enumerate(geo['edges']):
        i, j = row['ends']; U = mp.exp(mp.j*state[f'a/{e}']); P = state[f'P/{e}']
        js.append(-2*row['conductance']*mp.im(mp.conj(q[i])*U*q[j])); gauss[i] += P; gauss[j] -= P
        energy += P*P/(2*row['electric_mass'])+row['conductance']*abs(U*q[j]-q[i])**2
    angles = []
    for row in geo['plaquettes']:
        f = sum(sign*state[f'a/{e}'] for e, sign in row['boundary']); angles.append(abs(4*f/3))
        energy += row['magnetic_weight']*f*f/2
    return {'charge': charge, 'current': js, 'gauss_residual': gauss, 'scalar_intensity': [abs(x)**2 for x in q],
            'energy': energy, 'max_weak_plaquette_angle': max(angles)}


def verify(packet):
    validate_custody(packet); reduction_check(packet['reduction'])
    with mp.workdps(60):
        geo = geometry_check(packet['geometry'])
        require(type(packet['runs']) is list and all(type(r) is dict for r in packet['runs']) and
                [r.get('cohort') for r in packet['runs']] == ['baseline', 'phase_intervention', 'gauge_copy'], 'cohort order')
        data = [replay(run, geo) for run in packet['runs']]
        base, active, gauge = [r[0] for r in data]
        for (_, x), (_, y) in zip(base, gauge):
            for key in x:
                vals = zip(x[key], y[key]) if isinstance(x[key], list) else [(x[key], y[key])]
                require(all(abs(a-b) < mp.mpf('1e-48') for a, b in vals), 'gauge-copy invariants')
        neighbors = {21}
        for edge in geo['edges']:
            if 21 in edge['ends']: neighbors.update(edge['ends'])
        outside = [i for i in range(64) if i not in neighbors]
        require(len(outside) == 57, 'nonvacuous off-support census')
        for i in outside:
            for p in ('psi', 'pi'):
                require(base[1][0][f'{p}/{i}'] == active[1][0][f'{p}/{i}'], 'first-kick off-support')
        e = next(k for k, row in enumerate(geo['edges']) if row['ends'] == [21, 37])
        # Independent exact golden computation: v_2^2/gap_2 = 1/4.
        phi = (1+s.sqrt(5))/2
        points = [0, 2*phi-3, 4*phi-6, phi-1, 3*phi-4, 1]
        c = s.simplify(((points[3]-points[1])/2)**2/(points[3]-points[2]))
        require(c == s.Rational(1, 4), 'exact golden edge conductance')
        J = s.Rational(8, 125)*c
        exact = {'source_site': 21, 'target_site': 37, 'conductance': str(c), 'initial_scalar': '1/5',
                 'intervention_phase': ['3/5', '4/5'], 'current': str(J), 'electric_half_kick': str(J/400),
                 'meaning': 'exact ideal first edge subflow; binary64 execution is compared numerically'}
        same(packet['exact_first_edge_control'], exact, 'exact current witness')
        require(abs(active[1][0][f'P/{e}']-mp.mpf(1)/25000) < mp.mpf('1e-50'), 'source response sign')
        signal = abs(active[-1][1]['scalar_intensity'][37]-base[-1][1]['scalar_intensity'][37])
        require(signal > mp.mpf('1e-6'), 'transmitted detector signal')
        require(abs(active[-1][0][f'a/{e}']) > mp.mpf('1e-7'), 'recurrent electric connection feedback')
        return {'verified': True, 'mathematical_replay': True, 'sites': 64, 'links': 144, 'plaquettes': 108,
                'events': sum(len(r['events']) for r in packet['runs']), 'cohorts': 3,
                'checkpoints_per_cohort': 4, 'model_time_end': '1/100',
                'numerical_replay_max_abs_error': float(max(r[1] for r in data)),
                'independent_gauss_max_abs': float(max(r[2] for r in data)),
                'neighbor_intensity_response': float(signal), 'nonvacuous_off_support_sites': len(outside),
                'exact_first_current': str(J), 'exact_first_electric_kick': str(J/400),
                'continuous_history_error_enclosure': False,
                'producer_reverse_diagnostic_independently_replayed': False}


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__); ap.add_argument('path', nargs='?', type=Path, default=OUTPUT)
    print(json.dumps(verify(load(ap.parse_args().path)), sort_keys=True, indent=2))

"""Produce the conditional reduction and a numerical source-address pilot."""
import argparse
from pathlib import Path
from hashlib import sha256
from reduction import derive
from pilot import canonical, digest, geometry, execute, observables

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUTPUT = HERE/'abelian_receipt.json'
PARENT_COMMIT = '78f71f4f6f8dc94f80a7e20fe8dd5ea497775e0c'
PARENTS = ('code/sm_local_action/jet_action.py', 'code/sm_local_action/local_action_receipt.json',
           'paper/tex_fragments/LOCAL_SM_JET_ACTION.tex',
           'code/source_scalar_packet/source_common_scalar.py',
           'code/causal_refinement/source_net_causet.py',
           'code/causal_refinement/verify_source_net_causet.py',
           'Lean/Screen/PrimitivePortFrameQuotient.lean',
           'Lean/Screen/SeamCurrentCarrierQuotient.lean', 'Lean/Screen/PortFrameGram.lean')
SOURCES = ('reduction.py', 'pilot.py', 'build_abelian.py', 'verify_abelian.py', 'test_abelian.py', 'README.md')
EXTRA = ('paper/tex_fragments/CARTAN_SCALAR_REDUCTION.tex', 'Lean/Screen/CartanScalarReduction.lean')
SCOPE = {'local_classical_full_action_reduction': True,
         'discrete_log_plaquette_chart_required': True,
         'prepared_golden_addresses_same_tensor_weights': True,
         'nonzero_variational_current_and_electric_feedback': True,
         'ideal_split_gauss_preservation': True,
         'numerical_local_operation_replay': True,
         'continuous_history_error_enclosure': False,
         'inherited_q233_detector_error': False,
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


def pins(paths):
    return {p: {'sha256': sha256((ROOT/p).read_bytes()).hexdigest(), 'bytes': (ROOT/p).stat().st_size} for p in paths}


def build():
    geo = geometry(); runs = []
    for name in ('baseline', 'phase_intervention', 'gauge_copy'):
        run = execute(geo, name)
        for row in run['checkpoints']:
            row['observables'] = observables(geo, row['values'])
        runs.append(run)
    reverse = execute(geo, 'phase_intervention', reverse_kick=True)
    forward = runs[1]['checkpoints'][-1]['values']; backward = reverse['checkpoints'][-1]['values']
    def difference(a, b):
        return max(abs(x-y) for x, y in zip(a, b)) if isinstance(a, list) else abs(a-b)
    return {'schema': 'oph.cartan-scalar-current.v1', 'scope': SCOPE, 'units': UNITS, 'law': LAW,
            'parent_commit': PARENT_COMMIT, 'parent_pins': pins(PARENTS),
            'source_pins': pins(tuple('code/sm_abelian_reduction/'+p for p in SOURCES)+EXTRA),
            'reduction': derive(), 'geometry': geo, 'runs': runs,
            'exact_first_edge_control': {'source_site': 21, 'target_site': 37, 'conductance': '1/4',
                 'initial_scalar': '1/5', 'intervention_phase': ['3/5', '4/5'],
                 'current': '2/125', 'electric_half_kick': '1/25000',
                 'meaning': 'exact ideal first edge subflow; binary64 execution is compared numerically'},
            'producer_only_diagnostic': {'reverse_potential_order_final_max_difference':
                    max(difference(v, backward[k]) for k, v in forward.items()),
                 'independently_replayed': False}}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write', action='store_true'); ap.add_argument('--check', action='store_true')
    args = ap.parse_args(); data = canonical(build())
    if args.write: OUTPUT.write_bytes(data)
    if args.check and OUTPUT.read_bytes() != data: raise ValueError('abelian receipt drift')
    print('CARTAN_SCALAR_PRODUCED', len(data), sha256(data).hexdigest())


if __name__ == '__main__': main()

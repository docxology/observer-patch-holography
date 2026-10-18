"""Independent first-order symplectic and exact clock/instrument verification.

No producer is imported. The full scalar operator is rebuilt from source
edge energies using the independent Q(sqrt(5)) parent implementation. The
old clock and quantum proofs are rerun by the public verify entry point.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import sys
import types

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUTPUT = HERE/'sequential_instrument_receipt.json'
SCALAR = 'code/source_scalar_execution/source_scalar_execution_receipt.json'
CLOCK = 'code/source_scalar_clock_quantum/clock_quantum_receipt.json'
PINS = {
    SCALAR: 'cf246c2caa072334e0d4796c1c6c49d2a231a263ff34281843a1c35c7cdbb69a',
    CLOCK: '26ffdec55a41554af735c39f2198cad2858f9ad24a13c9868bde8b1d7b9697d9',
}
CLOCK_VERIFIER = 'code/source_scalar_clock_quantum/verify_clock_quantum.py'
CLOCK_VERIFIER_SHA = '001cb8258cb531ebb61558babe3eac1d67db4030cb29c75725847e5fcdff5aa5'
FILES = (
    'code/source_scalar_instruments/sequential_instrument.py',
    'code/source_scalar_instruments/verify_sequential_instrument.py',
    'code/source_scalar_instruments/test_sequential_instrument.py',
    'paper/tex_fragments/SOURCE_SCALAR_SEQUENTIAL_INSTRUMENT.tex',
)
SCALE = 10**15


def need(ok, message):
    if not ok: raise ValueError(message)


def raw(x):
    return (json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)+'\n').encode('ascii')


def equal(a,b,message):
    need(raw(a)==raw(b),message)


def load(path=OUTPUT):
    def pairs(items):
        out = {}
        for k,v in items:
            need(k not in out,'duplicate key'); out[k] = v
        return out
    def reject(x): raise ValueError('inexact JSON number '+x)
    data = Path(path).read_bytes(); need(len(data)<250000,'receipt size')
    return json.loads(data,object_pairs_hook=pairs,parse_float=reject,parse_constant=reject)


def current_module(relative, name):
    path = ROOT/relative; previous = sys.modules.get(name)
    module = types.ModuleType(name); module.__file__ = str(path); sys.modules[name] = module
    try: exec(compile(path.read_bytes(),str(path),'exec'),module.__dict__)
    finally:
        if previous is None: sys.modules.pop(name,None)
        else: sys.modules[name] = previous
    return module


def down(x): return F((x*SCALE).numerator//(x*SCALE).denominator,SCALE)
def up(x): return -down(-x)


def bracket(value, R):
    """Integer bisection with exact algebraic signs, independent of producer."""
    left,right = -SCALE,SCALE
    while (value-R(F(left,SCALE))).sign()<0: left *= 2
    while (value-R(F(right,SCALE))).sign()>0: right *= 2
    while right-left>1:
        mid = (left+right)//2
        if (value-R(F(mid,SCALE))).sign()>=0: left = mid
        else: right = mid
    return F(left,SCALE),F(right,SCALE)


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


def check_gadget(packet,mass,action,velocity,g,R):
    sites = [i for i in range(64) if g[i] != R()]; n = len(sites)
    need(sites==list(range(32,64)),'actual detector half')
    root = packet['root_site']; need(type(root) is int and root==min(sites),'GHZ root')
    tree = packet['ghz_cnot_tree']; need(type(tree) is list and len(tree)==n-1,'tree census')
    # Independent CSS stabilizer propagation: all generators stay purely X
    # or purely Z, so no hidden Pauli phase can enter this circuit.
    index = {v:i for i,v in enumerate(sites)}
    stabilizers = [(1<<i,0) if sites[i]==root else (0,1<<i) for i in range(n)]
    visited = {root}
    for edge in tree:
        need(type(edge) is list and len(edge)==2 and all(type(i) is int for i in edge),'typed CNOT')
        u,v = edge
        need(u in visited and v in sites and v not in visited,'ordered connected CNOT tree')
        need(any(j==v and a!=R() for j,a in action[u]),'CNOT outside actual scalar edge')
        a,b = index[u],index[v]
        stabilizers = [(x ^ (((x>>a)&1)<<b), z ^ (((z>>b)&1)<<a)) for x,z in stabilizers]
        visited.add(v)
    need(visited==set(sites),'incomplete GHZ support')
    need(stabilizers[index[root]]==((1<<n)-1,0),'GHZ global X stabilizer')
    zrows = [z for x,z in stabilizers if x==0]
    need(len(zrows)==n-1 and all(z.bit_count()%2==0 for z in zrows),'GHZ even Z stabilizers')
    # Gaussian elimination over F2 independently verifies rank n-1.
    pivots = {}
    for z in zrows:
        while z:
            k = z.bit_length()-1
            if k in pivots: z ^= pivots[k]
            else: pivots[k]=z; break
    need(len(pivots)==n-1,'GHZ stabilizer independence')
    expected = {
        'detector_sites':sites,'root_site':root,
        'coherent_preparation_sites':[i for i in range(64) if velocity[i]!=R()],
        'local_controlled_field_coefficients_Qphi':[[i,(mass[i]*g[i]).encode()] for i in sites],
        'ghz_cnot_tree':tree,
        'local_pointer_readout_bases':[[i,'Y' if i==root else 'X'] for i in sites],
        'pointer_initial_state':'all zero; H on root then the ordered CNOT tree',
        'interaction':'exp(-i Z_i tensor m_i*g_i*q_i/2) at each detector site',
        'binary_record':'XOR of all local pointer outcome bits; bit0 is positive eigenvalue',
        'fine_record_kraus_factor_squared':str(F(1,2**(n-1))),
        'fine_records_per_parity':2**(n-1),
        'ideal_operations_per_readout':{'zero_preparations':n,'hadamards':1,'edge_cnots':n-1,
          'controlled_local_field_kicks':n,'local_pointer_readouts':n,'parity_decodes':1,'total':4*n+1},
        'readout_count':21,'total_ideal_readout_operations':21*(4*n+1),
        'additional_initial_coherent_preparation_kicks':sum(v!=R() for v in velocity),
        'operation_counts_bound_physical_time':False,
    }
    equal(packet,expected,'regional pointer gadget')


def verify_arithmetic(packet):
    """Exact new certificate checks; public verify additionally replays parents."""
    parents = {}
    for path,h in PINS.items():
        data = (ROOT/path).read_bytes(); need(sha256(data).hexdigest()==h,'immutable parent '+path)
        parents[path] = json.loads(data)
    clock = parents[CLOCK]
    v = current_module('code/source_scalar_execution/verify_source_scalar_execution.py','_instrument_scalar_math')
    R = v.R; mass,action,velocity,g,_ = v.model(ROOT)
    g0 = sum((m*x*x for m,x in zip(mass,g)),R()); g0u = bracket(g0,R)[1]
    equal(packet['detector_mass_norm_squared_Qphi'],g0.encode(),'same detector norm')
    equal(packet['detector_mass_norm_squared_upper'],str(g0u),'detector norm upper')
    equal(packet['energy_injected_per_readout_Qphi'],(g0/8).encode(),'centered kick work')
    equal(packet['total_readout_injected_work_Qphi'],(21*g0/8).encode(),'total injected detector work')
    check_gadget(packet['regional_gadget'],mass,action,velocity,g,R)
    apply = lambda z:[sum((a*z[j] for j,a in row),R()) for row in action]
    position = [R() for _ in range(64)]; speed = g[:]; rows = []
    for separation in range(1,21):
        force = apply(position); half = [p-v.TAU*f/2 for p,f in zip(speed,force)]
        position = [q+v.TAU*p for q,p in zip(position,half)]
        force = apply(position); speed = [p-v.TAU*f/2 for p,f in zip(half,force)]
        c = sum((m*x*y for m,x,y in zip(mass,g,position)),R())
        cl,cu = bracket(c,R); square = bracket(c*c,R)[1]
        need(0<=square<8,'positive cosine domain')
        rows.append({'separation_steps':separation,'commutator_over_i_Qphi':c.encode(),
                     'commutator_interval':[str(cl),str(cu)],'square_upper':str(square)})
    equal(packet['cross_time_brackets'],rows,'full symplectic cross-time commutators')
    expected_rows = []; dmin = F(1)
    for j,old in enumerate(clock['rows'],1):
        if j>1: dmin = down(dmin*(1-F(rows[j-2]['square_upper'])/8))
        a,b = map(F,old['recovered_elapsed_time_interval'])
        need(0<a<b,'positive clock window')
        if j>1: need(F(clock['rows'][j-2]['recovered_elapsed_time_interval'][1])<a,'ordered clock windows')
        closs = up(sum(((b-F(p['recovered_elapsed_time_interval'][0]))**2 for p in clock['rows'][:j-1]),F(0))*g0u**2/8)
        need(0<=closs<1,'continuous attenuation positivity')
        plo,phi = map(F,old['split_probability_interval'])
        amp = max(abs(plo-F(1,2)),abs(phi-F(1,2)))
        gap = max(1-dmin,closs); extra = up(gap*amp)
        error = up(F(old['total_probability_error_upper'])+extra)
        signal = down(dmin*F(old['split_response_abs_lower']))
        # Interval scalar multiplication, implemented by sign cases rather
        # than the producer's four-corner enumeration.
        lo,hi = plo-F(1,2),phi-F(1,2)
        low = lo if lo<=0 else dmin*lo
        high = hi if hi>=0 else dmin*hi
        expected_rows.append({
            'step':j,'recovered_elapsed_time_interval':old['recovered_elapsed_time_interval'],
            'nominal_time_Qphi':old['nominal_time_Qphi'],'signal_sign':old['signal_sign'],
            'discrete_attenuation_interval':[str(dmin),'1'],
            'continuous_attenuation_interval':[str(1-closs),'1'],
            'attenuation_difference_upper':str(gap),
            'unmeasured_split_response_abs_upper':str(amp),
            'unmeasured_clock_comparison_error_upper':old['total_probability_error_upper'],
            'disturbance_from_unmeasured_split_upper':str(up((1-dmin)*amp)),
            'sequential_comparison_extra_error_upper':str(extra),
            'sequential_probability_error_upper':str(error),
            'sequential_split_probability_interval':[str(down(F(1,2)+low)),str(up(F(1,2)+high))],
            'sequential_split_response_abs_lower':str(signal),
            'continuous_sequential_response_abs_lower':str(max(F(0),signal-error)),
            'uniformly_resolved':signal>error,
        })
    equal(packet['rows'],expected_rows,'all sequential clock/probability enclosures')
    expected_instrument = {
        'pointer_state':'|+X>','unitary':'exp(-i Z tensor Phi(g)/2)',
        'outcome0':'+Y','K0':'(exp(-i Phi/2)-i exp(i Phi/2))/2',
        'K1':'(exp(-i Phi/2)+i exp(i Phi/2))/2','effect0':'(I+sin(Phi(g)))/2',
        'nonselective_map':'(W(-g/2) rho W(g/2)+W(g/2) rho W(-g/2))/2',
        'joint_record_state':'sum_h L_h rho L_h* tensor |h><h|; L_h=K_h21 S ... K_h1 S',
        'baseline_sequential_probability':'1/2','all_record_marginals_independent':False,
    }
    equal(packet['instrument'],expected_instrument,'centered instrument convention')
    equal(packet['scope'],scope(),'instrument physical/conditional scope')
    equal(packet['parents'],PINS,'same parent references')
    equal(packet['rounding_scale'],SCALE,'rational precision')
    equal(packet['schema'],'oph.source_scalar.centered_sequential_instrument.v1','schema')
    summary = {'readout_times':21,'prior_pair_brackets':210,'distinct_positive_separations':20,
               'uniformly_resolved_steps':[r['step'] for r in expected_rows if r['uniformly_resolved']]}
    equal(packet['summary'],summary,'complete summary')
    equal(packet['source_pins'],{f:sha256((ROOT/f).read_bytes()).hexdigest() for f in FILES},'current source bytes')
    need(set(packet)=={'schema','scope','parents','rounding_scale','instrument',
        'detector_mass_norm_squared_Qphi','detector_mass_norm_squared_upper','energy_injected_per_readout_Qphi',
        'total_readout_injected_work_Qphi','regional_gadget','cross_time_brackets','rows','summary','source_pins'},'top-level fields')
    return {'verified':True,**summary,'mathematical_replay':False,'parent_events_replayed':None,
            'physical_outcomes':False,'branch_conditioned_clock':False}


def verify(packet):
    result = verify_arithmetic(packet)
    need(sha256((ROOT/CLOCK_VERIFIER).read_bytes()).hexdigest()==CLOCK_VERIFIER_SHA,'immutable clock verifier')
    old = current_module(CLOCK_VERIFIER,'_instrument_clock_quantum_verifier')
    parent = old.verify(old.load(ROOT/CLOCK),root=ROOT)
    need(parent.get('full_clock_replay') is True and parent.get('full_original_quantum_replay') is True
         and type(parent.get('parent_events_replayed')) is int and parent['parent_events_replayed']==5888,'full parent clock and quantum replay')
    # Reject any receipt/source change during the (potentially longer) replay.
    verify_arithmetic(packet)
    return {**result,'mathematical_replay':True,'parent_events_replayed':5888}


if __name__ == '__main__':
    ap=argparse.ArgumentParser();ap.add_argument('path',nargs='?',type=Path,default=OUTPUT)
    args=ap.parse_args();print(json.dumps(verify(load(args.path)),indent=2))

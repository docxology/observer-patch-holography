"""Exact scalar bounds for mathematical KDK trajectories on the golden family."""
from fractions import Fraction as F
from hashlib import sha256
from math import isqrt
from pathlib import Path
import argparse, importlib.util, json, sys

HERE=Path(__file__).resolve().parent
RER=HERE.parents[1]
PARENT='code/source_scalar_packet/source_common_scalar_receipt.json'
PARENT_SHA='4c6e601c6253499429bf2418383701f45ef99da905969f5024b000b2fc915a4c'
VERIFIER='code/source_scalar_packet/verify_source_common_scalar.py'
VERIFIER_SHA='70665fa34c0c03ae713f9201996a6109e31e9770153a82a725300cd0bc73ad74'
INTERVALS='code/source_scalar_packet/source_scalar_intervals.py'
INTERVALS_SHA='ac614f4c8b50bf83da8a7eb9442077c5b981d73dc58ee3cbb1000f8c0f0e2bcf'
COMMIT='f59c99d69d596055fa77eef5fcde4d184f92bb93'
FILES=('code/source_scalar_time_refinement/source_scalar_time_refinement.py',
 'code/source_scalar_time_refinement/verify_source_scalar_time_refinement.py',
 'code/source_scalar_time_refinement/test_source_scalar_time_refinement.py',
 'paper/tex_fragments/SOURCE_SCALAR_TIME_REFINEMENT.tex')
OUTPUT=HERE/'source_scalar_time_refinement_receipt.json'
GRID=10**12

def need(ok,message):
    if not ok:raise ValueError(message)
def raw(x):return (json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)+'\n').encode('ascii')
def context(root=RER):
    for path,digest in ((PARENT,PARENT_SHA),(VERIFIER,VERIFIER_SHA),(INTERVALS,INTERVALS_SHA)):
        need(sha256((root/path).read_bytes()).hexdigest()==digest,'immutable spatial parent: '+path)
    def module(name,path):
        spec=importlib.util.spec_from_file_location(name,root/path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m
        exec(compile((root/path).read_bytes(),str(root/path),'exec'),m.__dict__);return m
    module('source_scalar_intervals',INTERVALS)
    v=module('_time_refinement_spatial_parent',VERIFIER)
    return v,v.load(root/PARENT)
def ceil(q):return -((-q.numerator)//q.denominator)
def up(q):return F(ceil(q*GRID),GRID)
def root_upper(q):
    need(q>=0,'nonnegative square')
    k=isqrt(q.numerator*GRID*GRID//q.denominator)
    return F(k if F(k,GRID)**2==q else k+1,GRID)
def pair_interval(pair):
    scale=10**24;k=isqrt(5*scale*scale);lo,hi=F(scale+k,2*scale),F(scale+k+1,2*scale)
    a,b=pair
    return [a+b*(lo if b>=0 else hi),a+b*(hi if b>=0 else lo)]
def geometry(q):
    need(type(q) is int and 5<=q<=1000,'bounded source census')
    coords=[[-((b+isqrt(5*b*b))//2),b] for b in range(q)]+[[1,0]]
    coords.sort(key=lambda x:pair_interval(x)[0])
    need(coords[0]==[0,0] and coords[-1]==[1,0],'fixed boundaries')
    for x,y in zip(coords,coords[1:]):need(pair_interval(x)[1]<pair_interval(y)[0],'certified coordinate order')
    gaps=[[b[0]-a[0],b[1]-a[1]] for a,b in zip(coords,coords[1:])]
    chosen=min(gaps,key=lambda x:pair_interval(x)[0]);lo,hi=pair_interval(chosen)
    need(0<lo<=hi<F(1,4),'positive minimum gap')
    need(all(g==chosen or hi<pair_interval(g)[0] for g in gaps),'actual minimum gap')
    return chosen,lo,hi
def level(parent):
    q=parent['q'];pair,hlo,hhi=geometry(q);power=0
    while F(1,2**power)>hlo*hlo:power+=1
    tau=F(1,2**power)
    need(2*tau>hhi*hhi,'largest admissible dyadic')
    Lambda=1+12/(hlo*hlo);omega=root_upper(Lambda);r=tau*tau*Lambda
    need(r<1 and tau<F(1,20),'stable step and nonempty window')
    defect=F(parent['gram_row_sum_error_upper'][1]);nu=1+defect
    need(0<=defect<1,'parent Gram norm bound')
    mean=tau*tau*nu*(omega/3+Lambda/9)
    vacuum=tau*tau*nu*omega/24
    temporal=up(mean+vacuum)
    spatial=F(parent['graph_vs_compact_continuum_error_upper'][1])
    signal=F(parent['resolved_graph_signal_lower'])
    combined=min(F(1),spatial+temporal);response=max(F(0),signal-temporal)
    nearby=min(F(1),combined+2*tau)
    first=ceil(F(19,20)/tau);last=int(1/tau)
    need(first*tau>=F(19,20) and last*tau==1 and first<=last,'admissible full closed window grid')
    return {'q':q,'fibonacci_level':parent['fibonacci_level'],'dynamic_oscillators':(q-1)**3,
      'minimum_gap_Qphi':pair,'minimum_gap_interval':list(map(str,(hlo,hhi))),
      'step_exponent':power,'time_step':str(tau),'operator_norm_upper':str(Lambda),
      'sqrt_operator_norm_upper':str(omega),'squared_step_operator_bound':str(r),
      'gram_defect_upper':str(defect),'smearing_norm_squared_upper':str(nu),
      'velocity_norm_squared_upper':str(16*nu),
      'mean_probability_error_upper':str(mean),'vacuum_probability_error_upper':str(vacuum),
      'temporal_probability_error_upper':str(temporal),'spatial_probability_error_upper':str(spatial),
      'same_grid_total_error_upper':str(combined),'split_response_lower':str(response),
      'nearby_continuum_error_upper':str(nearby),
      'comparison_error_smaller_than_response':combined<response,
      'first_window_step':first,'last_window_step':last,'window_grid_points':last-first+1,
      'hypothetical_one_write_per_site_per_step_count':last*(q-1)**3}
def produce(root=RER):
    v,parent=context(root);need(v.verify(parent)['verified'],'full independent spatial replay')
    rows=[level(x) for x in parent['levels']];last=rows[-1]
    need(F(last['temporal_probability_error_upper'])<=F('0.000008071512'),'temporal threshold')
    need(F(last['same_grid_total_error_upper'])<F('0.050063') and F(last['split_response_lower'])>F('0.137746'),'resolved split comparison')
    need(F(last['nearby_continuum_error_upper'])<F('0.050078'),'nearby reference threshold')
    return {'schema':'oph.source-scalar-time-refinement.v1',
      'parent':{'path':PARENT,'sha256':PARENT_SHA,'source_commit':COMMIT},
      'window':['19/20','1'],'units':{'time':'c*t/L','hbar':'1','dimensionless_mass':'1'},
      'preparation':{'same_parent_compact_fc_gc':True,'initial_mean_position':'0',
        'initial_mean_momentum':'4*f_c','initial_state':'original finite-action vacuum with coherent momentum displacement',
        'effect':'(I+sin(Phi(g_c)))/2','baseline_probability':'1/2'},
      'levels':rows,'scope':{'all_finite_spectral_modes_retained':True,
        'mathematical_local_canonical_split_trajectory':True,'observer_event_log_executed':False,
        'same_parent_action_population_and_preparation':True,'time_refinement_supplied':True,
        'source_routing_physical_clock_or_outcomes_selected':False,'q5_clock_error_transferred':False,
        'full_Fock_state_norm_convergence_claimed':False,'velocity_norm_convergence_claimed':False,
        'count_volume_for_substeps_established':False,'nearby_grid_distance_bound':'tau; inside the comparison window',
        'reference_time_readout':'P_split(k*tau), k=min(last,max(first,floor(s/tau+1/2))), s in [19/20,1]',
        'continuum_probability_Lipschitz_upper':'2',
        'interacting_quantum_continuum':False},
      'source_pins':{f:sha256((root/f).read_bytes()).hexdigest() for f in FILES}}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    ap.add_argument('--root',type=Path,default=RER);a=ap.parse_args();packet=produce(a.root);b=raw(packet)
    output=a.root/'code/source_scalar_time_refinement/source_scalar_time_refinement_receipt.json'
    if a.write:output.write_bytes(b)
    if a.check:need(output.read_bytes()==b,'time refinement receipt drift')
    print(json.dumps(packet['levels'][-1],indent=2))

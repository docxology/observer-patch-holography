"""Producer-free exact source-gap and finite/continuum detector-bound replay."""
from fractions import Fraction as F
from hashlib import sha256
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

def need(c,message):
    if not c:raise ValueError(message)
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)
def exact(a,b,message):need(canonical(a)==canonical(b),message)
def unique(xs):
    result={}
    for k,v in xs:need(k not in result,'duplicate JSON key');result[k]=v
    return result
def forbidden(x):raise ValueError('noninteger JSON token')
def load(path=OUTPUT):
    b=Path(path).read_bytes();need(len(b)<200000,'receipt size')
    return json.loads(b,object_pairs_hook=unique,parse_float=forbidden,parse_constant=forbidden)
def context(root=RER):
    for path,pin in ((PARENT,PARENT_SHA),(VERIFIER,VERIFIER_SHA),(INTERVALS,INTERVALS_SHA)):
        need(sha256((root/path).read_bytes()).hexdigest()==pin,'immutable spatial source: '+path)
    def read_module(name,path):
        spec=importlib.util.spec_from_file_location(name,root/path);module=importlib.util.module_from_spec(spec)
        sys.modules[name]=module;exec(compile((root/path).read_bytes(),str(root/path),'exec'),module.__dict__)
        return module
    interval=read_module('source_scalar_intervals',INTERVALS)
    v=read_module('_independent_time_refinement_parent',VERIFIER)
    return v,v.load(root/PARENT),interval
def ceil(q):return -(q.numerator//-q.denominator)
def rounded_up(q):return F(ceil(q*GRID),GRID)
def sqrt_upper(q):
    need(q>=0,'nonnegative square')
    low,high=0,GRID
    while F(high,GRID)**2<q:high*=2
    while high-low>1:
        middle=(low+high)//2
        if F(middle,GRID)**2>=q:high=middle
        else:low=middle
    return F(0) if q==0 else F(high,GRID)
def source_gaps(q):
    need(type(q) is int and 5<=q<=1000,'bounded integer q')
    scale=10**24;left,right=2*scale,3*scale
    while right-left>1:
        middle=(left+right)//2
        if middle*middle<=5*scale*scale:left=middle
        else:right=middle
    phi=(F(scale+left,2*scale),F(scale+right,2*scale))
    def interval(pair):
        a,b=pair;vals=[a+b*x for x in phi];return min(vals),max(vals)
    pairs=[]
    for b in range(q):
        low,high=b*phi[0],b*phi[1];floor=low.numerator//low.denominator
        need(floor<=low and high<floor+1,'unique exact source floor')
        pairs.append((-floor,b))
    pairs.append((1,0));pairs.sort(key=lambda z:interval(z)[0])
    need(pairs[0]==(0,0) and pairs[-1]==(1,0),'source boundaries')
    for a,b in zip(pairs,pairs[1:]):need(interval(a)[1]<interval(b)[0],'strict source order')
    gaps=[(b[0]-a[0],b[1]-a[1]) for a,b in zip(pairs,pairs[1:])]
    pair=min(gaps,key=lambda z:interval(z)[0]);lo,hi=interval(pair)
    need(0<lo<=hi<F(1,4),'minimum positive source spacing')
    for other in set(gaps):
        if other!=pair:need(hi<interval(other)[0],'certified minimum rather than maximum gap')
    return list(pair),lo,hi
def reconstruct_level(parent):
    q=parent['q'];pair,lo,hi=source_gaps(q)
    tau=F(1);power=0
    while tau>lo*lo:tau/=2;power+=1
    need(tau<=lo*lo and 2*tau>hi*hi,'maximal safe dyadic')
    Lambda=(lo*lo+12)/(lo*lo);omega=sqrt_upper(Lambda);r=Lambda*tau*tau
    need(r<1 and tau<=F(1,20),'CFL and window length')
    defect=F(parent['gram_row_sum_error_upper'][1]);need(0<=defect<1,'actual Gram defect')
    nu=1+defect
    # Derived independently from half the displacement error and quarter
    # the vacuum variance error; no compressed-spectrum estimate is used.
    mean=(4*nu)*tau*tau*(omega/12+Lambda/36)
    variance=tau*tau*nu*omega/24
    temporal=rounded_up(mean+variance)
    spatial=F(parent['graph_vs_compact_continuum_error_upper'][1]);signal=F(parent['resolved_graph_signal_lower'])
    total=min(F(1),temporal+spatial);response=max(F(0),signal-temporal)
    n0=ceil(F(19,20)/tau);n1=1//tau
    need(F(n1)*tau==1 and F(n0)*tau>=F(19,20) and n0<=n1,'inside-window grid')
    return {'q':q,'fibonacci_level':parent['fibonacci_level'],'dynamic_oscillators':(q-1)**3,
      'minimum_gap_Qphi':pair,'minimum_gap_interval':[str(lo),str(hi)],'step_exponent':power,
      'time_step':str(tau),'operator_norm_upper':str(Lambda),'sqrt_operator_norm_upper':str(omega),
      'squared_step_operator_bound':str(r),'gram_defect_upper':str(defect),
      'smearing_norm_squared_upper':str(nu),'velocity_norm_squared_upper':str(16*nu),
      'mean_probability_error_upper':str(mean),'vacuum_probability_error_upper':str(variance),
      'temporal_probability_error_upper':str(temporal),'spatial_probability_error_upper':str(spatial),
      'same_grid_total_error_upper':str(total),'split_response_lower':str(response),
      'nearby_continuum_error_upper':str(min(F(1),total+2*tau)),
      'comparison_error_smaller_than_response':total<response,
      'first_window_step':n0,'last_window_step':n1,'window_grid_points':n1-n0+1,
      'hypothetical_one_write_per_site_per_step_count':n1*(q-1)**3}
def verify_arithmetic(packet,parent,root=RER):
    need(type(packet) is dict,'receipt object')
    rows=[reconstruct_level(x) for x in parent['levels']]
    expected={'schema':'oph.source-scalar-time-refinement.v1',
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
    exact(packet,expected,'independent time refinement reconstruction')
    final=rows[-1]
    need(final['q']==233 and F(final['same_grid_total_error_upper'])<F('0.050063')
         and F(final['split_response_lower'])>F('0.137746')
         and F(final['nearby_continuum_error_upper'])<F('0.050078'),'resolved theorem thresholds')
    return {'verdict':'PASS','full_spatial_parent_replayed':False,'levels':len(rows),
      'q':233,'time_step':final['time_step'],'temporal_probability_error_upper':final['temporal_probability_error_upper'],
      'same_grid_total_error_upper':final['same_grid_total_error_upper'],'split_response_lower':final['split_response_lower'],
      'nearby_continuum_error_upper':final['nearby_continuum_error_upper'],'observer_event_log_executed':False}
def verify(packet,root=RER):
    v,parent,_=context(root);need(v.verify(parent)['verified'],'fresh independent spatial proof')
    report=verify_arithmetic(packet,parent,root)
    need(sha256((root/PARENT).read_bytes()).hexdigest()==PARENT_SHA,'final parent identity')
    report['full_spatial_parent_replayed']=True;return report

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('path',nargs='?',type=Path,default=OUTPUT)
    ap.add_argument('--root',type=Path,default=RER);a=ap.parse_args()
    print(json.dumps(verify(load(a.path),root=a.root),indent=2,sort_keys=True))

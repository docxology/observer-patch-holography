"""Producer-free exact probability replay, with a fresh pinned parent proof."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import importlib.util
import json
import sys
import argparse

HERE=Path(__file__).resolve().parent
RER=HERE.parents[1]
PARENT_PATH='code/source_scalar_execution/source_scalar_execution_receipt.json'
PARENT_SHA='cf246c2caa072334e0d4796c1c6c49d2a231a263ff34281843a1c35c7cdbb69a'
VERIFIER_PATH='code/source_scalar_execution/verify_source_scalar_execution.py'
VERIFIER_SHA='c03892572732bbf7d019e721d19b6a249b445e2dc30f54d3c237be938cf88d42'
FILES=('paper/tex_fragments/SOURCE_SCALAR_QUANTUM.tex',
 'code/source_scalar_quantum/quantum_probability.py',
 'code/source_scalar_quantum/verify_quantum_probability.py',
 'code/source_scalar_quantum/test_scalar_quantum_probability.py')
OUTPUT=HERE/'quantum_probability_receipt.json'
SCALE=10**12

def need(c,m):
    if not c:raise ValueError(m)
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)
def equal(a,b,m):need(canonical(a)==canonical(b),m)
def pairs(seq):
    d={}
    for k,v in seq:
        need(k not in d,'duplicate JSON key');d[k]=v
    return d

def forbidden(x):raise ValueError('float/nonfinite JSON forbidden')
def load(path=OUTPUT):
    raw=Path(path).read_bytes();need(len(raw)<200_000,'quantum receipt size')
    return json.loads(raw.decode('ascii'),object_pairs_hook=pairs,parse_float=forbidden,parse_constant=forbidden)

def parent_context(rer=RER):
    raw=(rer/PARENT_PATH).read_bytes();need(sha256(raw).hexdigest()==PARENT_SHA,'immutable parent receipt identity')
    code=(rer/VERIFIER_PATH).read_bytes();need(sha256(code).hexdigest()==VERIFIER_SHA,'immutable parent verifier identity')
    name='_oph_scalar_quantum_parent_independent'
    spec=importlib.util.spec_from_file_location(name,rer/VERIFIER_PATH)
    module=importlib.util.module_from_spec(spec);sys.modules[name]=module
    exec(compile(code,str(rer/VERIFIER_PATH),'exec'),module.__dict__)
    data=module.load(rer/PARENT_PATH)
    return module,data

def bracket(x,R,square=False):
    # Independent exact monotone bisection, with no floating approximation.
    if square:need(x.sign()>=0,'square nonnegative');lo=0
    else:lo=-SCALE
    hi=SCALE
    def difference(n):return (R(F(n,SCALE)**2 if square else F(n,SCALE))-x).sign()
    while difference(lo)>0:lo*=2
    while difference(hi)<0:hi*=2
    while hi-lo>1:
        mid=(hi+lo)//2
        if difference(mid)<=0:lo=mid
        else:hi=mid
    return F(lo,SCALE),F(hi,SCALE)

def down(q):return F((q*SCALE).numerator//(q*SCALE).denominator,SCALE)
def up(q):return -down(-q)

def expected_scope():return {'all_finite_modes':True,'hbar':'1','initial_state':'original finite-action vacuum with coherent momentum displacement v',
 'baseline':'original vacuum; split baseline covariance evolves but sine effect remains 1/2',
 'effect':'(I+sin(Phi(g)))/2','clock':'supplied model t_j=j*sqrt(5)/35; j=1,...,21',
 'changed_vacuum':False,'spatial_continuum_error_transfer':False,'native_clock':False,
 'observed_quantum_outcomes':False,'intermediate_time_error_enclosure':False}

def verify_arithmetic(packet,parent,module,rer=RER):
    """Pure arithmetic consumer; caller must separately authenticate/replay parent.

    Default verify() always does so. Tests use immutable original parent bytes
    to isolate adversarial probability errors without repeating that full proof.
    """
    need(type(packet) is dict,'quantum object')
    R=module.R
    mass,rows,velocity,g,addresses=module.model(rer)
    g0=sum((m*x*x for m,x in zip(mass,g)),R())
    # Reconstruct the quadratic form by diagonal plus each unordered pair once.
    matrix=[dict(row) for row in rows]
    g1=sum((mass[i]*matrix[i][i]*g[i]*g[i] for i in range(64)),R())
    for i in range(64):
        for j,a in matrix[i].items():
            if j<=i:continue
            need(mass[i]*a==mass[j]*matrix[j][i],'weighted operator symmetry')
            g1+=2*mass[i]*a*g[i]*g[j]
    need(g0.sign()>0 and (g1-g0).sign()>=0,'positive smearing/action')
    g0up=bracket(g0,R)[1];gnup=bracket(g0,R,True)[1];sqrtup=bracket(g0*g1,R,True)[1]
    r=F(30049,12005);delta=up(F(1,245)*sqrtup/(8-2*r));vmax=g0up/2+delta
    need(0<r<3 and 0<vmax<2,'covariance denominator and damping budget')
    rows_expected=[]
    need(len(parent['diagnostics']['comparisons'])==21,'parent time census')
    for j,row in enumerate(parent['diagnostics']['comparisons'],1):
        need(row['step']==j,'parent ordered time census')
        mean=module.parse(row['executed_detector_Qphi']);lo,hi=bracket(mean,R)
        sign=mean.sign()
        if not sign:lo=hi=F(0)
        a,b=(lo,hi) if sign>=0 else (-hi,-lo)
        need(0<=a<=b<=1,'small signed mean')
        signal=down((1-vmax/2)*max(F(0),a-b**3/6)/2)
        e=module.rational(row['full_mass_norm_discretization_error'][1]);need(e>=0,'parent norm error nonnegative')
        error=up(gnup*e/2+delta/4)
        interval=[F(1,2)+signal,F(1,2)+b/2] if sign>=0 else [F(1,2)-b/2,F(1,2)-signal]
        need(0<=interval[0]<=interval[1]<=1,'effect probability enclosure')
        rows_expected.append({'step':j,'time_Qphi':row['model_time_Qphi'],'mean_Qphi':row['executed_detector_Qphi'],
          'mean_bracket':[str(lo),str(hi)],'parent_state_error_upper':str(e),'mean_error_upper':str(up(gnup*e)),
          'signal_sign':sign,'split_probability_interval':list(map(str,interval)),
          'split_response_abs_lower':str(signal),'probability_error_upper':str(error),
          'reference_response_abs_lower':str(max(F(0),signal-error)),'resolved_above_total_bound':signal>error})
    expected={'schema':'oph.finite-scalar-original-vacuum-probability.v1',
      'parent':{'path':PARENT_PATH,'sha256':PARENT_SHA,'candidate_source_commit':'f59c99d69d596055fa77eef5fcde4d184f92bb93'},
      'scope':expected_scope(),'constants':{'tau_squared':'1/245','cfl_upper':str(r),'operator_lower':'1','rounding_scale':SCALE},
      'moments':{'g_mass_squared_Qphi':g0.encode(),'g_energy_Qphi':g1.encode(),'g_mass_squared_upper':str(g0up),
        'g_norm_upper':str(gnup),'sqrt_mass_energy_upper':str(sqrtup)},
      'covariance':{'increase_nonnegative':True,'increase_upper':str(delta),'original_variance_upper':str(g0up/2),'split_variance_upper':str(vmax)},
      'rows':rows_expected,'summary':{'times':21,'resolved_steps':[r['step'] for r in rows_expected if r['resolved_above_total_bound']]},
      'source_pins':{f:sha256((rer/f).read_bytes()).hexdigest() for f in FILES}}
    equal(packet,expected,'exact original-vacuum probability certificate')
    return {'verdict':'PASS','times':21,'resolved_steps':expected['summary']['resolved_steps'],
            'uniform_added_variance_upper':str(delta),'step16':rows_expected[15],
            'quantum_probability_scope':'original finite-action vacuum and coherent momentum preparation; bounded sine effect',
            'spatial_continuum_error_transfer':False,'observed_outcomes':False}

def verify(packet,rer=RER):
    module,parent=parent_context(rer)
    # Full upstream proof is mandatory; no cached success or producer dispatch.
    report=module.verify(parent,root=rer)
    need(report['verdict']=='PASS' and report['events_replayed']==5888,'fresh parent replay result')
    result=verify_arithmetic(packet,parent,module,rer)
    # Detect parent/verifier/source changes during a replay as well.
    parent_context(rer)
    equal(packet['source_pins'],{f:sha256((rer/f).read_bytes()).hexdigest() for f in FILES},'unchanged own sources')
    result['parent_full_mathematical_replay']=True
    result['parent_events_replayed']=5888
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('path',nargs='?',type=Path,default=OUTPUT);a=ap.parse_args()
    print(json.dumps(verify(load(a.path)),sort_keys=True,indent=2))

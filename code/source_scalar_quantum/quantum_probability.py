"""Exact producer for original-vacuum finite scalar probability bounds."""
from fractions import Fraction as F
from decimal import Decimal, localcontext, ROUND_FLOOR
from pathlib import Path
from hashlib import sha256
import argparse
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT='code/source_scalar_execution/source_scalar_execution_receipt.json'
PARENT_HASH='cf246c2caa072334e0d4796c1c6c49d2a231a263ff34281843a1c35c7cdbb69a'
OUTPUT=HERE/'quantum_probability_receipt.json'
FILES=('paper/tex_fragments/SOURCE_SCALAR_QUANTUM.tex',
 'code/source_scalar_quantum/quantum_probability.py',
 'code/source_scalar_quantum/verify_quantum_probability.py',
 'code/source_scalar_quantum/test_scalar_quantum_probability.py')
SCALE=10**12

class Phi:
    def __init__(self,a=0,b=0): self.a,self.b=F(a),F(b)
    @staticmethod
    def of(x): return x if isinstance(x,Phi) else Phi(x)
    def __add__(self,y): y=self.of(y);return Phi(self.a+y.a,self.b+y.b)
    __radd__=__add__
    def __neg__(self): return Phi(-self.a,-self.b)
    def __sub__(self,y): return self+-self.of(y)
    def __mul__(self,y):
        y=self.of(y);return Phi(self.a*y.a+self.b*y.b,self.a*y.b+self.b*y.a+self.b*y.b)
    __rmul__=__mul__
    def sign(self):
        a,b=self.a+self.b/2,self.b/2
        if not b:return (a>0)-(a<0)
        if not a:return (b>0)-(b<0)
        if a*b>0:return 1 if a>0 else -1
        delta=a*a-5*b*b;return ((delta>0)-(delta<0))*(1 if a>0 else -1)
    def encode(self):return [str(self.a),str(self.b)]
    def decimal(self):
        d=lambda f:Decimal(f.numerator)/Decimal(f.denominator)
        return d(self.a)+d(self.b)*(1+Decimal(5).sqrt())/2

def bracket(x,square=False):
    with localcontext() as c:
        c.prec=220
        d=x.decimal();n=int(((d.sqrt() if square else d)*SCALE).to_integral_value(rounding=ROUND_FLOOR))
    def test(k):return (Phi(F(k,SCALE)**2 if square else F(k,SCALE))-x).sign()
    while test(n)>0:n-=1
    while test(n+1)<0:n+=1
    return F(n,SCALE),F(n+1,SCALE)

def floor_q(x):return F(x*SCALE//1,SCALE)
def ceil_q(x):return -floor_q(-x)
def scope():return {'all_finite_modes':True,'hbar':'1','initial_state':'original finite-action vacuum with coherent momentum displacement v',
 'baseline':'original vacuum; split baseline covariance evolves but sine effect remains 1/2',
 'effect':'(I+sin(Phi(g)))/2','clock':'supplied model t_j=j*sqrt(5)/35; j=1,...,21',
 'changed_vacuum':False,'spatial_continuum_error_transfer':False,'native_clock':False,
 'observed_quantum_outcomes':False,'intermediate_time_error_enclosure':False}

def produce():
    raw=(ROOT/PARENT).read_bytes();assert sha256(raw).hexdigest()==PARENT_HASH
    p=json.loads(raw);parse=lambda a:Phi(*a)
    m=list(map(parse,p['mass_Qphi']));g=list(map(parse,p['detector_Qphi']))
    rows=[[(j,parse(a)) for j,a in row] for row in p['action_rows_Qphi']]
    ag=[sum((a*g[j] for j,a in row),Phi()) for row in rows]
    g0=sum((w*x*x for w,x in zip(m,g)),Phi());g1=sum((w*x*y for w,x,y in zip(m,g,ag)),Phi())
    g0u=bracket(g0)[1];gnu=bracket(g0,True)[1];sqrtu=bracket(g0*g1,True)[1]
    r=F(30049,12005);d=ceil_q(F(1,245)*sqrtu/(8*(1-r/4)));vmax=g0u/2+d
    outrows=[]
    for row in p['diagnostics']['comparisons']:
        mean=parse(row['executed_detector_Qphi']);lo,hi=bracket(mean)
        if mean.sign()==0:lo=hi=F(0)
        sign=mean.sign();low,up=(lo,hi) if sign>=0 else (-hi,-lo)
        signal=floor_q((1-vmax/2)*max(F(0),low-up**3/6)/2)
        e=F(row['full_mass_norm_discretization_error'][1]);err=ceil_q(gnu*e/2+d/4)
        probs=[F(1,2)+signal,F(1,2)+up/2] if sign>=0 else [F(1,2)-up/2,F(1,2)-signal]
        outrows.append({'step':row['step'],'time_Qphi':row['model_time_Qphi'],
          'mean_Qphi':row['executed_detector_Qphi'],'mean_bracket':list(map(str,[lo,hi])),
          'parent_state_error_upper':str(e),'mean_error_upper':str(ceil_q(gnu*e)),
          'signal_sign':sign,'split_probability_interval':list(map(str,probs)),
          'split_response_abs_lower':str(signal),'probability_error_upper':str(err),
          'reference_response_abs_lower':str(max(F(0),signal-err)),
          'resolved_above_total_bound':signal>err})
    return {'schema':'oph.finite-scalar-original-vacuum-probability.v1',
      'parent':{'path':PARENT,'sha256':PARENT_HASH,'candidate_source_commit':'f59c99d69d596055fa77eef5fcde4d184f92bb93'},
      'scope':scope(),'constants':{'tau_squared':'1/245','cfl_upper':str(r),'operator_lower':'1','rounding_scale':SCALE},
      'moments':{'g_mass_squared_Qphi':g0.encode(),'g_energy_Qphi':g1.encode(),
        'g_mass_squared_upper':str(g0u),'g_norm_upper':str(gnu),'sqrt_mass_energy_upper':str(sqrtu)},
      'covariance':{'increase_nonnegative':True,'increase_upper':str(d),'original_variance_upper':str(g0u/2),'split_variance_upper':str(vmax)},
      'rows':outrows,'summary':{'times':21,'resolved_steps':[r['step'] for r in outrows if r['resolved_above_total_bound']]},
      'source_pins':{f:sha256((ROOT/f).read_bytes()).hexdigest() for f in FILES}}

def raw(x):return (json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)+'\n').encode('ascii')
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true');a=ap.parse_args();p=produce();data=raw(p)
    if a.write:OUTPUT.write_bytes(data)
    if a.check and OUTPUT.read_bytes()!=data:raise SystemExit('producer parity failure')
    print(json.dumps(p['summary'],indent=2))

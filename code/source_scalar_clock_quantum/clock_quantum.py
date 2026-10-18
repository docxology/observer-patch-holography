"""Exact same-state scalar probability bounds with recovered action-time intervals."""
from decimal import Decimal, ROUND_FLOOR, localcontext
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse, json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SCALE=10**12
SCALAR='code/source_scalar_execution/source_scalar_execution_receipt.json'
SCALAR_SHA='cf246c2caa072334e0d4796c1c6c49d2a231a263ff34281843a1c35c7cdbb69a'
QUANTUM='code/source_scalar_quantum/quantum_probability_receipt.json'
QUANTUM_SHA='1545e272e2ed6983f1d8643ce60212e8109437066ab0e162770ee7422f9e86dc'
CLOCK='code/source_scalar_clock/source_scalar_clock_receipt.json'
CLOCK_SHA='8908cfe94361cad34c172bb15f9be20ddd0dbc08006759c7a09eb2e3ab6c6748'
QVERIFY='code/source_scalar_quantum/verify_quantum_probability.py'
QVERIFY_SHA='1ab26644da41ee7977074b1a741aa3fa0a2df3fcbef40a4bc595758c2eb5203d'
CVERIFY='code/source_scalar_clock/verify_source_scalar_clock.py'
CVERIFY_SHA='51520ad5d26bc4b574b1c8db1ed77108014b2e3e172a0d760e81c195904ed66d'
FILES=('code/source_scalar_clock_quantum/clock_quantum.py',
       'code/source_scalar_clock_quantum/verify_clock_quantum.py',
       'code/source_scalar_clock_quantum/test_clock_quantum.py',
       'paper/tex_fragments/SOURCE_SCALAR_CLOCK_QUANTUM.tex')
OUTPUT=HERE/'clock_quantum_receipt.json'
SCHEDULES=('ascending_intervention','descending_intervention')

def need(ok,reason):
    if not ok:raise ValueError(reason)
def raw(x):return (json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False,ensure_ascii=True)+'\n').encode('ascii')
def digest(x):return sha256(raw(x)).hexdigest()
def down(x):return F((x*SCALE).numerator//(x*SCALE).denominator,SCALE)
def up(x):return -down(-x)
class Phi:
    def __init__(self,a=0,b=0):self.a,self.b=F(a),F(b)
    @staticmethod
    def of(x):return x if isinstance(x,Phi) else Phi(x)
    def __add__(self,y):y=self.of(y);return Phi(self.a+y.a,self.b+y.b)
    __radd__=__add__
    def __neg__(self):return Phi(-self.a,-self.b)
    def __sub__(self,y):return self+-self.of(y)
    def __mul__(self,y):
        y=self.of(y);return Phi(self.a*y.a+self.b*y.b,self.a*y.b+self.b*y.a+self.b*y.b)
    __rmul__=__mul__
    def sign(self):
        a,b=self.a+self.b/2,self.b/2
        if not b:return (a>0)-(a<0)
        if not a:return (b>0)-(b<0)
        if a*b>0:return 1 if a>0 else -1
        delta=a*a-5*b*b;return ((delta>0)-(delta<0))*(1 if a>0 else -1)
    def absolute(self):return -self if self.sign()<0 else self
    def encode(self):return [str(self.a),str(self.b)]
    def decimal(self):
        d=lambda f:Decimal(f.numerator)/Decimal(f.denominator)
        return d(self.a)+d(self.b)*(1+Decimal(5).sqrt())/2
def upper(x,square=False):
    need(x.sign()>=0,'nonnegative bound input')
    with localcontext() as ctx:
        ctx.prec=220;approx=x.decimal();q=approx.sqrt() if square else approx
        n=int((q*SCALE).to_integral_value(rounding=ROUND_FLOOR))
    def cmp(k):return (Phi(F(k,SCALE)**2 if square else F(k,SCALE))-x).sign()
    while cmp(n)>0:n-=1
    while cmp(n+1)<0:n+=1
    # The exact sign tests, not the decimal approximation, certify this endpoint.
    return F(n+1,SCALE)
def pinned_json(root,path,pin):
    b=(root/path).read_bytes();need(sha256(b).hexdigest()==pin,'immutable '+path)
    return json.loads(b)
def scope():return {
    'reference':'same continuous finite64-mode Hamiltonian, original vacuum and coherent momentum displacement v',
    'effect':'(I+sin(Phi(g)))/2','hbar':'1','baseline_probability':'1/2',
    'comparison_quantifier':'for every real time in each recovered elapsed-time interval',
    'discrete_probability_exists_only_at_executed_layers':True,
    'clock_only_uncertainty':True,'same_action_state_preparation_and_detector_required':True,
    'hidden_common_configuration_stationarity_is_hypothesis':True,
    'one_positive_duration_per_complete_configuration_interval':True,
    'record_noise_certifies_quantum_state_or_field_error':False,
    'interval_overlap_proves_hidden_history_exists':False,
    'changed_vacuum':False,'observed_quantum_outcomes':False,
    'physical_clock_or_count_volume_identified':False,'regional_quantum_time_slice_proved':False,
    'spatial_continuum_error_transferred':False}
def dependencies():return {k:{'path':p,'sha256':h} for k,p,h in
    [('scalar',SCALAR,SCALAR_SHA),('original_vacuum_quantum',QUANTUM,QUANTUM_SHA),('reconstructed_clock',CLOCK,CLOCK_SHA)]}
def produce(root=ROOT):
    scalar=pinned_json(root,SCALAR,SCALAR_SHA);quantum=pinned_json(root,QUANTUM,QUANTUM_SHA);clock=pinned_json(root,CLOCK,CLOCK_SHA)
    for p,h in ((QVERIFY,QVERIFY_SHA),(CVERIFY,CVERIFY_SHA)):need(sha256((root/p).read_bytes()).hexdigest()==h,'verifier pin')
    mass=[Phi(*x) for x in scalar['mass_Qphi']];g=[Phi(*x) for x in scalar['detector_Qphi']];v=[Phi(*x) for x in scalar['initial_velocity_Qphi']]
    g2=sum((m*x*x for m,x in zip(mass,g)),Phi());v2=sum((m*x*x for m,x in zip(mass,v)),Phi());L=up(upper(g2*v2,True)/2)
    need(quantum['parent']['sha256']==clock['parent']['sha256']==SCALAR_SHA,'common scalar parent')
    layer_hashes={name:[digest(row) for row in scalar['traces'][name]['layers']] for name in SCHEDULES}
    for name in SCHEDULES:need(layer_hashes[name]==clock['traces'][name]['layer_value_sha256'],'same clock fields')
    need(layer_hashes[SCHEDULES[0]]==layer_hashes[SCHEDULES[1]],'same completed fields across schedules')
    intervals=clock['stability']['schedules'][SCHEDULES[0]]['elapsed_time_intervals']
    need(intervals==clock['stability']['schedules'][SCHEDULES[1]]['elapsed_time_intervals'],'same elapsed bounds')
    out=[]
    for j,row in enumerate(quantum['rows'],1):
        need(row['step']==j,'all ordered quantum rows');a,b=map(F,intervals[j]);t=Phi(*row['time_Qphi'])
        offsets=[(t-Phi(a)).absolute(),(t-Phi(b)).absolute()];delta=upper(offsets[0] if (offsets[0]-offsets[1]).sign()>=0 else offsets[1])
        timing=up(L*delta);error=up(F(row['probability_error_upper'])+timing)
        lo,hi=map(F,row['split_probability_interval']);ref=[max(F(0),lo-error),min(F(1),hi+error)];signal=F(row['split_response_abs_lower'])
        out.append({'step':j,'reconstructed_layer_index':j+1,'layer_value_sha256':layer_hashes[SCHEDULES[0]][j+1],
          'nominal_time_Qphi':row['time_Qphi'],'recovered_elapsed_time_interval':list(map(str,[a,b])),
          'time_offset_upper':str(delta),'timing_probability_error_upper':str(timing),
          'original_probability_error_upper':row['probability_error_upper'],'total_probability_error_upper':str(error),
          'split_probability_interval':row['split_probability_interval'],'split_response_abs_lower':str(signal),'signal_sign':row['signal_sign'],
          'continuous_probability_interval_for_every_time':list(map(str,ref)),
          'continuous_response_interval_for_every_time':[str(x-F(1,2)) for x in ref],
          'continuous_response_abs_lower':str(max(F(0),signal-error)),
          'uniformly_resolved':signal>error})
    return {'schema':'oph.scalar-clock-original-vacuum-detector.v1','dependencies':dependencies(),
      'dependency_verifier_pins':{QVERIFY:QVERIFY_SHA,CVERIFY:CVERIFY_SHA},'scope':scope(),
      'clock_budget':clock['stability']['budget'],
      'configuration_join':{'site_count':64,'completed_layer_count':23,'parent_events':5888,
        'mass_sha256':digest(scalar['mass_Qphi']),'action_sha256':digest(scalar['action_rows_Qphi']),
        'preparation_velocity_sha256':digest(scalar['initial_velocity_Qphi']),'detector_sha256':digest(scalar['detector_Qphi']),
        'schedule_layer_value_sha256':layer_hashes},
      'moments':{'g_mass_squared_Qphi':g2.encode(),'v_mass_squared_Qphi':v2.encode(),
        'norm_product_squared_Qphi':(g2*v2).encode(),'continuous_probability_lipschitz_upper':str(L)},
      'rows':out,'summary':{'times':len(out),'original_resolved_steps':quantum['summary']['resolved_steps'],
        'resolved_steps':[r['step'] for r in out if r['uniformly_resolved']],
        'unresolved_steps':[r['step'] for r in out if not r['uniformly_resolved']],
        'maximum_timing_probability_error_upper':str(max(F(r['timing_probability_error_upper']) for r in out))},
      'source_pins':{f:sha256((root/f).read_bytes()).hexdigest() for f in FILES}}
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true');a=ap.parse_args();p=produce();b=raw(p)
    if a.write:OUTPUT.write_bytes(b)
    if a.check:need(OUTPUT.read_bytes()==b,'producer byte parity')
    print(json.dumps(p['summary'],indent=2,sort_keys=True))

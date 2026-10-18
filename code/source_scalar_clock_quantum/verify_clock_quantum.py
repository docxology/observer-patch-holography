"""Independent clock/quantum parent replay and exact all-row time comparison."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse, importlib.util, json, sys

HERE=Path(__file__).resolve().parent
RER=HERE.parents[1]
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

def need(ok,message):
    if not ok:raise ValueError(message)
def raw(x):return (json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False,ensure_ascii=True)+'\n').encode('ascii')
def equal(a,b,message):need(raw(a)==raw(b),message)
def digest(x):return sha256(raw(x)).hexdigest()
def pairs(seq):
    result={}
    for k,v in seq:need(k not in result,'duplicate JSON key');result[k]=v
    return result
def no_float(x):raise ValueError('float/nonfinite JSON token')
def load(path=OUTPUT):
    data=Path(path).read_bytes();need(len(data)<200000,'clock-quantum receipt size')
    return json.loads(data.decode('ascii'),object_pairs_hook=pairs,parse_float=no_float,parse_constant=no_float)
def rational(x):
    need(type(x) is str,'rational string');value=F(x);need(str(value)==x,'canonical rational');return value
def down(q):return F((q*SCALE).numerator//(q*SCALE).denominator,SCALE)
def up(q):return -down(-q)
def upper(x,R,square=False):
    """Pure exact bisection, independent of the producer's decimal seed."""
    need(x.sign()>=0,'nonnegative outward bound');lo=0;hi=SCALE
    def compare(n):return (R(F(n,SCALE)**2 if square else F(n,SCALE))-x).sign()
    while compare(hi)<=0:hi*=2
    while hi-lo>1:
        middle=(hi+lo)//2
        if compare(middle)<=0:lo=middle
        else:hi=middle
    return F(hi,SCALE)
def load_code(root,path,pin,kind):
    code=(root/path).read_bytes();need(sha256(code).hexdigest()==pin,'pinned '+kind+' verifier')
    name='_clock_quantum_'+kind+'_'+pin[:16]
    spec=importlib.util.spec_from_file_location(name,root/path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m
    exec(compile(code,str(root/path),'exec'),m.__dict__);return m
def dependency_context(root=RER):
    for path,pin in ((SCALAR,SCALAR_SHA),(QUANTUM,QUANTUM_SHA),(CLOCK,CLOCK_SHA)):
        need(sha256((root/path).read_bytes()).hexdigest()==pin,'immutable dependency '+path)
    q=load_code(root,QVERIFY,QVERIFY_SHA,'original_quantum');c=load_code(root,CVERIFY,CVERIFY_SHA,'clock')
    qp=q.load(root/QUANTUM);cp=c.load(root/CLOCK);v,sp=q.parent_context(root)
    return q,c,v,sp,qp,cp
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
def row_bounds(original,j,interval,L,v,layer_hash):
    need(type(j) is int and 1<=j<=21,'exact completed index')
    equal(original['step'],j,'quantum completed index');a,b=map(rational,interval);need(0<=a<b,'positive-width time interval')
    t=v.parse(original['time_Qphi']);need(t==j*v.TAU,'nominal action-time identity')
    need((v.R(a)-t).sign()<=0 and (v.R(b)-t).sign()>=0,'nominal time enclosed')
    left=t-v.R(a);right=v.R(b)-t;distance=left if (left-right).sign()>=0 else right
    delta=upper(distance,v.R);timing=up(L*delta);old_error=rational(original['probability_error_upper'])
    need(old_error>=0 and L>=0,'nonnegative probability error');error=old_error+timing
    pl,pu=map(rational,original['split_probability_interval']);need(0<=pl<=pu<=1,'split effect interval')
    reference=[max(F(0),pl-error),min(F(1),pu+error)]
    signal=rational(original['split_response_abs_lower']);sign=original['signal_sign']
    need(type(sign) is int and sign in (-1,0,1) and signal>=0,'signed split response')
    if signal>0:
        need((sign==1 and pl-F(1,2)>=signal) or (sign==-1 and F(1,2)-pu>=signal),'response interval consistency')
    return {'step':j,'reconstructed_layer_index':j+1,'layer_value_sha256':layer_hash,
      'nominal_time_Qphi':original['time_Qphi'],'recovered_elapsed_time_interval':[str(a),str(b)],
      'time_offset_upper':str(delta),'timing_probability_error_upper':str(timing),
      'original_probability_error_upper':str(old_error),'total_probability_error_upper':str(error),
      'split_probability_interval':original['split_probability_interval'],'split_response_abs_lower':str(signal),'signal_sign':sign,
      'continuous_probability_interval_for_every_time':list(map(str,reference)),
      'continuous_response_interval_for_every_time':[str(x-F(1,2)) for x in reference],
      'continuous_response_abs_lower':str(max(F(0),signal-error)),'uniformly_resolved':signal>error}
def verify_arithmetic(packet,scalar,quantum,clock,v,root=RER):
    """Internal arithmetic only; verify() additionally requires both full parent proofs."""
    need(type(packet) is dict,'clock-quantum object')
    # This internal entry point also forbids coherently replaced upstream data.
    for p,pin in ((scalar,SCALAR_SHA),(quantum,QUANTUM_SHA),(clock,CLOCK_SHA)):
        need(digest(p)==pin,'immutable parent object')
    equal(quantum['parent']['sha256'],SCALAR_SHA,'quantum scalar parent')
    equal(clock['parent']['sha256'],SCALAR_SHA,'clock scalar parent')
    mass,A,velocity,g,_=v.model(root);R=v.R
    g2=sum((mass[i]*g[i]*g[i] for i in range(64)),R())
    v2=sum((mass[i]*velocity[i]*velocity[i] for i in range(64)),R())
    need(g2.sign()>0 and v2.sign()>0,'nonzero fixed detector/preparation');L=up(upper(g2*v2,R,True)/2)
    equal(g2.encode(),quantum['moments']['g_mass_squared_Qphi'],'quantum detector normalization')
    hashes={}
    for name in SCHEDULES:
        vectors=scalar['traces'][name]['layers'];need(len(vectors)==23,'complete scalar vector census')
        hashes[name]=[digest(row) for row in vectors]
        equal(hashes[name],clock['traces'][name]['layer_value_sha256'],'actual reconstructed clock values')
    equal(hashes[SCHEDULES[0]],hashes[SCHEDULES[1]],'same schedule preparations/fields')
    equal(clock['exact_duration']['positive_tick_Qphi'],v.TAU.encode(),'same nominal clock normalization')
    expected_budget={'configuration_M_norm':'1/100000000','operator_norm_upper':'614','increment_residual_norm':'0'}
    equal(clock['stability']['budget'],expected_budget,'clock-only budget')
    schedules=clock['stability']['schedules'];elapsed={}
    for name in SCHEDULES:
        edges=schedules[name]['edge_duration_intervals'];need(len(edges)==21,'all edge intervals')
        total=[F(0),F(0)];sums=[['0','0']]
        for pair in edges:
            a,b=map(rational,pair);need(0<a<=b,'positive duration enclosure')
            total=[total[0]+a,total[1]+b];sums.append(list(map(str,total)))
        equal(sums,schedules[name]['elapsed_time_intervals'],'full cumulative interval sum')
        elapsed[name]=sums
    equal(elapsed[SCHEDULES[0]],elapsed[SCHEDULES[1]],'same time reconstruction across schedules')
    need(len(quantum['rows'])==len(scalar['diagnostics']['comparisons'])==21,'all comparison rows')
    out=[]
    for j,row in enumerate(quantum['rows'],1):
        # Bind the previously verified quantum mean and its norm error to this
        # same original scalar action, then add timing without replacing either.
        source=scalar['diagnostics']['comparisons'][j-1]
        equal(row['mean_Qphi'],source['executed_detector_Qphi'],'same quantum field mean')
        equal(row['parent_state_error_upper'],source['full_mass_norm_discretization_error'][1],'same all-mode error')
        out.append(row_bounds(row,j,elapsed[SCHEDULES[0]][j],L,v,hashes[SCHEDULES[0]][j+1]))
    expected={'schema':'oph.scalar-clock-original-vacuum-detector.v1',
      'dependencies':{k:{'path':p,'sha256':h} for k,p,h in
        [('scalar',SCALAR,SCALAR_SHA),('original_vacuum_quantum',QUANTUM,QUANTUM_SHA),('reconstructed_clock',CLOCK,CLOCK_SHA)]},
      'dependency_verifier_pins':{QVERIFY:QVERIFY_SHA,CVERIFY:CVERIFY_SHA},'scope':scope(),'clock_budget':expected_budget,
      'configuration_join':{'site_count':64,'completed_layer_count':23,'parent_events':5888,
        'mass_sha256':digest(scalar['mass_Qphi']),'action_sha256':digest(scalar['action_rows_Qphi']),
        'preparation_velocity_sha256':digest(scalar['initial_velocity_Qphi']),'detector_sha256':digest(scalar['detector_Qphi']),
        'schedule_layer_value_sha256':hashes},
      'moments':{'g_mass_squared_Qphi':g2.encode(),'v_mass_squared_Qphi':v2.encode(),
        'norm_product_squared_Qphi':(g2*v2).encode(),'continuous_probability_lipschitz_upper':str(L)},
      'rows':out,'summary':{'times':21,'original_resolved_steps':quantum['summary']['resolved_steps'],
        'resolved_steps':[r['step'] for r in out if r['uniformly_resolved']],
        'unresolved_steps':[r['step'] for r in out if not r['uniformly_resolved']],
        'maximum_timing_probability_error_upper':str(max(F(r['timing_probability_error_upper']) for r in out))},
      'source_pins':{f:sha256((root/f).read_bytes()).hexdigest() for f in FILES}}
    equal(packet,expected,'independent all-time-interval quantum comparison')
    return {'verdict':'PASS',**expected['summary'],'step16':out[15],
      'clock_only_uncertainty':True,'physical_clock_identified':False}
def verify(packet,root=RER):
    q,c,v,scalar,quantum,clock=dependency_context(root)
    qr=q.verify(quantum,rer=root);cr=c.verify(clock,root=root)
    need(qr.get('verdict')=='PASS' and qr.get('parent_full_mathematical_replay') is True
         and type(qr.get('parent_events_replayed')) is int and qr['parent_events_replayed']==5888,'full original quantum parent proof required')
    need(cr.get('verdict')=='PASS' and cr.get('full_parent_mathematical_replay') is True
         and type(cr.get('events_authenticated')) is int and cr['events_authenticated']==5888
         and type(cr.get('positive_gram_cases')) is int and cr['positive_gram_cases']==40,'full reconstructed clock proof required')
    result=verify_arithmetic(packet,scalar,quantum,clock,v,root)
    dependency_context(root)
    equal(packet['source_pins'],{f:sha256((root/f).read_bytes()).hexdigest() for f in FILES},'unchanged own sources')
    result.update({'parent_events_replayed':5888,'full_clock_replay':True,'full_original_quantum_replay':True})
    return result
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('path',nargs='?',type=Path,default=OUTPUT);ap.add_argument('--root',type=Path,default=RER);a=ap.parse_args()
    print(json.dumps(verify(load(a.path),root=a.root),sort_keys=True,indent=2))

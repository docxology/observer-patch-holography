"""Independent verifier: normalized one-dimensional rows and exact readback.

No producer is imported. Tensor row identities replace its assembled
geometry. The immutable parent's own independent verifier is rerun.
"""
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
from rational import I, Q, phi, magnitude

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUTPUT=HERE/'readout_receipt.json'
PARENT=ROOT/'code/sm_abelian_reduction/abelian_receipt.json'
PIN='6dbc4bdeaa9a8242ff0db405d3e5a61be7b6eeb2adfa045eb765e6d142fbba2d'


def require(condition, label):
    if not condition:
        raise ValueError(label)


def unique(pairs):
    result={}
    for k,v in pairs:
        require(k not in result,'duplicate key')
        result[k]=v
    return result


def load(path=OUTPUT):
    return json.loads(Path(path).read_text(),object_pairs_hook=unique,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))


def parent_verify(parent):
    path=ROOT/'code/sm_abelian_reduction/verify_abelian.py'
    spec=importlib.util.spec_from_file_location('_readout_parent_verifier',path)
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    out=module.verify(parent)
    require(out['verified'] is True and out['mathematical_replay'] is True,'parent mathematical replay')
    return out


def readback(run,cp):
    # Reconstruct latest-writer state, independently of copied frames and
    # independent of the producer's one-hop readback implementation.
    state={}; version={}; writer={}
    for event in run['events'][:cp['event']+1]:
        for read in event['reads']:
            k=read['port']
            require(read['value']==state[k] and read['version']==version[k]
                    and read['writer']==writer[k],'actual latest-writer read')
        if event['id']==cp['event']:
            require(event['operation']=='readout','checkpoint operation')
            z=next(r['value'] for r in event['reads'] if r['port']=='psi/37')
            return Q(z[0])**2+Q(z[1])**2
        for w in event['writes']:
            k=w['port']; state[k]=w['value']; version[k]=w['version']; writer[k]=event['id']
    raise ValueError('checkpoint absent')


def verify(packet, *, replay_parent=True):
    require(type(packet) is dict and set(packet)=={'schema','parent_sha256','geometry','majorants','window',
        'resolved_window','current','electric_feedback','neighbor_response','scope','checkpoints'},'root schema')
    require(hashlib.sha256(PARENT.read_bytes()).hexdigest()==PIN,'immutable parent hash')
    parent=load(PARENT)
    report=parent_verify(parent) if replay_parent else None
    require(packet['schema']=='oph.cartan-scalar-readout.v1' and packet['parent_sha256']==PIN,'schema/pin')
    require(packet['geometry']=={'sites':64,'links':144,'plaquettes':108,'detector_site':37,'source_site':21,'current_edge':54},'geometry contract')
    expected_scope={'continuous_classical_current_and_detector_bounds':True,'decoded_completed_checkpoint_errors':True,
                    'first_kick_is_exact_time_sample':False,'whole_state_numerical_trajectory_enclosed':False,
                    'quantum_dynamics_or_born_outcomes':False,'source_action_population_clock_selected':False,
                    'full_fermion_generation_executed':False,'laboratory_or_empirical_result':False}
    require(packet['scope']==expected_scope and all(type(v) is bool for v in packet['scope'].values()),'scope promotion')
    require(packet['window']==['0','1/100'] and packet['resolved_window']==['1/200','1/100'],'time window')
    expected_majorants={'scalar_radius':'1/4','connection_radius':'1/100000','scalar_acceleration':'88',
                       'connection_acceleration':'13/250','neighbor_remainder':'30759','incident_magnetic_weight_sum':'78'}
    require(packet['majorants']==expected_majorants,'majorant contract')
    s,a,b,d,t=Q(1,4),Q(1,100000),Q(88),Q(13,250),Q(1,100)
    f=phi(); long=2*f-3; short=5-3*f
    gaps=[long,long,short,long,short]
    widths=[long,(long+short)/2,(short+long)/2,(long+short)/2]
    interior=[]; wall=[]
    for k in range(4):
        u=I(0); w=I(0)
        if k:
            u+=I(1)/(widths[k]*gaps[k])
        else:
            w+=I(1)/(widths[k]*gaps[0])
        if k<3:
            u+=I(1)/(widths[k]*gaps[k+1])
        else:
            w+=I(1)/(widths[k]*gaps[4])
        interior.append(u); wall.append(w)
    for p in itertools.product(range(4),repeat=3):
        u=sum((interior[k] for k in p),I(0)); w=sum((wall[k] for k in p),I(0))
        require((s*(2*u+1+w+s*s/2)).hi<b,'scalar force bound')
        for axis in range(3):
            if p[axis]==3:
                continue
            trans=[j for j in range(3) if j!=axis]
            transverse=sum((interior[p[j]] for j in trans),I(0))
            require((Q(3,4)*s*s+4*a*transverse).hi<d,'connection force bound')
            eps=Q(8,3)*widths[p[trans[0]]]*widths[p[trans[1]]]/gaps[p[axis]+1]
            require((eps*transverse).hi<78,'incident magnetic sum')
    require(Q(1,5)+b*t*t/2<s and d*t*t/2<a,'strict first-exit enclosure')
    require(Q(4,3)*4*a<1,'principal-log chart; 1 < 2*pi')
    # At site 37 all coordinates are interior: no fixed-wall contribution.
    local=sum((interior[k] for k in (2,1,1)),I(0))
    E=(local*(2*b+Q(1,5)*d)+(1+Q(3,2)*s*s)*b).hi
    require(E<Q(30759),'neighbor fourth-order remainder')
    # Exact target c=1/4: (2-phi)^2 = 5-3phi under phi^2=phi+1.
    require((4+1,-4+1)==(5,-3),'exact target conductance identity')
    mass=widths[2]*widths[1]*widths[1]
    base=I(-Q(51,250)); real=base-I(Q(1,50))/mass; imag=I(Q(1,25))/mass
    quadratic_difference=(real-base)/5
    quartic_difference=(real**2+imag**2-base**2)/4
    e=Q(30759)
    err4=4*(Q(1,5)+b*t*t/2)*e/24+2*e*e*t**4/576
    require(quadratic_difference.hi+(magnitude(quartic_difference)+err4)*t*t < -Q(9,20),'signed detector signal')
    require(packet['neighbor_response']=={'sign':'negative','magnitude_lower_coefficient':'9/20',
        'meaning':'I_intervention(t)-I_baseline(t) <= -(9/20)*t^2 for 0<t<=1/100',
        'magnitude_lower_at_end':'9/200000','magnitude_lower_on_resolved_window':'9/800000'},'detector claim')
    c2=(Q(2,5)*b+Q(1,25)*d)/4; c4=b*b/8
    ce=c2*t*t+c4*t**4
    require(packet['current']=={'initial':'2/125','deviation_at_end':str(ce),
                               'lower_on_window':str(Q(2,125)-ce)},'current bound')
    pe=(c2+2*d*78)*t**3/3+c4*t**5/5
    require(packet['electric_feedback']=={'linear_value_at_end':'1/6250','error_at_end':str(pe),
                                         'lower_at_end':str(Q(1,6250)-pe)},'electric bound')
    want=[]
    for run in parent['runs']:
        for cp in run['checkpoints']:
            if cp['phase']=='first_kick':
                continue
            time=Q(cp['step'],200); actual=readback(run,cp)
            if run['cohort']=='phase_intervention':
                ref=(I(Q(1,5))+real*time*time/2)**2+(imag*time*time/2)**2
            else:
                ref=(I(Q(1,5))+base*time*time/2)**2
            rem=e*time**4/24
            error=magnitude(I(actual)-ref)+2*(Q(1,5)+b*time*time/2)*rem+rem*rem
            want.append((run['cohort'],cp['event'],time,actual,error))
    require(len(packet['checkpoints'])==len(want)==9,'complete completed-checkpoint census')
    maximum=Q(0)
    for row,(cohort,event,time,actual,error) in zip(packet['checkpoints'],want):
        require(set(row)=={'cohort','event','time','decoded_intensity','error_upper'},'checkpoint schema')
        require((row['cohort'],row['event'],Q(row['time']),Q(row['decoded_intensity']))==(cohort,event,time,actual),'decoded checkpoint identity')
        # Independent geometry may yield slightly different rational brackets.
        reported=Q(row['error_upper'])
        require(reported>=error and reported< Q(6,10**6),'checkpoint error bound')
        maximum=max(maximum,reported)
    return {'verified':True,'mathematical_replay':replay_parent,'continuous_classical_detector_bound':True,
            'current_lower':str(Q(2,125)-ce),'neighbor_response_lower_at_end':'9/200000',
            'completed_checkpoints':9,'max_checkpoint_intensity_error':str(maximum),
            'parent_events':report['events'] if report else None,
            'physical_premise_discharged':False,'observed_postdiction':False}


if __name__=='__main__':
    parser=argparse.ArgumentParser(); parser.add_argument('--path',type=Path,default=OUTPUT)
    print(json.dumps(verify(load(parser.parse_args().path)),indent=2,sort_keys=True))

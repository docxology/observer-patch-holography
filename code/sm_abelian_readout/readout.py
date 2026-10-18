"""A priori nonlinear current and separated scalar-detector certificate.

The frozen binary64 history is only decoded data. Continuous-IVP bounds
follow from an analytic first-exit argument, not from floating replay.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
from rational import I, Q, phi, magnitude

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT/'code/sm_abelian_reduction/abelian_receipt.json'
OUTPUT = HERE/'readout_receipt.json'
PARENT_HASH = '6dbc4bdeaa9a8242ff0db405d3e5a61be7b6eeb2adfa045eb765e6d142fbba2d'
S, A, B, D, T = Q(1,4), Q(1,100000), Q(88), Q(13,250), Q(1,100)


def geometry_bounds():
    f = phi()
    x = [I(0), 2*f-3, 4*f-6, f-1, 3*f-4, I(1)]
    gaps = [b-a for a,b in zip(x,x[1:])]
    weights = [(a+b)/2 for a,b in zip(gaps,gaps[1:])]
    xyz = list(itertools.product(range(4), repeat=3))
    idx = {p:i for i,p in enumerate(xyz)}
    prod = lambda rows: _product(rows)
    mass = [prod(weights[k] for k in p) for p in xyz]
    boundary = [sum((prod(weights[p[j]] for j in range(3) if j != axis)
                     /gaps[0 if k == 0 else 4] for axis,k in enumerate(p) if k in (0,3)), I(0)) for p in xyz]
    edges = []
    lookup = {}
    for i,p in enumerate(xyz):
        for axis in range(3):
            if p[axis] == 3:
                continue
            nxt = tuple(v+(j==axis) for j,v in enumerate(p))
            c = prod(weights[p[j]] for j in range(3) if j!=axis)/gaps[p[axis]+1]
            lookup[p,axis] = len(edges)
            edges.append((i,idx[nxt],c))
    face_sums = [I(0) for _ in edges]
    nfaces = 0
    for p in xyz:
        for a,b in itertools.combinations(range(3),2):
            if p[a]==3 or p[b]==3:
                continue
            pa = tuple(v+(j==a) for j,v in enumerate(p))
            pb = tuple(v+(j==b) for j,v in enumerate(p))
            g = Q(8,3)*weights[p[3-a-b]]/(gaps[p[a]+1]*gaps[p[b]+1])
            for e in (lookup[p,a],lookup[pa,b],lookup[pb,a],lookup[p,b]):
                face_sums[e] += g
            nfaces += 1
    sums = [I(0) for _ in mass]
    for i,j,c in edges:
        sums[i] += c
        sums[j] += c
    accel = [(2*S*sums[i]+(mass[i]+boundary[i]+mass[i]*S*S/2)*S)/mass[i] for i in range(64)]
    link = [(2*c*S*S+4*A*face_sums[e])/(Q(8,3)*c) for e,(_,_,c) in enumerate(edges)]
    i = 37
    remainder = (sums[i]*(2*B+Q(1,5)*D)+(mass[i]+boundary[i]+Q(3,2)*mass[i]*S*S)*B)/mass[i]
    return {'mass37':mass[37], 'force_max': max(z.hi for z in accel),
            'link_max':max(z.hi for z in link), 'remainder37':remainder,
            'gamma_max':max(z.hi for z in face_sums), 'sites':len(mass),
            'edges':len(edges), 'faces':nfaces}


def _product(rows):
    answer = I(1)
    for x in rows:
        answer *= x
    return answer


def load_parent():
    data = PARENT.read_bytes()
    if hashlib.sha256(data).hexdigest()!=PARENT_HASH:
        raise ValueError('immutable parent changed')
    return json.loads(data)


def decoded_intensity(run, checkpoint):
    """Consume actual readout ports; copied checkpoint fields are not inputs."""
    event = run['events'][checkpoint['event']]
    if event['operation'] != 'readout':
        raise ValueError('not a readout')
    read = next(r for r in event['reads'] if r['port']=='psi/37')
    writer = run['events'][read['writer']]
    write = next(w for w in writer['writes'] if w['port']=='psi/37')
    if write['version']!=read['version'] or write['value']!=read['value']:
        raise ValueError('readback writer mismatch')
    re,im = map(Q,read['value'])
    return re*re+im*im


def bounds():
    geo = geometry_bounds()
    if not (geo['force_max']<B and geo['link_max']<D and geo['gamma_max']<78
            and geo['remainder37'].hi<30759):
        raise ValueError('majorant not established')
    mass = geo['mass37']
    a0 = I(-Q(51,250))
    a1 = a0-I(Q(1,50))/mass
    b1 = I(Q(1,25))/mass
    k2 = Q(1,5)*(a1-a0)
    k4 = (a1*a1+b1*b1-a0*a0)/4
    # Each site's remainder is E*t^4/24. Two intensity remainders:
    # 4*(s0+B*t^2/2)*r + 2*r^2.
    E = Q(30759)
    error_coefficient = 4*(Q(1,5)+B*T*T/2)*E/24+2*E*E*T**4/(24**2)
    signal_coefficient = -k2.hi-(magnitude(k4)+error_coefficient)*T*T
    if signal_coefficient <= Q(9,20):
        raise ValueError('separated detector not resolved')
    current_c2 = Q(1,4)*(Q(2,5)*B+Q(1,25)*D)
    current_c4 = B*B/8
    current_error = current_c2*T*T+current_c4*T**4
    feedback_error = (current_c2+2*D*78)*T**3/3+current_c4*T**5/5
    result = {'schema':'oph.cartan-scalar-readout.v1', 'parent_sha256':PARENT_HASH,
        'geometry':{'sites':64,'links':144,'plaquettes':108,'detector_site':37,'source_site':21,'current_edge':54},
        'majorants':{'scalar_radius':str(S),'connection_radius':str(A),'scalar_acceleration':str(B),
                     'connection_acceleration':str(D),'neighbor_remainder':str(E),'incident_magnetic_weight_sum':'78'},
        'window':['0',str(T)], 'resolved_window':['1/200',str(T)],
        'current':{'initial':'2/125','deviation_at_end':str(current_error),
                   'lower_on_window':str(Q(2,125)-current_error)},
        'electric_feedback':{'linear_value_at_end':'1/6250','error_at_end':str(feedback_error),
                             'lower_at_end':str(Q(1,6250)-feedback_error)},
        'neighbor_response':{'sign':'negative','magnitude_lower_coefficient':'9/20',
            'meaning':'I_intervention(t)-I_baseline(t) <= -(9/20)*t^2 for 0<t<=1/100',
            'magnitude_lower_at_end':'9/200000','magnitude_lower_on_resolved_window':'9/800000'},
        'scope':{'continuous_classical_current_and_detector_bounds':True,'decoded_completed_checkpoint_errors':True,
                 'first_kick_is_exact_time_sample':False,'whole_state_numerical_trajectory_enclosed':False,
                 'quantum_dynamics_or_born_outcomes':False,'source_action_population_clock_selected':False,
                 'full_fermion_generation_executed':False,'laboratory_or_empirical_result':False},
        'checkpoints':[]}
    parent = load_parent()
    for run in parent['runs']:
        for cp in run['checkpoints']:
            if cp['phase']=='first_kick':
                continue
            t = Q(cp['step'],200)
            observed = decoded_intensity(run,cp)
            if run['cohort']=='phase_intervention':
                quadratic = (I(Q(1,5))+a1*t*t/2)**2+(b1*t*t/2)**2
            else:
                quadratic = (I(Q(1,5))+a0*t*t/2)**2
            r = E*t**4/24
            analytic = 2*(Q(1,5)+B*t*t/2)*r+r*r
            err = magnitude(I(observed)-quadratic)+analytic
            scale = 10**30
            err = Q(-(-(err*scale).numerator//(err*scale).denominator),scale)
            result['checkpoints'].append({'cohort':run['cohort'],'event':cp['event'],'time':str(t),
                                         'decoded_intensity':str(observed),'error_upper':str(err)})
    return result


def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--write',action='store_true'); args=parser.parse_args()
    data=json.dumps(bounds(),indent=2,sort_keys=True)+'\n'
    if args.write:
        OUTPUT.write_text(data)
    elif OUTPUT.read_text()!=data:
        raise SystemExit('receipt differs; regenerate deliberately')
    print('Cartan continuous readout certificate matches')


if __name__=='__main__':
    main()

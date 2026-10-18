"""Independent integer-interval replay of the charged trajectory enclosure.

The producer is never imported. The Hamiltonian is rebuilt from exact
simplex moments, and Picard/Taylor inclusions are checked with integer
directed rounding. Old binary64 samples are comparison data, never proof
inputs. Neither a physical clock nor a spatial limit is certified.
"""
from __future__ import annotations

from fractions import Fraction as Q
from math import factorial, isfinite, isqrt
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
OUTPUT = Path(__file__).resolve().parent/"runtime/whitney_charged_enclosure_receipt.json"
BITS = 256
UNIT = 1 << BITS
POLY_BITS = 96
SCOPE = "RIGOROUS_FINITE_CHARGED_ACTION_TIME_TUBE__SUPPLIED_MODEL_PARAMETER"
PARENT = "code/electromagnetism/runtime/whitney_charged_dynamics_receipt.json"
PARENT_SHA256 = "6062233dc4707ea0b1c6f8eec4b6a474998224f74a417b6fe2dd9faf46fb5264"
COORDINATES = ["alpha","Re(C)","Im(C)","Re(b)","Im(b)",
               "p_Re(C)","p_Im(C)","p_Re(b)","p_Im(b)"]
METHOD = {"name":"Picard inclusion and interval Taylor remainder",
          "steps":80,"step":"1/40","time_span":["0","2"],"taylor_order":32,
          "interval_bits":BITS,"polynomial_bits":POLY_BITS,
          "coordinate_order":COORDINATES,
          "interval_encoding":"integer endpoint pairs divided by 2^256",
          "polynomial_encoding":"integer coefficients divided by 2^96, ascending powers of local time",
          "error_norm":"maximum absolute canonical coordinate difference",
          "approximant":"piecewise polynomial; adjacent polynomial endpoints need not agree"}
PARAMETERS = {"charge":"1/4","mass_squared":"1/2","quartic":"1/4",
              "geometry_ratio":"6/(7+3*sqrt(5))","alpha_momentum":"0",
              "normalized_initial_energy":"49/40+9/(3200*r)"}
INTERPRETATION = {
    "units":"supplied dimensionless model units",
    "time":"exact supplied action parameter, not measured physical time",
    "action":"full dressed charged-scalar/Maxwell action on the fixed twenty-tetrahedron cone",
    "canonical_map":"C=exp(i*e*alpha)*c; momenta are for action divided by cone volume",
    "imports":["cone geometry","matter law and couplings","temporal gauge","exact initial data","action time"],
    "rigorous_time_enclosure":True,"whole_time_interval":True,
    "physical_clock_selected":False,"spatial_continuum_error_certified":False,
    "observer_history":False,"quantum_history":False,"empirical_comparison":False,
    "formalized_in_Lean":False,
    "historical_comparison":"old binary64 coordinates interpreted as exact dyadic numbers at nominal j/40; original float timestamps are metadata"}
BOUNDS = {"uniform_canonical_polynomial_error_upper":"1/100000000000000000000",
          "historical_position_velocity_error_upper":"1/10000000000",
          "normalized_denominator_lower_bound":"2/5"}
PINS = {
    "Lean/Screen/SeamCurrentEdge30Moment.lean",
    "Lean/Screen/SeamCurrentCarrierQuotient.lean",
    "Lean/ObserverPatchHolography/CoreAxioms.lean",
    "paper/tex_fragments/WHITNEY_CHARGED_MATTER.tex",
    "paper/tex_fragments/WHITNEY_CHARGED_EXECUTION.tex",
    "paper/tex_fragments/WHITNEY_EPHEMERIS_CLOCK.tex",
    "paper/tex_fragments/WHITNEY_CHARGED_ENCLOSURE.tex",
    "code/electromagnetism/whitney_charged_dynamics.py",
    "code/electromagnetism/verify_whitney_charged_dynamics.py",
    "code/electromagnetism/whitney_charged_enclosure.py",
    "code/electromagnetism/verify_whitney_charged_enclosure.py",
    "code/electromagnetism/test_whitney_charged_enclosure.py",
    PARENT,
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def same(actual, expected, message):
    require(type(actual) is type(expected),message)
    require(json.dumps(actual,sort_keys=True,allow_nan=False)==
            json.dumps(expected,sort_keys=True,allow_nan=False),message)


def load(path=OUTPUT):
    def pairs(items):
        result={}
        for key,value in items:
            require(key not in result,"duplicate JSON key")
            result[key]=value
        return result
    def floating(value):
        raise ValueError("enclosure JSON admits no floating values")
    return json.loads(Path(path).read_text(encoding="utf-8"),object_pairs_hook=pairs,
                      parse_float=floating,parse_constant=floating)


def integer(value):
    require(type(value) is str and re.fullmatch(r"0|-?[1-9][0-9]*",value) is not None,
            "canonical signed integer string required")
    require(len(value)<=100,"oversized interval integer")
    return int(value)


class Box:
    """Independent fixed-point interval implementation, integer endpoints."""
    __slots__=("low","high")

    def __init__(self,value=0,high=None):
        if high is None:
            q=Q(value)
            self.low=q.numerator*UNIT//q.denominator
            self.high=-(-q.numerator*UNIT//q.denominator)
        else:
            self.low,self.high=value,high
        require(self.low<=self.high,"reversed interval")

    @classmethod
    def parse(cls,pair):
        require(type(pair) is list and len(pair)==2,"interval pair required")
        return cls(integer(pair[0]),integer(pair[1]))

    @staticmethod
    def coerce(x):
        return x if isinstance(x,Box) else Box(x)

    def __add__(self,x):
        x=self.coerce(x)
        return Box(self.low+x.low,self.high+x.high)

    __radd__=__add__

    def __neg__(self):
        return Box(-self.high,-self.low)

    def __sub__(self,x):
        return self+-self.coerce(x)

    def __rsub__(self,x):
        return self.coerce(x)+-self

    def __mul__(self,x):
        x=self.coerce(x)
        if self.low>=0 and x.low>=0:
            a,b=self.low*x.low,self.high*x.high
        elif self.high<=0 and x.high<=0:
            a,b=self.high*x.high,self.low*x.low
        else:
            corners=[self.low*x.low,self.low*x.high,self.high*x.low,self.high*x.high]
            a,b=min(corners),max(corners)
        return Box(a//UNIT,-(-b//UNIT))

    __rmul__=__mul__

    def inverse(self):
        require(not self.low<=0<=self.high,"division through zero")
        return Box(UNIT*UNIT//self.high,-(-UNIT*UNIT//self.low))

    def __truediv__(self,x):
        return self*self.coerce(x).inverse()

    def __rtruediv__(self,x):
        return self.coerce(x)*self.inverse()

    def contains(self,x,strict=False):
        return (self.low<x.low and x.high<self.high) if strict else (
            self.low<=x.low and x.high<=self.high)

    def magnitude(self):
        return max(abs(self.low),abs(self.high))


class Expression:
    """Scalar expression DAG, independent normalized-derivative recurrence."""
    def __init__(self,graph,tag,args):
        self.graph,self.tag,self.args=graph,tag,args
        self.index=len(graph)
        graph.append(self)

    def cast(self,x):
        return x if isinstance(x,Expression) else Expression(self.graph,"c",[Box.coerce(x)])

    def __add__(self,x):return Expression(self.graph,"+",[self,self.cast(x)])
    __radd__=__add__
    def __neg__(self):return Expression(self.graph,"-",[self])
    def __sub__(self,x):return self+-self.cast(x)
    def __rsub__(self,x):return self.cast(x)+-self
    def __mul__(self,x):return Expression(self.graph,"*",[self,self.cast(x)])
    __rmul__=__mul__
    def __truediv__(self,x):return self*Expression(self.graph,"/",[self.cast(x)])


def derivatives(graph,outputs,y,degree):
    coefficients=[[] for _ in graph]
    state=[[b] for b in y]
    zero=Box(0)
    for k in range(degree):
        for node in graph:
            tag,args=node.tag,node.args
            if tag=="v":a=state[args[0]][k]
            elif tag=="c":a=args[0] if k==0 else zero
            elif tag=="+":a=coefficients[args[0].index][k]+coefficients[args[1].index][k]
            elif tag=="-":a=-coefficients[args[0].index][k]
            elif tag=="*":
                u,v=coefficients[args[0].index],coefficients[args[1].index]
                a=zero
                for j in range(k+1):a=a+u[j]*v[k-j]
            elif tag=="/":
                u=coefficients[args[0].index]
                if k==0:a=u[0].inverse()
                else:
                    a=zero
                    for j in range(1,k+1):a=a+u[j]*coefficients[node.index][k-j]
                    a=-a/u[0]
            else:raise ValueError("bad expression")
            coefficients[node.index].append(a)
        for j,out in enumerate(outputs):state[j].append(coefficients[out.index][k]/(k+1))
    return state


# Exact sparse polynomial algebra in four real scalar coordinates. These
# identities derive the kinetic reduction and potential from simplex moments.
class Polynomial:
    def __init__(self,terms=None):
        self.terms={k:Q(v) for k,v in (terms or {}).items() if v}

    @classmethod
    def constant(cls,x):return cls({(0,0,0,0):Q(x)})
    @classmethod
    def variable(cls,j):
        k=[0]*4;k[j]=1
        return cls({tuple(k):Q(1)})
    @classmethod
    def cast(cls,x):return x if isinstance(x,cls) else cls.constant(x)
    def __add__(self,x):
        x=self.cast(x);d=self.terms.copy()
        for k,v in x.terms.items():d[k]=d.get(k,Q(0))+v
        return Polynomial(d)
    __radd__=__add__
    def __neg__(self):return Polynomial({k:-v for k,v in self.terms.items()})
    def __sub__(self,x):return self+-self.cast(x)
    def __rsub__(self,x):return self.cast(x)+-self
    def __mul__(self,x):
        x=self.cast(x);d={}
        for a,u in self.terms.items():
            for b,v in x.terms.items():
                k=tuple(i+j for i,j in zip(a,b,strict=True));d[k]=d.get(k,Q(0))+u*v
        return Polynomial(d)
    __rmul__=__mul__
    def derivative(self,j):
        d={}
        for k,v in self.terms.items():
            if k[j]:
                l=list(k);l[j]-=1;d[tuple(l)]=v*k[j]
        return Polynomial(d)
    def evaluate(self,x):
        result=0
        for k,c in sorted(self.terms.items()):
            term=c
            for j,power in enumerate(k):
                for _ in range(power):term=term*x[j]
            result=result+term
        return result


def convolution(a,b):
    result=[Polynomial() for _ in range(len(a)+len(b)-1)]
    for i,x in enumerate(a):
        for j,y in enumerate(b):result[i+j]=result[i+j]+x*y
    return result


def moment(n):return Q(6,(n+1)*(n+2)*(n+3))
def integrate_polynomial(a):return sum((p*moment(n) for n,p in enumerate(a)),Polynomial())


def action_algebra():
    cr,ci,br,bi=[Polynomial.variable(i) for i in range(4)]
    real,imag=[br,cr-br],[bi,ci-bi]
    nr,ni=convolution(real,real),convolution(imag,imag)
    norm=[a+b for a,b in zip(nr,ni,strict=True)]
    s=[Polynomial(),Polynomial.constant(1)]
    one_s=[Polynomial.constant(1),Polynomial.constant(-1)]
    a,b,c=2*moment(2),2*(moment(1)-moment(2)),2*(1-2*moment(1)+moment(2))
    det=a*c-b*b
    require(det==Q(3,20),"scalar mass determinant")
    inverse=((c/det,-b/det),(-b/det,a/det))
    e=Q(1,4)
    cross=[]
    for shape in [s,one_s]:
        factor=convolution(s,shape)
        cross += [2*e*integrate_polynomial(convolution(factor,imag)),
                  -2*e*integrate_polynomial(convolution(factor,real))]
    w=[inverse[0][0]*cross[0]+inverse[0][1]*cross[2],
       inverse[0][0]*cross[1]+inverse[0][1]*cross[3],
       inverse[1][0]*cross[0]+inverse[1][1]*cross[2],
       inverse[1][0]*cross[1]+inverse[1][1]*cross[3]]
    kinetic=2*e*e*integrate_polynomial([Polynomial(),Polynomial()]+norm)
    schur=kinetic-sum((x*y for x,y in zip(cross,w,strict=True)),Polynomial())
    norm_u=(cr-br)*(cr-br)+(ci-bi)*(ci-bi)
    require(schur.terms==(Q(2,525)*e*e*norm_u).terms,"Schur identity")
    potential=Q(1,2)*integrate_polynomial(norm)+Q(1,8)*integrate_polynomial(convolution(norm,norm))
    return {"inverse":inverse,"w":w,"schur":schur,"norm_u":norm_u,
            "gradient":[potential.derivative(j) for j in range(4)]}


ALGEBRA=action_algebra()


def ratio():
    a=isqrt(5*UNIT*UNIT)
    require(a*a<=5*UNIT*UNIT<(a+1)*(a+1),"sqrt5 integer enclosure")
    result=6/(7+3*Box(a,a+1))
    require(result.low>Box(Q(2,5)).high,"positive geometry ratio")
    return result


def field(y,r):
    x,p=y[1:5],y[5:9]
    w=[a.evaluate(x) for a in ALGEBRA['w']]
    d=r+Q(1,4200)*((x[0]-x[2])*(x[0]-x[2])+(x[1]-x[3])*(x[1]-x[3]))
    av=-sum((u*v for u,v in zip(w,p,strict=True)),0)/d
    hi=ALGEBRA['inverse']
    xd=[sum((hi[j//2][k]*p[2*k+j%2] for k in range(2)),0)-w[j]*av for j in range(4)]
    pd=[]
    for j in range(4):
        dw=sum((a.derivative(j).evaluate(x)*v for a,v in zip(ALGEBRA['w'],p,strict=True)),0)
        ds=ALGEBRA['schur'].derivative(j).evaluate(x)
        grad=r*ALGEBRA['norm_u'].derivative(j).evaluate(x)+ALGEBRA['gradient'][j].evaluate(x)
        pd.append(av*dw+av*av*ds/2-grad)
    return [av]+xd+pd


def graph():
    nodes=[]
    y=[Expression(nodes,'v',[j]) for j in range(9)]
    r=Expression(nodes,'c',[ratio()])
    return nodes,field(y,r)


def polynomial_value(coefficients,h):
    result=Box(0)
    for c in reversed(coefficients):result=c+h*result
    return result


def parse_state(value):
    require(type(value) is list and len(value)==9,"nine canonical coordinates required")
    return [Box.parse(pair) for pair in value]


def check_step(y,whole,next_y,polynomial,h,order,nodes,outputs):
    time=Box(0,h.high)
    image=[a+time*f for a,f in zip(y,field(whole,ratio()),strict=True)]
    require(all(b.contains(v,strict=True) for b,v in zip(whole,image,strict=True)),"Picard inclusion fails")
    local=derivatives(nodes,outputs,y,order)
    remainder=derivatives(nodes,outputs,whole,order+1)
    power=Box(1)
    for _ in range(order+1):power=power*h
    endpoints=[polynomial_value(a,h)+b[-1]*power for a,b in zip(local,remainder,strict=True)]
    require(all(b.contains(v) for b,v in zip(next_y,endpoints,strict=True)),"Taylor endpoint inclusion fails")
    require(type(polynomial) is list and len(polynomial)==9,"nine dense polynomials required")
    error=0
    for coefficients,actual,tail in zip(polynomial,local,remainder,strict=True):
        require(type(coefficients) is list and len(coefficients)==order+1,"Taylor polynomial degree")
        radii=[]
        for value,interval in zip(coefficients,actual,strict=True):
            approximation=Box(Q(integer(value),1<<POLY_BITS))
            difference=interval-approximation
            radii.append(Box(difference.magnitude(),difference.magnitude()))
        bound=polynomial_value(radii,h)+Box(tail[-1].magnitude(),tail[-1].magnitude())*power
        error=max(error,bound.high)
    return error


def initial():
    return [Box(x) for x in [0,1,0,1,0,0,Q(3,10),0,Q(-3,10)]]


def sine_cosine(angle):
    """Taylor with the real-variable Lagrange bound |remainder|<=A^41/41!."""
    require(angle.magnitude()<2*UNIT,"trigonometric comparison range")
    sine,cosine,power=Box(0),Box(0),Box(1)
    for n in range(41):
        coefficient=Q((-1)**(n//2),factorial(n))
        if n%2:sine=sine+coefficient*power
        else:cosine=cosine+coefficient*power
        power=power*angle
    a=Q(angle.magnitude(),UNIT)
    tail=Box(a**41/factorial(41))
    error=Box(-tail.high,tail.high)
    return sine+error,cosine+error


def original_coordinates(y):
    av,*_=field(y,ratio())
    velocity=field(y,ratio())
    sine,cosine=sine_cosine(y[0]/4)
    cr=cosine*y[1]+sine*y[2]
    ci=cosine*y[2]-sine*y[1]
    before_real=velocity[1]+av*y[2]/4
    before_imag=velocity[2]-av*y[1]/4
    cd_real=cosine*before_real+sine*before_imag
    cd_imag=cosine*before_imag-sine*before_real
    return [y[0],cr,ci,y[3],y[4],av,cd_real,cd_imag,velocity[3],velocity[4]]


def historical_comparison(rows):
    data=(ROOT/PARENT).read_bytes()
    require(hashlib.sha256(data).hexdigest()==PARENT_SHA256,"historical receipt identity changed")
    old=json.loads(data)
    require(len(old['samples'])==81,"historical sample count")
    bound=0
    for j,(row,sample) in enumerate(zip(rows,old['samples'],strict=True)):
        require(abs(Q.from_float(sample['t'])-Q(j,40))<Q(1,10**14),"historical nominal sample time")
        values=sample['q_reduced']+sample['v_reduced']
        require(len(values)==10 and all(type(x) in (float,int) and isfinite(x) for x in values),
                "historical binary64 coordinates")
        enclosed=original_coordinates(parse_state(row['state']))
        for x,y in zip(enclosed,values,strict=True):
            exact=Q.from_float(y) if isinstance(y,float) else Q(y)
            bound=max(bound,(x-Box(exact)).magnitude())
    require(Q(bound,UNIT)<=Q(BOUNDS['historical_position_velocity_error_upper']),
            "historical coordinate discrepancy exceeds bound")
    return Q(bound,UNIT)


def verify(packet):
    require(type(packet) is dict,"receipt object required")
    require(set(packet)=={'schema','scope','source_pins','parameters','method','interpretation','bounds','states'},
            "unexpected or missing receipt field")
    same(packet['schema'],'oph.whitney_charged_enclosure.v1',"schema")
    same(packet['scope'],SCOPE,"scope")
    same(packet['parameters'],PARAMETERS,"declared parameters")
    same(packet['method'],METHOD,"integration method contract")
    same(packet['interpretation'],INTERPRETATION,"interpretation contract")
    same(packet['bounds'],BOUNDS,"claimed bound contract")
    pins=packet['source_pins']
    require(type(pins) is dict and set(pins)==PINS,"exact source pin set required")
    for path,digest in pins.items():
        require(type(digest) is str and re.fullmatch('[0-9a-f]{64}',digest) is not None,"source digest")
        require(hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,"stale source pin: "+path)
    rows=packet['states']
    require(type(rows) is list and len(rows)==81,"81 state enclosures required")
    for j,row in enumerate(rows):
        require(type(row) is dict and set(row)==({'state'} if j==80 else {'state','picard_box','polynomial'}),
                "step record fields")
    y=parse_state(rows[0]['state'])
    same(rows[0]['state'],[[str(x.low),str(x.high)] for x in initial()],"exact initial enclosure")
    nodes,outputs=graph()
    h=Box(Q(1,40))
    maximum=0
    for j in range(80):
        row=rows[j];next_y=parse_state(rows[j+1]['state'])
        step_error=check_step(y,parse_state(row['picard_box']),next_y,
                             row['polynomial'],h,32,nodes,outputs)
        require(Q(step_error,UNIT)<=Q(BOUNDS['uniform_canonical_polynomial_error_upper']),
                "continuous-time polynomial error exceeds bound")
        maximum=max(maximum,step_error)
        y=next_y
    require(Q(maximum,UNIT)<=Q(BOUNDS['uniform_canonical_polynomial_error_upper']),
            "continuous-time polynomial error exceeds bound")
    # The endpoint is separated from alpha(0)=0; the enclosed history is not
    # constant. Its nonzero initial electric field and Gauss-compatible charge
    # follow from the exact initial data and the pinned symmetry-lift proof.
    require(y[0].high<Box(Q(-1,100)).low,"nontrivial charged coordinate change")
    historic=historical_comparison(rows)
    return {"accepted":True,"scope":SCOPE,"steps":80,"samples":81,"taylor_order":32,
            "canonical_dimension":9,"time_horizon":"2",
            "uniform_canonical_polynomial_error_upper":BOUNDS['uniform_canonical_polynomial_error_upper'],
            "historical_position_velocity_error_upper":BOUNDS['historical_position_velocity_error_upper'],
            "normalized_denominator_lower_bound":"2/5",
            "rigorous_time_enclosure":True,"whole_time_interval":True,
            "physical_clock_selected":False,"spatial_continuum_error_certified":False,
            "observer_history":False,"quantum_history":False,"empirical_comparison":False,
            "formalized_in_Lean":False,
            "exact_diagnostics":{"uniform_error_replay_upper":str(Q(maximum,UNIT)),
                                 "historical_error_replay_upper":str(historic)}}


if __name__=='__main__':
    print(json.dumps(verify(load()),sort_keys=True))

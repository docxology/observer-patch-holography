"""Producer: online graph heights, independent of the replay verifier's Kahn pass."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from math import isqrt
from hashlib import sha256
from pathlib import Path
import argparse, importlib.util, json, sys

HERE=Path(__file__).resolve().parent
RER=HERE.parents[1]
PARENT='code/source_scalar_execution/source_scalar_execution_receipt.json'
PARENT_SHA='cf246c2caa072334e0d4796c1c6c49d2a231a263ff34281843a1c35c7cdbb69a'
VERIFIER='code/source_scalar_execution/verify_source_scalar_execution.py'
VERIFIER_SHA='c03892572732bbf7d019e721d19b6a249b445e2dc30f54d3c237be938cf88d42'
PARENT_COMMIT='f59c99d69d596055fa77eef5fcde4d184f92bb93'
FILES=('code/source_scalar_clock/source_scalar_clock.py',
       'code/source_scalar_clock/verify_source_scalar_clock.py',
       'code/source_scalar_clock/test_source_scalar_clock.py',
       'Lean/Screen/ActionTimeGram.lean','Lean/Screen/SourceActionTime.lean',
       'paper/tex_fragments/SOURCE_SCALAR_CLOCK.tex')
OUTPUT=HERE/'source_scalar_clock_receipt.json'
SCALE=10**12
def raw(x):return (json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False,ensure_ascii=True)+'\n').encode('ascii')
def need(x,s):
    if not x:raise ValueError(s)
def digest(x):return sha256(raw(x)).hexdigest()
def context(root=RER):
    source=(root/PARENT).read_bytes();need(sha256(source).hexdigest()==PARENT_SHA,'immutable scalar receipt')
    code=(root/VERIFIER).read_bytes();need(sha256(code).hexdigest()==VERIFIER_SHA,'immutable scalar verifier')
    name='_source_scalar_clock_producer_parent';spec=importlib.util.spec_from_file_location(name,root/VERIFIER)
    v=importlib.util.module_from_spec(spec);sys.modules[name]=v
    exec(compile(code,str(root/VERIFIER),'exec'),v.__dict__)
    return v,v.load(root/PARENT)
def scope():return {'inference_reads_stored_step_time_schedule_or_container_position':False,
    'authenticated_read_edges_define_graph':True,'audit_ledger_edges_are_field_edges':False,
    'initial_seed_layers_causally_ordered':False,'complete_parent_history_required':True,
    'resource_to_site_adapter_supplied':True,'action_mass_quadrature_orientation_and_relative_scale_supplied':True,
    'one_duration_per_whole_configuration_layer':True,'arbitrary_site_dependent_lapse':False,
    'candidate_duration_uniformity_assumed':False,'hypothetical_configuration_noise_budget':True,
    'hidden_full_configuration_stationarity_required':True,'noisy_history_existence_certified':False,
    'interval_overlap_implies_history_existence':False,'increment_residual_is_unscaled_EL_residual':False,
    'physical_or_regional_time_slice_claim':False,'causal_count_clock_identified':False,
    'source_native_law_selected':False,'graph_reconstruction_formalized_in_Lean':False}
def trace_report(t,v,m,A):
    heights={};byid={};byhash={};writes={};children=defaultdict(set);parents={};ledger='0'*64;reads=0
    for e in t['events']:
        material={k:e[k] for k in ('id','reads','write','ledger_parent')};h=digest(material)
        need(h==e['hash'] and e['ledger_parent']==ledger,'event authentication');ident=raw(e['id'])
        need(ident not in byid,'unique event');ps=[]
        for r in e['reads']:
            need(raw(r)==raw(writes[raw(r[:2])]),'actual read');p=byid[raw(r[2])];ps.append(p);children[p].add(h);reads+=1
        need(len(set(ps))==len(ps),'duplicate field parent');parents[h]=set(ps)
        heights[h]=1+max(heights[p] for p in ps) if ps else 0
        w=e['write'];need(raw(w[2])==ident and raw(w[:2]) not in writes,'unique writer/version')
        writes[raw(w[:2])]=w;byid[ident]=h;byhash[h]=e;ledger=h
    need(ledger==t['final_hash'],'final chain')
    roots={h for h,d in heights.items() if d==0}
    degree={h:sum(heights[c]==1 for c in children[h]) for h in roots}
    layers=[{h for h in roots if degree[h]==1},{h for h in roots if degree[h]>1}]
    layers.extend({h for h,d in heights.items() if d==j} for j in range(1,max(heights.values())+1))
    need(all(len(x)==64 for x in layers) and len(layers)==23,'layer census')
    vectors=[];ordered=[]
    for i,layer in enumerate(layers):
        site={byhash[h]['write'][0]%64:h for h in layer};need(set(site)==set(range(64)),'site coverage')
        order=[site[k] for k in range(64)];ordered.append(order)
        vectors.append([v.parse(byhash[h]['write'][3]) for h in order])
        if i>=2:
            for k,h in enumerate(order):need(parents[h]=={ordered[i-2][k]}|{ordered[i-1][n] for n,_ in A[k]},'stencil')
    need([[x.encode() for x in row] for row in vectors]==t['layers'],'stored layer equality')
    ticks=[];undefined=[]
    for i in range(1,len(vectors)-1):
        old,u,nxt=vectors[i-1:i+2];au=v.apply(A,u);E=v.inner(m,u,au);d=[2*x-y-z for x,y,z in zip(u,old,nxt)]
        if E.sign()==0:
            need(all(x.sign()==0 for x in u) and all(x.sign()==0 for x in d),'zero-center full residual')
            undefined.append(i-1);continue
        s=v.inner(m,u,d)/E;need(all(x==s*y for x,y in zip(d,au)),'full centered residual');ticks.append(s.encode())
    need(not ticks or all(x==ticks[0] for x in ticks),'common recovered tick')
    return vectors, {'event_count':len(byhash),'dynamic_read_count':reads,
      'height_census':[[j,sum(d==j for d in heights.values())] for j in range(max(heights.values())+1)],
      'seed_first_update_child_census':[list(x) for x in sorted(Counter(degree.values()).items())],
      'layer_sizes':[len(x) for x in layers],
      'layer_value_sha256':[digest([x.encode() for x in row]) for row in vectors],
      'ordered_layer_event_sha256':[digest(row) for row in ordered],
      'defined_tick_centers':len(ticks),'undefined_center_indices':undefined,
      'recovered_squared_tick_Qphi':ticks[0] if ticks else None,
      'full_centered_residual_zero_at_defined_centers':True,
      'parent_trace_final_hash':t['final_hash']}

encoded=raw
def infer(p,m,x,y,z):
 need(len(m)==len(x)==len(y)==len(z)>0,'common finite dimension')
 need(all(mi.sign()>0 for mi in m),'positive diagonal mass')
 dot=lambda a,b:sum((w*u*v for w,u,v in zip(m,a,b)),p.R())
 xx,xy,yy=dot(x,x),dot(x,y),dot(y,y);det=xx*yy-xy*xy
 need(det.sign()>0,'positive 2x2 Gram determinant')
 zx,zy=dot(z,x),dot(z,y);alpha=(zx*yy-zy*xy)/det;beta=(zy*xx-zx*xy)/det
 need(all((zi-alpha*xi-beta*yi).sign()==0 for xi,yi,zi in zip(x,y,z)),'full vector decomposition')
 need(alpha.sign()>0 and beta.sign()<0,'positive durations')
 hm2=-2*beta/(alpha*(alpha+1));hp2=alpha*alpha*hm2
 return {'gram_Qphi':[xx.encode(),xy.encode(),yy.encode()],'gram_determinant_Qphi':det.encode(),
  'gram_determinant_interval':list(map(str,p.value_bounds(det))),
  'alpha_Qphi':alpha.encode(),'beta_Qphi':beta.encode(),
  'previous_squared_duration_Qphi':hm2.encode(),'next_squared_duration_Qphi':hp2.encode()}


def exact(x, message):
    need(type(x) in (int, F), message)
    return F(x)


def sqrt_interval(x):
    x = exact(x, 'exact square')
    need(x >= 0, 'nonnegative square')
    k = isqrt(x.numerator*SCALE*SCALE//x.denominator)
    return [F(k, SCALE), F(k if F(k, SCALE)**2 == x else k+1, SCALE)]


def coefficient_box(alpha, beta, la, lb, ex, ey, ez, rho=F(0)):
    alpha, beta, la, lb, ex, ey, ez, rho = [exact(x, 'exact bound input')
                                          for x in (alpha, beta, la, lb, ex, ey, ez, rho)]
    need(alpha > 0 and beta < 0, 'nominal duration signs')
    need(la > 0 and lb > 0 and min(ex, ey, ez, rho) >= 0, 'positive norms/nonnegative budgets')
    q = ex*la+ey*lb
    need(q < 1, 'conditioning margin')
    B = (ez+rho+ex*abs(alpha)+ey*abs(beta))/(1-q)
    da, db = la*B, lb*B
    al, au, bl, bu = alpha-da, alpha+da, -beta-db, -beta+db
    need(al > 0 and bl > 0, 'robust duration signs')
    hm2 = [2*bl/(au*(au+1)), 2*bu/(al*(al+1))]
    hp2 = [2*bl*al/(al+1), 2*bu*au/(au+1)]
    return {'q': q, 'alpha_radius': da, 'beta_radius': db,
            'alpha_interval': [al, au], 'negative_beta_interval': [bl, bu],
            'previous_squared_duration_interval': hm2, 'next_squared_duration_interval': hp2,
            'previous_duration_interval': [sqrt_interval(hm2[0])[0], sqrt_interval(hm2[1])[1]],
            'next_duration_interval': [sqrt_interval(hp2[0])[0], sqrt_interval(hp2[1])[1]]}


def strings(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, list):
        return [strings(v) for v in x]
    if isinstance(x, dict):
        return {k: strings(v) for k, v in x.items()}
    return x


def intersect_edges(rows):
    need(len(rows) == 20, 'twenty consecutive triples')
    candidates = [[] for _ in range(21)]
    for j, row in enumerate(rows):
        candidates[j].append(row['previous_duration_interval'])
        candidates[j+1].append(row['next_duration_interval'])
    edges = [[max(v[0] for v in entries), min(v[1] for v in entries)] for entries in candidates]
    need(all(0 < lo <= hi for lo, hi in edges), 'shared interval intersection')
    return edges



def produce(root=RER):
    v,parent=context(root);need(v.verify(parent,root=root)['verdict']=='PASS','fresh full parent proof')
    m,A,*_=v.model(root);reports={};vectors={};records=[];schedules={};epsilon=F(1,10**8)
    for name,trace in parent['traces'].items():
        vectors[name],reports[name]=trace_report(trace,v,m,A)
    for name in ('ascending_intervention','descending_intervention'):
        numeric=[]
        for j in range(1,21):
            older,u,newer=vectors[name][j:j+3]
            x=[ui-oi for ui,oi in zip(u,older)];y=v.apply(A,u);z=[ni-ui for ni,ui in zip(newer,u)]
            info=infer(v,m,x,y,z);xx,xy,yy=map(v.parse,info['gram_Qphi']);D=xx*yy-xy*xy
            need(v.parse(info['alpha_Qphi'])==v.R(1) and v.parse(info['beta_Qphi'])==v.R(F(-1,245)), 'actual inferred coefficients')
            need(v.parse(info['previous_squared_duration_Qphi'])==v.R(F(1,245))
                 and v.parse(info['next_squared_duration_Qphi'])==v.R(F(1,245)), 'identified positive durations')
            def upper(square):
                lo,hi=v.norm_bounds(square)
                return lo if v.R(lo*lo)==square else hi
            la,lb=upper(yy/D),upper(xx/D)
            bounds=coefficient_box(1,F(-1,245),la,lb,2*epsilon,614*epsilon,2*epsilon)
            numeric.append(bounds)
            records.append({'trace':name,'center_step':j,**info,
                            'left_inverse_row_norm_upper':[str(la),str(lb)],**strings(bounds)})
        edges=intersect_edges(numeric);elapsed=[[F(0),F(0)]]
        for lo,hi in edges:
            need((v.R(lo)-v.TAU).sign()<=0 and (v.R(hi)-v.TAU).sign()>=0,'nominal interval inhabitant')
            elapsed.append([elapsed[-1][0]+lo,elapsed[-1][1]+hi])
        schedules[name]=strings({'edge_duration_intervals':edges,'elapsed_time_intervals':elapsed})
    need(schedules['ascending_intervention']==schedules['descending_intervention'],'schedule invariant values')
    final=list(map(F,schedules['ascending_intervention']['elapsed_time_intervals'][-1]))
    lower=min(F(r['gram_determinant_interval'][0]) for r in records)
    return {'schema':'oph.source-scalar-clock.v1',
      'parent':{'path':PARENT,'sha256':PARENT_SHA,'source_commit':PARENT_COMMIT},
      'traces':reports,
      'exact_duration':{'positive_tick_Qphi':['-1/35','2/35'],'squared_tick':'1/245',
                        'identified_edges':21,'positive_gram_cases':40,'common_gram_lower':str(lower),
                        'full_vector_decompositions':True,'shared_edge_equality':True,
                        'baseline_identifies_duration':False},
      'stability':{'budget':{'configuration_M_norm':str(epsilon),'operator_norm_upper':'614','increment_residual_norm':'0'},
                   'records':records,'schedules':schedules,
                   'summary':strings({'maximum_q':max(F(r['q']) for r in records),
                    'maximum_alpha_radius':max(F(r['alpha_radius']) for r in records),
                    'maximum_beta_radius':max(F(r['beta_radius']) for r in records),
                    'final_elapsed_interval':final,'final_elapsed_width':final[1]-final[0]})},
      'scope':scope(),'source_pins':{f:sha256((root/f).read_bytes()).hexdigest() for f in FILES}}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    ap.add_argument('--root',type=Path,default=RER);a=ap.parse_args();packet=produce(a.root);b=raw(packet)
    output=a.root/'code/source_scalar_clock/source_scalar_clock_receipt.json'
    if a.write:output.write_bytes(b)
    if a.check:need(output.read_bytes()==b,'canonical clock receipt drift')
    print(json.dumps({'exact_duration':packet['exact_duration'],'stability':packet['stability']['summary']},indent=2))

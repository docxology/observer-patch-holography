"""Independent unordered-event authentication, Kahn layers and full action replay."""
from collections import Counter, defaultdict, deque
from fractions import Fraction as F
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
GRID=SCALE
def need(ok,message):
    if not ok:raise ValueError(message)
def raw(x):return (json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False,ensure_ascii=True)+'\n').encode('ascii')
def same(a,b,message):need(raw(a)==raw(b),message)
def digest(x):return sha256(raw(x)).hexdigest()
def pairs(xs):
    out={}
    for k,v in xs:need(k not in out,'duplicate JSON key');out[k]=v
    return out
def bad_number(x):raise ValueError('noninteger JSON token')
def load(path=OUTPUT):
    b=Path(path).read_bytes();need(len(b)<500000,'receipt size')
    return json.loads(b.decode('ascii'),object_pairs_hook=pairs,parse_float=bad_number,parse_constant=bad_number)
def context(root=RER):
    source=(root/PARENT).read_bytes();need(sha256(source).hexdigest()==PARENT_SHA,'immutable scalar receipt')
    code=(root/VERIFIER).read_bytes();need(sha256(code).hexdigest()==VERIFIER_SHA,'immutable scalar verifier')
    name='_source_scalar_clock_independent_parent';spec=importlib.util.spec_from_file_location(name,root/VERIFIER)
    v=importlib.util.module_from_spec(spec);sys.modules[name]=v
    exec(compile(code,str(root/VERIFIER),'exec'),v.__dict__)
    return v,v.load(root/PARENT)
def identity(x):
    need((type(x) is str and 0<len(x)<=200) or
         (type(x) is list and len(x)==2 and all(type(n) is int and n>=0 for n in x)), 'opaque identity shape')
    return raw(x)
def hash_string(x):return type(x) is str and len(x)==64 and all(c in '0123456789abcdef' for c in x)
def authenticate(trace):
    events=trace['events'];need(type(events) is list and 0<len(events)<=10000,'event list')
    nodes={};ids={};versions={};next_audit={}
    for e in events:
        need(type(e) is dict and set(e)=={'id','reads','write','ledger_parent','hash'},'event schema')
        ident=identity(e['id']);h=e['hash'];need(hash_string(h) and hash_string(e['ledger_parent']),'hash shape')
        need(h not in nodes and ident not in ids,'unique event/hash')
        need(e['ledger_parent'] not in next_audit,'forked audit chain')
        same(digest({k:e[k] for k in ('id','reads','write','ledger_parent')}),h,'event authentication')
        w=e['write'];need(type(w) is list and len(w)==4,'write schema')
        need(type(w[0]) is int and 0<=w[0]<128 and type(w[1]) is int and w[1]>0,'resource/version types')
        same(w[2],e['id'],'write identity');rv=(w[0],w[1]);need(rv not in versions,'unique version')
        need(type(e['reads']) is list,'read schema')
        nodes[h]=e;ids[ident]=h;versions[rv]=h;next_audit[e['ledger_parent']]=h
    # Authentication traverses explicit audit pointers. It does not group events
    # by audit position, and the following graph algorithm never sees this order.
    positions={};cursor='0'*64
    while cursor in next_audit:
        cursor=next_audit[cursor];need(cursor not in positions,'audit cycle');positions[cursor]=len(positions)
    need(len(positions)==len(nodes),'incomplete audit chain');same(cursor,trace['final_hash'],'terminal hash')
    graph={};count=0
    for h,e in nodes.items():
        parents=[]
        for r in e['reads']:
            need(type(r) is list and len(r)==4,'read tuple')
            need(type(r[0]) is int and 0<=r[0]<128 and type(r[1]) is int and r[1]>0,'read resource/version types')
            rv=(r[0],r[1]);need(rv in versions,'read version absent');p=versions[rv]
            need(identity(r[2]) in ids and ids[identity(r[2])]==p,'actual writer')
            same(r,nodes[p]['write'],'read value/version/writer');need(positions[p]<positions[h],'backward audit read')
            parents.append(p);count+=1
        need(len(set(parents))==len(parents),'duplicate read writer');graph[h]=set(parents)
    return graph,nodes,count
def infer_layers(graph):
    children=defaultdict(set);remaining={v:len(ps) for v,ps in graph.items()}
    for v,ps in graph.items():
        for p in ps:need(p in graph,'missing graph parent');children[p].add(v)
    roots={v for v,n in remaining.items() if n==0};queue=deque(roots);height={v:0 for v in roots}
    while queue:
        p=queue.popleft()
        for v in children[p]:
            remaining[v]-=1
            if remaining[v]==0:height[v]=1+max(height[x] for x in graph[v]);queue.append(v)
    need(len(height)==len(graph),'read graph cycle');need(roots and max(height.values())>=1,'no update layer')
    degree={v:sum(height[c]==1 for c in children[v]) for v in roots}
    old={v for v in roots if degree[v]==1};current={v for v in roots if degree[v]>1}
    need(old and current and old|current==roots,'ambiguous seed partition')
    layers=[old,current]+[{v for v,d in height.items() if d==j} for j in range(1,max(height.values())+1)]
    need(all(len(x)==len(old) for x in layers),'incomplete configuration layer')
    return layers,height,degree
def recover(trace,v,m,A):
    graph,nodes,count=authenticate(trace);layers,height,degree=infer_layers(graph);n=len(m)
    need(n==64 and len(A)==n and len(layers)==23 and all(len(x)==n for x in layers),'q5 full layer census')
    ordered=[];vectors=[];version={}
    for i,layer in enumerate(layers):
        site={nodes[h]['write'][0]%n:h for h in layer};need(len(site)==n and set(site)==set(range(n)),'site bijection')
        order=[site[k] for k in range(n)];ordered.append(order)
        vec=[]
        for k,h in enumerate(order):
            w=nodes[h]['write'];resource=w[0]
            need(resource==((i+1)%2)*n+k,'alternating declared buffer/address map')
            expected_version=version.get(resource,0)+1;need(w[1]==expected_version,'sequential immutable versions');version[resource]=expected_version
            vec.append(v.parse(w[3]))
            if i>=2:
                expected={ordered[i-2][k]}|{ordered[i-1][other] for other,_ in A[k]}
                need(graph[h]==expected,'complete adjacent action stencil')
            else:need(not graph[h],'initial roots')
        vectors.append(vec)
    ticks=[];undefined=[]
    for i in range(1,len(vectors)-1):
        older,u,newer=vectors[i-1:i+2];au=v.apply(A,u)
        d=[2*u[k]-older[k]-newer[k] for k in range(n)];E=v.inner(m,u,au)
        need(E.sign()>=0,'positive action energy')
        if E.sign()==0:
            need(all(x.sign()==0 for x in u) and all(x.sign()==0 for x in d),'zero-center full residual')
            undefined.append(i-1);continue
        s=v.inner(m,u,d)/E;need(s.sign()>0,'positive recovered squared duration')
        need(all(d[k]==s*au[k] for k in range(n)),'full centered action residual');ticks.append(s.encode())
    need(not ticks or all(x==ticks[0] for x in ticks),'inconsistent centered tick')
    report={'event_count':len(nodes),'dynamic_read_count':count,
      'height_census':[[j,sum(d==j for d in height.values())] for j in range(max(height.values())+1)],
      'seed_first_update_child_census':[list(x) for x in sorted(Counter(degree.values()).items())],
      'layer_sizes':[len(x) for x in layers],
      'layer_value_sha256':[digest([x.encode() for x in row]) for row in vectors],
      'ordered_layer_event_sha256':[digest(row) for row in ordered],
      'defined_tick_centers':len(ticks),'undefined_center_indices':undefined,
      'recovered_squared_tick_Qphi':ticks[0] if ticks else None,
      'full_centered_residual_zero_at_defined_centers':True,
      'parent_trace_final_hash':trace['final_hash']}
    return vectors,report

require=need
def square_root_bounds(value, p):
    """Independent algebraic binary search, with exact-root endpoint handling."""
    require(value.sign() >= 0, 'nonnegative square')
    left, right = 0, GRID
    while (p.R(F(right, GRID)**2)-value).sign() < 0:
        right *= 2
    while right-left > 1:
        middle = (left+right)//2
        if (p.R(F(middle, GRID)**2)-value).sign() <= 0:
            left = middle
        else:
            right = middle
    if (p.R(F(right, GRID)**2)-value).sign() == 0:
        return [F(right, GRID), F(right, GRID)]
    if (p.R(F(left, GRID)**2)-value).sign() == 0:
        return [F(left, GRID), F(left, GRID)]
    return [F(left, GRID), F(right, GRID)]


def string_tree(x):
    if type(x) is F:
        return str(x)
    if type(x) is list:
        return [string_tree(v) for v in x]
    if type(x) is dict:
        return {k: string_tree(v) for k, v in x.items()}
    return x



def expected_row(p, mass, A, triple, name, step):
    old, center, after = triple
    x = [c-o for c, o in zip(center, old)]
    y = p.apply(A, center)
    z = [a-c for a, c in zip(after, center)]
    dot = lambda u, v: sum((m*a*b for m, a, b in zip(mass, u, v)), p.R())
    xx, xy, yy = dot(x, x), dot(x, y), dot(y, y)
    determinant = xx*yy-xy*xy
    require(determinant.sign() > 0, 'actual positive Gram determinant')
    alpha = (yy*dot(x, z)-xy*dot(y, z))/determinant
    beta = (xx*dot(y, z)-xy*dot(x, z))/determinant
    require(alpha == p.R(1) and beta == p.R(F(-1, 245)), 'actual coefficients')
    require(all((zi-alpha*xi-beta*yi).sign() == 0 for xi, yi, zi in zip(x, y, z)),
            'actual full vector equation')
    # Exact algebraic comparisons handle both grid roots and irrational roots.
    la = square_root_bounds(yy/determinant, p)[1]
    lb = square_root_bounds(xx/determinant, p)[1]
    epsilon = F(1, 10**8)
    q = epsilon*(2*la+614*lb)
    require(q < 1, 'rank/conditioning margin')
    budget = epsilon*F(1594, 245)/(1-q)
    da, db = la*budget, lb*budget
    alo, ahi, blo, bhi = 1-da, 1+da, F(1, 245)-db, F(1, 245)+db
    require(alo > 0 and blo > 0, 'strict duration signs')
    previous2 = [2*blo/(ahi*ahi+ahi), 2*bhi/(alo*alo+alo)]
    next2 = [2*blo/(1+1/alo), 2*bhi/(1+1/ahi)]
    row = {'trace': name, 'center_step': step, 'gram_Qphi': [xx.encode(), xy.encode(), yy.encode()],
           'gram_determinant_Qphi': determinant.encode(), 'left_inverse_row_norm_upper': [la, lb],
           'q': q, 'alpha_radius': da, 'beta_radius': db,
           'alpha_interval': [alo, ahi], 'negative_beta_interval': [blo, bhi],
           'previous_squared_duration_interval': previous2, 'next_squared_duration_interval': next2,
           'previous_duration_interval': [square_root_bounds(p.R(previous2[0]), p)[0],
                                          square_root_bounds(p.R(previous2[1]), p)[1]],
           'next_duration_interval': [square_root_bounds(p.R(next2[0]), p)[0],
                                      square_root_bounds(p.R(next2[1]), p)[1]]}
    row.update({'gram_determinant_interval':list(map(str,p.value_bounds(determinant))),
                'alpha_Qphi':alpha.encode(),'beta_Qphi':beta.encode(),
                'previous_squared_duration_Qphi':(-2*beta/(alpha*(alpha+1))).encode(),
                'next_squared_duration_Qphi':(-2*alpha*beta/(alpha+1)).encode()})
    return row


def verify_arithmetic(packet, v, parent, root=RER):
    """Internal replay; public verify additionally runs the full parent proof."""
    need(type(packet) is dict, 'clock receipt object')
    mass,A,*_=v.model(root);reports={};records=[];schedules={}
    for name,trace in parent['traces'].items():
        vectors,reports[name]=recover(trace,v,mass,A)
        same([[x.encode() for x in row] for row in vectors],trace['layers'],'actual decoded layer join')
        if not name.endswith('intervention'):
            need(all(x.sign()==0 for row in vectors for x in row),'zero baseline lacks clock rank')
            continue
        rows=[expected_row(v,mass,A,vectors[j:j+3],name,j) for j in range(1,21)]
        records.extend(rows);edges=[]
        for edge in range(21):
            intervals=[]
            if edge>0:intervals.append(rows[edge-1]['next_duration_interval'])
            if edge<20:intervals.append(rows[edge]['previous_duration_interval'])
            lo=max(x[0] for x in intervals);hi=min(x[1] for x in intervals)
            need(0<lo<=hi,'shared positive edge interval')
            need((v.R(lo)-v.TAU).sign()<=0 and (v.R(hi)-v.TAU).sign()>=0,'exact nominal inhabitant')
            edges.append([lo,hi])
        elapsed=[[F(0),F(0)]]+[[sum(x[0] for x in edges[:j]),sum(x[1] for x in edges[:j])]
                               for j in range(1,22)]
        schedules[name]={'edge_duration_intervals':edges,'elapsed_time_intervals':elapsed}
    need(schedules['ascending_intervention']==schedules['descending_intervention'],'schedules have same readout')
    final=schedules['ascending_intervention']['elapsed_time_intervals'][-1]
    lower=min(F(r['gram_determinant_interval'][0]) for r in records)
    scope={'inference_reads_stored_step_time_schedule_or_container_position':False,
      'authenticated_read_edges_define_graph':True,'audit_ledger_edges_are_field_edges':False,
      'initial_seed_layers_causally_ordered':False,'complete_parent_history_required':True,
      'resource_to_site_adapter_supplied':True,'action_mass_quadrature_orientation_and_relative_scale_supplied':True,
      'one_duration_per_whole_configuration_layer':True,'arbitrary_site_dependent_lapse':False,
      'candidate_duration_uniformity_assumed':False,'hypothetical_configuration_noise_budget':True,
      'hidden_full_configuration_stationarity_required':True,'noisy_history_existence_certified':False,
      'interval_overlap_implies_history_existence':False,'increment_residual_is_unscaled_EL_residual':False,
      'physical_or_regional_time_slice_claim':False,'causal_count_clock_identified':False,
      'source_native_law_selected':False,'graph_reconstruction_formalized_in_Lean':False}
    expected={'schema':'oph.source-scalar-clock.v1',
      'parent':{'path':PARENT,'sha256':PARENT_SHA,'source_commit':PARENT_COMMIT},
      'traces':reports,
      'exact_duration':{'positive_tick_Qphi':['-1/35','2/35'],'squared_tick':'1/245',
        'identified_edges':21,'positive_gram_cases':40,'common_gram_lower':str(lower),
        'full_vector_decompositions':True,'shared_edge_equality':True,'baseline_identifies_duration':False},
      'stability':{'budget':{'configuration_M_norm':'1/100000000','operator_norm_upper':'614','increment_residual_norm':'0'},
        'records':records,'schedules':schedules,
        'summary':{'maximum_q':max(r['q'] for r in records),
          'maximum_alpha_radius':max(r['alpha_radius'] for r in records),
          'maximum_beta_radius':max(r['beta_radius'] for r in records),
          'final_elapsed_interval':final,'final_elapsed_width':final[1]-final[0]}},
      'scope':scope,'source_pins':{f:sha256((root/f).read_bytes()).hexdigest() for f in FILES}}
    same(packet,string_tree(expected),'independent canonical clock reconstruction')
    return {'verdict':'PASS','full_parent_mathematical_replay':False,
      'events_authenticated':sum(r['event_count'] for r in reports.values()),
      'dynamic_reads_authenticated':sum(r['dynamic_read_count'] for r in reports.values()),
      'layers_per_trace':23,'traces':4,'positive_gram_cases':40,'identified_edges':21,
      'physical_or_regional_time_slice_claim':False,
      'final_elapsed_interval':string_tree(final),'final_elapsed_width':str(final[1]-final[0])}


def verify(packet, root=RER):
    v,parent=context(root)
    need(v.verify(parent,root=root)['verdict']=='PASS','fresh independent full parent proof')
    report=verify_arithmetic(packet,v,parent,root)
    need(sha256((root/PARENT).read_bytes()).hexdigest()==PARENT_SHA,'final immutable parent identity')
    report['full_parent_mathematical_replay']=True
    return report


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('path',nargs='?',type=Path,default=OUTPUT)
    ap.add_argument('--root',type=Path,default=RER);args=ap.parse_args()
    print(json.dumps(verify(load(args.path),root=args.root),indent=2,sort_keys=True))

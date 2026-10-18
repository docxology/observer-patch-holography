"""Independent exact-interval adapter for externally captured Maxwell episodes.

No producer is imported. A parent proof is freshly checked on every call.
Operator-pinned files attest identities relative to explicitly supplied trust;
they cannot prove physical truth or identify encoded potentials with nature.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re
import types

ROOT = Path(__file__).resolve().parents[2]
PARENT = "code/electromagnetism/runtime/serial_maxwell_readout_receipt.json"
PARENT_SHA = "ed20c921d8e03b73acd85a24c9a3abc76f29c642c51dbee53642704a86134f6d"
PARENT_VERIFIER = "code/electromagnetism/verify_serial_maxwell_readout.py"
PARENT_VERIFIER_SHA = "5432264f6d20fafaa186f546376ac9b9347300d8626bcc4a5d246f8fb83b5325"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def closed(value, keys, name):
    need(type(value) is dict and set(value) == set(keys.split()), name + " keys")


def rational(value):
    need(type(value) is str and len(value) <= 200, "bounded rational string required")
    try:
        result = Q(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError("rational string required") from error
    need(str(result) == value, "canonical rational string required")
    return result


def digest(value):
    need(type(value) is str and re.fullmatch(r"[0-9a-f]{64}", value) is not None,
         "SHA-256 required")
    return value


def name(value):
    need(type(value) is str and 0 < len(value) <= 200 and value.strip() == value,
         "nonempty identity required")
    return value


def utc(value):
    need(type(value) is str and value.endswith("Z"), "UTC timestamp required")
    try:
        result = datetime.fromisoformat(value[:-1] + "+00:00")
    except ValueError as error:
        raise ValueError("invalid UTC timestamp") from error
    need(result.tzinfo == timezone.utc, "UTC timestamp required")
    return result


def strict_json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, "duplicate JSON key")
            result[key] = value
        return result
    def invalid(_):
        raise ValueError("floating point and nonfinite JSON are forbidden")
    return json.loads(raw.decode("utf-8"), object_pairs_hook=pairs,
                      parse_float=invalid, parse_constant=invalid)


def pinned(path, expected):
    raw = Path(path).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == digest(expected), "operator file pin mismatch")
    return strict_json(raw)


class Interval:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo, self.hi = Q(lo), Q(lo if hi is None else hi)
        need(self.lo <= self.hi, "reversed interval")

    @classmethod
    def parse(cls, pair):
        need(type(pair) is list and len(pair) == 2, "interval endpoint pair required")
        return cls(*map(rational, pair))

    @staticmethod
    def cast(x):
        return x if isinstance(x, Interval) else Interval(x)

    def __add__(self, x):
        x = self.cast(x)
        return Interval(self.lo+x.lo, self.hi+x.hi)
    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, x):
        return self+-self.cast(x)

    def __rsub__(self, x):
        return self.cast(x)+-self

    def __mul__(self, x):
        x = self.cast(x)
        corners = [a*b for a in (self.lo, self.hi) for b in (x.lo, x.hi)]
        return Interval(min(corners), max(corners))
    __rmul__ = __mul__

    def square(self):
        return Interval(0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2),
                        max(self.lo**2, self.hi**2))

    def contains(self, value):
        return self.lo <= Q(value) <= self.hi

    @property
    def width(self):
        return self.hi-self.lo

    def json(self):
        return [str(self.lo), str(self.hi)]


def fresh_parent():
    packet = pinned(ROOT/PARENT, PARENT_SHA)
    source = (ROOT/PARENT_VERIFIER).read_bytes()
    need(hashlib.sha256(source).hexdigest() == PARENT_VERIFIER_SHA,
         "immutable parent verifier changed")
    # Execute newly read code, rather than an import or a prior verdict cache.
    module = types.ModuleType("fresh_serial_maxwell_measurement_parent")
    module.__file__ = str(ROOT/PARENT_VERIFIER)
    exec(compile(source, module.__file__, "exec"), module.__dict__)
    module.verify(packet)
    edges, gradient, curl = module.carrier()
    return packet, edges, gradient, curl


def validate_prereg(p, edges):
    closed(p, "schema status study_id run_id capture_kind preregistered_utc parent adapter_sources apparatus execution channels clock limits controls decision physical_completion_claim", "preregistration")
    need(p["schema"] == "oph.maxwell_measurement.preregistration.v1" and p["status"] == "FROZEN",
         "a separately frozen preregistration is required")
    name(p["study_id"]); name(p["run_id"])
    need(p["capture_kind"] in ("synthetic", "hardware_emulator"), "capture kind")
    freeze = utc(p["preregistered_utc"])
    need(p["parent"] == {"path": PARENT, "sha256": PARENT_SHA}, "parent identity")
    sources = {"code/maxwell_measurement/" + file for file in
               ("contract.py", "verify.py", "test_measurement.py")}
    need(type(p["adapter_sources"]) is dict and set(p["adapter_sources"]) == sources,
         "adapter implementation identity census")
    for path in sources:
        need(hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest(p["adapter_sources"][path]),
             "frozen adapter implementation changed")
    need(p["execution"] == {
        "gauge_order": [False, True], "events_per_execution": 585,
        "state_coordinates": 42, "slices": 3, "probes_per_slice": 60,
        "feedback_cycles_per_execution": 180, "held_out_slice": 2,
        "model_action_step": "1/2", "calibration_source": "external references only; no episode samples",
        "record_order_is_physical_causal_order": False}, "fixed execution/held-out contract")
    # Canonical serialization distinguishes bools from integer counts.
    need(all(type(p["execution"][k]) is int for k in (
        "events_per_execution", "state_coordinates", "slices", "probes_per_slice",
        "feedback_cycles_per_execution", "held_out_slice")), "integer execution metadata")
    need(p["execution"]["gauge_order"] == [False, True] and
         all(type(x) is bool for x in p["execution"]["gauge_order"]), "typed gauge order")
    need(p["execution"]["record_order_is_physical_causal_order"] is False,
         "record order does not attest physical causal order")
    a = p["apparatus"]
    closed(a, "device_id firmware_sha256 claimant_organization interpretation physical_electromagnetic_field_claim", "apparatus")
    name(a["device_id"]); name(a["claimant_organization"]); digest(a["firmware_sha256"])
    need(a["interpretation"] == "hardware encoding of supplied model potentials" and
         a["physical_electromagnetic_field_claim"] is False and p["physical_completion_claim"] is False,
         "emulator interpretation boundary")
    need(p["decision"] == "complete interval conformance with held-out slice and gauge controls",
         "closed decision rule")
    need(p["controls"] == ["sham_no_probe", "pair_mean", "feedback_disabled"], "control population")
    closed(p["limits"], "maximum_coordinate_width maximum_field_width maximum_action_width maximum_tick_error maximum_clock_relative_width minimum_control_separation", "limits")
    limits = {k: rational(v) for k, v in p["limits"].items()}
    ceilings = {"maximum_coordinate_width": Q(1,1000), "maximum_field_width": Q(1,20),
                "maximum_action_width": Q(1,2), "maximum_tick_error": Q(1,1000),
                "maximum_clock_relative_width": Q(1,1000)}
    need(all(0 < limits[k] <= v for k,v in ceilings.items()), "nonvacuous uncertainty ceilings")
    need(Q(1,4) <= limits["minimum_control_separation"] < Q(1,2), "resolved control threshold")
    need(type(p["channels"]) is list and len(p["channels"]) == 42, "42 calibration channels")
    channels, ids = {}, set()
    for k, ch in enumerate(p["channels"]):
        closed(ch, "channel coordinate quantity oriented_ports orientation raw_unit model_unit calibration", "channel")
        need(ch["channel"] == f"slot{k}" and type(ch["coordinate"]) is int and ch["coordinate"] == k,
             "ordered coordinate/channel map")
        need(type(ch["orientation"]) is int and ch["orientation"] in (-1,1), "signed orientation")
        ports = [k] if k < 12 else list(edges[k-12])
        if k >= 12 and ch["orientation"] == -1:
            ports.reverse()
        need(ch["oriented_ports"] == ports and all(type(x) is int for x in ch["oriented_ports"]),
             "physical port orientation")
        need(ch["quantity"] == ("node_potential" if k < 12 else "edge_potential") and
             ch["model_unit"] == "dimensionless_model_potential", "quantity and model units")
        need(ch["raw_unit"] in ("raw_count", "V"), "declared raw measurement unit")
        cal = ch["calibration"]
        closed(cal, "id gain offset raw_error reference_sha256 reference_samples", "calibration")
        need(name(cal["id"]) not in ids, "unique calibration identities")
        ids.add(cal["id"]); digest(cal["reference_sha256"])
        gain, offset = Interval.parse(cal["gain"]), Interval.parse(cal["offset"])
        need(gain.lo > 0 if ch["orientation"] == 1 else gain.hi < 0,
             "gain sign must agree with orientation")
        error = rational(cal["raw_error"])
        need(error >= 0, "nonnegative raw uncertainty")
        refs = cal["reference_samples"]
        need(type(refs) is list and 2 <= len(refs) <= 100, "calibration reference population")
        raw_values, model_values = set(), set()
        for ref in refs:
            closed(ref, "id raw model_value captured_utc source", "calibration reference")
            name(ref["id"])
            need(ref["source"] == "external_reference" and utc(ref["captured_utc"]) < freeze,
                 "no held-out/episode data in calibration")
            raw, model = rational(ref["raw"]), rational(ref["model_value"])
            raw_values.add(raw); model_values.add(model)
            interval = gain*Interval(raw-error,raw+error)+offset
            need(interval.contains(model) and interval.width <= limits["maximum_coordinate_width"],
                 "calibration reference consistency/precision")
        need(len(raw_values) >= 2 and len(model_values) >= 2, "distinct calibration references")
        channels[ch["channel"]] = (gain,offset,error)
    clock = p["clock"]
    closed(clock, "orientation raw_unit seconds_per_tick tick_error reference_sha256 model_action_time_equals_device_time", "clock")
    need(type(clock["orientation"]) is int and clock["orientation"] == 1 and
         clock["raw_unit"] == "device_tick" and clock["model_action_time_equals_device_time"] is False,
         "clock orientation and model-time boundary")
    scale = Interval.parse(clock["seconds_per_tick"])
    need(scale.lo > 0, "positive clock calibration")
    need(scale.width <= limits["maximum_clock_relative_width"]*scale.lo,
         "nonvacuous clock calibration")
    tick_error = rational(clock["tick_error"])
    need(0 <= tick_error <= limits["maximum_tick_error"], "clock uncertainty ceiling")
    digest(clock["reference_sha256"])
    return channels, limits, scale, tick_error


def sample_plan(event, edges):
    """Operation-specific sample support; alleged parent arrays do not choose it."""
    op, args = event["op"], event["args"]
    result = []
    def add(role, key, channel, side):
        value = event[side][key]
        if side == "reads":
            value = value["value"]
        result.append((role, f"slot{channel}", rational(value)))
    if op in ("seed", "advance"):
        for k in range(42): add(f"loaded_{k}", f"x/{k}", k, "writes")
    elif op == "baseline":
        n,u = args
        add("input", f"x/{u}", u, "reads")
        add("retained_baseline", f"b/{n}/{u}", u, "writes")
    elif op == "probe":
        _,e,side = args
        u = edges[e][side]
        for tag, part in (("before","reads"),("after","writes")):
            add(tag+"_left",f"x/{u}",u,part)
            add(tag+"_right",f"x/{12+e}",12+e,part)
    elif op == "response":
        n,e,side = args
        u = edges[e][side]
        add("response",f"x/{u}",u,"reads")
        add("retained_response",f"r/{n}/{e}/{side}",u,"writes")
    elif op == "feedback":
        _,e,side = args
        add("restored_left",f"x/{edges[e][side]}",edges[e][side],"writes")
        add("restored_right",f"x/{12+e}",12+e,"writes")
    elif op == "decode":
        for k in range(42): add(f"decoded_{k}",f"d/{args[0]}/{k}",k,"writes")
    return result


def exact_trace(actual, expected):
    # JSON equality alone identifies True with 1 in Python.
    need(json.dumps(actual,sort_keys=True,separators=(",",":")) ==
         json.dumps(expected,sort_keys=True,separators=(",",":")),
         "actual operation/read-set/consumed writer/value trace")


def certify_capture(p, c, parent, edges, gradient, curl, channels, limits, scale, tick_error):
    closed(c, "schema study_id run_id capture_kind device_id firmware_sha256 captured_utc controls executions", "capture")
    need(c["schema"] == "oph.maxwell_measurement.capture.v1", "capture schema")
    for key in ("study_id","run_id","capture_kind"):
        need(c[key] == p[key], "capture/preregistration "+key)
    for key in ("device_id","firmware_sha256"):
        need(c[key] == p["apparatus"][key], "capture apparatus "+key)
    need(utc(c["captured_utc"]) > utc(p["preregistered_utc"]), "capture after preregistration")
    nonces = set()
    previous_tick = None

    def measured(row, role, channel, expected, start, end):
        closed(row, "role channel raw tick nonce", "raw sample")
        need(row["role"] == role and row["channel"] == channel, "complete ordered raw sample support")
        need(name(row["nonce"]) not in nonces, "unique raw capture nonce")
        nonces.add(row["nonce"])
        tick = rational(row["tick"])
        need(start+tick_error < tick < end-tick_error, "raw timestamp in event window")
        value = rational(row["raw"])
        gain,offset,error = channels[channel]
        interval = gain*Interval(value-error,value+error)+offset
        need(interval.width <= limits["maximum_coordinate_width"], "nonvacuous calibrated uncertainty")
        need(interval.contains(expected), "raw measurement/model mismatch")
        return interval, tick

    def window(row):
        nonlocal previous_tick
        a,b = rational(row["start_tick"]),rational(row["end_tick"])
        need(a+2*tick_error < b and (previous_tick is None or previous_tick+2*tick_error < a),
             "strict independent device clock order")
        previous_tick = b
        return a,b

    need(type(c["controls"]) is list and len(c["controls"]) == 3, "complete raw controls")
    for row, label in zip(c["controls"],p["controls"],strict=True):
        closed(row, "name start_tick end_tick samples", "control")
        need(row["name"] == label, "ordered control population")
        start,end = window(row)
        values = [Q(-1,2),Q(3,2)]
        values += values if label == "sham_no_probe" else [Q(1,2),Q(1,2)]
        need(type(row["samples"]) is list and len(row["samples"]) == 4, "control raw population")
        boxes, last = [],start
        for i,(sample,value) in enumerate(zip(row["samples"],values,strict=True)):
            box,tick = measured(sample,("before_left","before_right","after_left","after_right")[i],
                                "slot0" if i%2 == 0 else "slot12",value,start,end)
            need(last+2*tick_error < tick, "ordered control samples")
            last=tick; boxes.append(box)
        if label == "feedback_disabled":
            need((boxes[2]-boxes[0]).lo >= limits["minimum_control_separation"] and
                 (boxes[1]-boxes[3]).lo >= limits["minimum_control_separation"],
                 "disabled-feedback control must resolve failed restoration")
    need(type(c["executions"]) is list and len(c["executions"]) == 2, "two complete gauge executions")
    reports=[]
    for observed,reference in zip(c["executions"],parent["executions"],strict=True):
        closed(observed, "gauge events", "execution")
        need(type(observed["gauge"]) is bool and observed["gauge"] is reference["gauge"], "gauge identity")
        need(type(observed["events"]) is list and len(observed["events"]) == 585, "585 observed events")
        baselines, responses, decoded, decode_ticks = {},{},{},{}
        for row,event in zip(observed["events"],reference["events"],strict=True):
            closed(row, "trace start_tick end_tick samples", "observed event")
            exact_trace(row["trace"],event)
            start,end=window(row)
            required=sample_plan(event,edges)
            need(type(row["samples"]) is list and len(row["samples"]) == len(required), "complete event samples")
            boxes,last={},start
            for sample,(role,channel,value) in zip(row["samples"],required,strict=True):
                box,tick=measured(sample,role,channel,value,start,end)
                need(last+2*tick_error < tick, "ordered raw sample timestamps")
                last=tick; boxes[role]=box
            op,args=event["op"],event["args"]
            if op == "baseline": baselines[tuple(args)]=boxes["retained_baseline"]
            elif op == "response": responses[tuple(args)]=boxes["retained_response"]
            elif op == "decode":
                n=args[0]
                values=[baselines[n,u] for u in range(12)]
                for e,(left,right) in enumerate(edges):
                    first=2*responses[n,e,0]-baselines[n,left]
                    second=2*responses[n,e,1]-baselines[n,right]
                    need((first-second).contains(0), "two endpoint decodes disagree")
                    # Retain the full first decode interval, not a post-hoc narrowed intersection.
                    values.append(first)
                for k,value in enumerate(values):
                    need(value.width <= 3*limits["maximum_coordinate_width"] and
                         (value-boxes[f"decoded_{k}"]).contains(0), "public decode vs raw response")
                decoded[n]=values; decode_ticks[n]=Interval(start-tick_error,end+tick_error)
        need(set(decoded) == {0,1,2}, "complete 42-coordinate slices")
        phi=[decoded[n][:12] for n in range(3)]
        potential=[decoded[n][12:] for n in range(3)]
        def mv(matrix,vector):
            return [sum((int(matrix[i,j])*v for j,v in enumerate(vector)),Interval(0))
                    for i in range(matrix.rows)]
        electric=[[-2*(potential[n+1][e]-potential[n][e])-(phi[n][right]-phi[n][left])
                   for e,(left,right) in enumerate(edges)] for n in range(2)]
        magnetic=[mv(curl,potential[n]) for n in range(3)]
        need(all(v.width <= limits["maximum_field_width"] for row in electric+magnetic for v in row),
             "nonvacuous field uncertainty")
        sources=reference["events"][1]["writes"]
        charge=[[Q(sources[f"rho/{n}/{u}"]) for u in range(12)] for n in range(2)]
        current=[[Q(sources[f"J/{n}/{e}"]) for e in range(30)] for n in range(2)]
        residuals=[]
        for n in range(2):
            residuals += [v-r for v,r in zip(mv(gradient.T,electric[n]),charge[n],strict=True)]
            residuals += [magnetic[n+1][f]-magnetic[n][f]+Q(1,2)*v
                          for f,v in enumerate(mv(curl,electric[n]))]
        residuals += [electric[1][e]-electric[0][e]-Q(1,2)*(v-current[0][e])
                      for e,v in enumerate(mv(curl.T,magnetic[1]))]
        need(all(v.contains(0) for v in residuals), "measured Maxwell residuals")
        action=Interval(0)
        for n in range(2):
            action += Q(1,2)*(sum((v.square() for v in electric[n]),Interval(0))*Q(1,2)
                       -sum((v.square() for v in magnetic[n+1]),Interval(0))*Q(1,2)
                       +sum((j*a for j,a in zip(current[n],potential[n+1],strict=True)),Interval(0))
                       +sum((r*v for r,v in zip(charge[n],phi[n],strict=True)),Interval(0)))
        expected_action=Q(reference["events"][-1]["writes"]["field_source_action"])
        need(action.contains(expected_action) and action.width <= limits["maximum_action_width"],
             "field/source action conformance and uncertainty")
        reports.append({"gauge":reference["gauge"],"decoded_slices":[[v.json() for v in decoded[n]] for n in range(3)],
                        "electric":[[v.json() for v in row] for row in electric],
                        "magnetic":[[v.json() for v in row] for row in magnetic],
                        "field_source_action":action.json(),
                        "device_decode_durations_seconds":[((decode_ticks[n+1]-decode_ticks[n])*scale).json()
                                                           for n in range(2)]})
    for field in ("electric","magnetic"):
        for left,right in zip(reports[0][field],reports[1][field],strict=True):
            for x,y in zip(left,right,strict=True):
                need((Interval.parse(x)-Interval.parse(y)).contains(0), "gauge-invariant measured field")
    need((Interval.parse(reports[0]["field_source_action"])-Interval.parse(reports[1]["field_source_action"])).contains(0),
         "gauge-invariant measured field/source action")
    return reports,len(nonces)


def attest(trust,p,c,prereg_hash,capture_hash):
    closed(trust, "schema study_id run_id preregistration_sha256 capture_sha256 device_id firmware_sha256 preregistered_utc captured_utc operator_identity independent_witness_identity scope", "external attestation")
    need(trust["schema"] == "oph.maxwell_measurement.operator_attestation.v1", "attestation schema")
    for key in ("study_id","run_id","preregistered_utc"):
        need(trust[key] == p[key], "attested preregistration identity")
    for key in ("device_id","firmware_sha256","captured_utc"):
        need(trust[key] == c[key], "attested capture identity")
    need(trust["preregistration_sha256"] == prereg_hash and trust["capture_sha256"] == capture_hash,
         "attested external content pins")
    operator=name(trust["operator_identity"]); witness=name(trust["independent_witness_identity"])
    need(operator != witness, "distinct operator and independent witness identities")
    expected={key: True for key in ("physical_device_and_raw_capture_witnessed",
        "actual_read_write_consumption_witnessed", "complete_run_and_control_population",
        "firmware_and_device_identity_checked", "calibration_references_checked",
        "calibration_independent_of_episode_and_heldout_data", "preregistration_precedes_capture",
        "clock_reference_and_capture_timestamps_checked")}
    need(trust["scope"] == expected and all(type(x) is bool for x in trust["scope"].values()),
         "complete external witnessed scope")


def verify(prereg_path, capture_path, prereg_hash, capture_hash, trust_path=None, trust_hash=None):
    p,c=pinned(prereg_path,prereg_hash),pinned(capture_path,capture_hash)
    parent,edges,gradient,curl=fresh_parent()
    channels,limits,scale,tick_error=validate_prereg(p,edges)
    reports,count=certify_capture(p,c,parent,edges,gradient,curl,channels,limits,scale,tick_error)
    need((trust_path is None) == (trust_hash is None), "both operator trust file and pin are required")
    external=False
    if trust_path is not None:
        need(p["capture_kind"] != "synthetic", "synthetic data cannot acquire physical attestation")
        attest(pinned(trust_path,trust_hash),p,c,prereg_hash,capture_hash)
        external=True
    verdict=("SYNTHETIC_CONFORMANCE_ONLY" if p["capture_kind"] == "synthetic" else
             "CAPTURE_CONFORMS_RELATIVE_TO_OPERATOR_ATTESTATION" if external else "CAPTURE_CONFORMS_UNATTESTED")
    return {"schema":"oph.maxwell_measurement.adapter_result.v1","verdict":verdict,
            "preregistration_sha256":prereg_hash,"capture_sha256":capture_hash,
            "parent_sha256":PARENT_SHA,"fresh_parent_verification":True,
            "raw_samples":count,"executions":reports,"held_out_slice":2,
            "measurement_evidence_eligible_relative_to_operator":external,
            "physical_truth_certified":False,"complete_physical_episode_certified":False,
            "model_action_time_calibrated":False,"natural_electromagnetism_identified":False,
            "independent_physical_source_current_measured":False,
            "physical_signal_causal_order_certified":False,
            "calibration_independent_ratio_claimed":False}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preregistration",required=True,type=Path)
    parser.add_argument("--capture",required=True,type=Path)
    parser.add_argument("--preregistration-sha256",required=True)
    parser.add_argument("--capture-sha256",required=True)
    parser.add_argument("--operator-attestation",type=Path)
    parser.add_argument("--operator-attestation-sha256")
    args=parser.parse_args()
    try:
        result=verify(args.preregistration,args.capture,args.preregistration_sha256,args.capture_sha256,
                      args.operator_attestation,args.operator_attestation_sha256)
    except (ValueError,KeyError,TypeError,OSError,ZeroDivisionError) as error:
        print(json.dumps({"verdict":"INVALID","reason":str(error)}))
        raise SystemExit(2)
    print(json.dumps(result,sort_keys=True))
    if result["verdict"] == "CAPTURE_CONFORMS_UNATTESTED":
        raise SystemExit(1)


if __name__ == "__main__":
    main()

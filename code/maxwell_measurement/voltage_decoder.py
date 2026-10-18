"""Fixed-alphabet interval decoder for a proposed voltage Maxwell emulator.

The alphabet comes from the immutable finite program, before measurements.
An interval must contain exactly one symbol and pass the fixed precision
bound. Nearest-reference snapping is never performed. This module neither
authenticates raw captures nor changes the frozen measurement adapter.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PARENT = "code/electromagnetism/runtime/serial_maxwell_readout_receipt.json"
PARENT_SHA = "ed20c921d8e03b73acd85a24c9a3abc76f29c642c51dbee53642704a86134f6d"
HERE = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def rational(value):
    need(type(value) is str and len(value) <= 200, "bounded rational string required")
    try:
        result = Q(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError("invalid rational") from error
    need(str(result) == value, "canonical rational required")
    return result


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)+"\n").encode()


def strict_json(raw):
    def pairs(items):
        result = {}
        for k,v in items:
            need(k not in result, "duplicate JSON key")
            result[k] = v
        return result
    def reject(_):
        raise ValueError("JSON floating values are forbidden")
    return json.loads(raw.decode("utf-8"), object_pairs_hook=pairs,
                      parse_float=reject, parse_constant=reject)


def codebook():
    raw = (ROOT/PARENT).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == PARENT_SHA, "immutable parent identity")
    parent = strict_json(raw)
    symbols = {rational(value)
               for run in parent["executions"] for event in run["events"]
               for key,value in event["writes"].items()
               if key.split("/")[0] in {"x", "b", "r", "d"}}
    need(len(symbols) == 120, "complete parent state/record alphabet")
    symbols.update((Q(-1,2),Q(1,2),Q(3,2)))
    ordered = sorted(symbols)
    gap = min(b-a for a,b in zip(ordered,ordered[1:]))
    need(len(ordered) == 123 and gap == Q(23,42896), "fixed control alphabet and separation")
    need(2*Q(1,10000) < gap, "disjoint admitted decoding bands")
    return {
        "schema": "oph.maxwell_measurement.voltage_codebook.v1",
        "parent": {"path":PARENT,"sha256":PARENT_SHA},
        "source_pins": {"code/maxwell_measurement/"+file:
                        hashlib.sha256((HERE/file).read_bytes()).hexdigest()
                        for file in ("voltage_decoder.py","test_voltage_decoder.py")},
        "symbols": list(map(str,ordered)), "symbol_count":123,
        "construction": "all parent x/b/r/d writes plus the three declared control potentials",
        "uses_measured_validation_data":False,
        "minimum_model_separation":str(gap),
        "maximum_interval_width":"1/5000",
        "maximum_endpoint_distance_from_symbol":"1/10000",
        "nominal_encoding":{"volts_offset":"5/2","volts_per_model_unit":"1/2"},
        "rule":"exactly one contained symbol; reject empty, ambiguous, wide or inconsistent intervals",
        "experiment_preregistered":False,
        "physical_calibration_proved":False,
    }


def verify_codebook(received):
    # Canonical comparison distinguishes integer/bool substitutions recursively.
    need(canonical(received) == canonical(codebook()), "changed frozen interface codebook")


def decode_interval(lower, upper, received, expected=None):
    verify_codebook(received)
    lo,hi = rational(lower),rational(upper)
    need(lo <= hi, "reversed measurement interval")
    contained = [rational(x) for x in received["symbols"] if lo <= rational(x) <= hi]
    need(contained, "no alphabet symbol in measured interval; snapping forbidden")
    need(len(contained) == 1, "ambiguous measured interval")
    symbol = contained[0]
    need(hi-lo <= rational(received["maximum_interval_width"]), "measurement interval too wide")
    radius = rational(received["maximum_endpoint_distance_from_symbol"])
    need(max(symbol-lo,hi-symbol) <= radius, "measurement interval exceeds declared code margin")
    if expected is not None:
        target = rational(expected)
        need(target in map(rational,received["symbols"]), "expected value outside interface alphabet")
        need(symbol == target, "measured symbol disagrees with independently predicted value")
    return {"schema":"oph.maxwell_measurement.voltage_decode.v1",
            "symbol":str(symbol),"measured_model_interval":[lower,upper],
            "interval_contains_symbol":True,"nearest_reference_snapping":False,
            "expected_value_checked":expected is not None,
            "codebook_sha256":hashlib.sha256(canonical(received)).hexdigest(),
            "physical_capture_authenticated":False,"measurement_verdict":False}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest="operation",required=True)
    draft=sub.add_parser("prepare-codebook")
    draft.add_argument("--output",required=True,type=Path)
    decode=sub.add_parser("decode")
    decode.add_argument("--codebook",required=True,type=Path)
    decode.add_argument("--codebook-sha256",required=True)
    decode.add_argument("--lower",required=True)
    decode.add_argument("--upper",required=True)
    decode.add_argument("--expected")
    args=parser.parse_args()
    try:
        if args.operation == "prepare-codebook":
            need(not args.output.exists(), "refusing to overwrite existing interface")
            raw=canonical(codebook())
            args.output.parent.mkdir(parents=True,exist_ok=True)
            args.output.write_bytes(raw)
            print(json.dumps({"path":str(args.output),"sha256":hashlib.sha256(raw).hexdigest(),
                              "experiment_preregistered":False}))
        else:
            raw=args.codebook.read_bytes()
            need(hashlib.sha256(raw).hexdigest() == args.codebook_sha256, "external codebook pin mismatch")
            received=strict_json(raw)
            need(raw == canonical(received), "canonical codebook bytes required")
            print(json.dumps(decode_interval(args.lower,args.upper,received,args.expected),sort_keys=True))
    except (ValueError,OSError,TypeError,KeyError) as error:
        print(json.dumps({"verdict":"REJECTED","reason":str(error)}))
        raise SystemExit(2)


if __name__ == "__main__":
    main()

"""Independent exact checkpoint-error consumer; never imports its producer.

The immutable interval certificate is freshly replayed by its independent
Picard/Taylor checker, including the canonical-to-original q/v conversion.
The independent event checker reconstructs register writes and ancestry.
Every exported difference and sum is then checked with rational arithmetic.
No numerical trajectory is generated and no floating diagnostic is a bound.
"""
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import types

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUTPUT = HERE / "runtime/whitney_charged_checkpoint_receipt.json"
PREFIX = "code/electromagnetism/"
PIN_PATHS = tuple(PREFIX + name for name in (
    "whitney_charged_checkpoint.py", "verify_whitney_charged_checkpoint.py",
    "test_whitney_charged_checkpoint.py"))
PARENTS = {'enclosure': {'path': 'code/electromagnetism/runtime/whitney_charged_enclosure_receipt.json',
               'sha256': '509fce37d0df6a3fdd2044c1897415162afb5a541ed2d4ec615731a0d99763c9',
               'bytes': 969123},
 'instrument': {'path': 'code/electromagnetism/runtime/whitney_charged_instrument_receipt.json',
                'sha256': '4b7060b48ea3611011b863641a3d706a9496bdc1b0fb81dbf10fe7a84ca3490c',
                'bytes': 2232669},
 'historical': {'path': 'code/electromagnetism/runtime/whitney_charged_dynamics_receipt.json',
                'sha256': '6062233dc4707ea0b1c6f8eec4b6a474998224f74a417b6fe2dd9faf46fb5264',
                'bytes': 946241}}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def exact(actual, expected, message):
    require(type(actual) is type(expected), message + " type")
    if type(expected) is dict:
        require(actual.keys() == expected.keys(), message + " fields")
        for key in expected:
            exact(actual[key], expected[key], message + "/" + key)
    elif type(expected) is list:
        require(len(actual) == len(expected), message + " length")
        for a, b in zip(actual, expected):
            exact(a, b, message)
    else:
        require(actual == expected, message)


def pairs(items):
    out = {}
    for key, value in items:
        require(key not in out, "duplicate JSON key")
        out[key] = value
    return out


def forbidden(token):
    raise ValueError("floating or nonfinite JSON token")


def load(path=OUTPUT):
    raw = Path(path).read_bytes()
    require(len(raw) <= 200000, "checkpoint receipt size")
    return json.loads(raw.decode("utf-8"), object_pairs_hook=pairs,
                      parse_float=forbidden, parse_constant=forbidden)


def rational(value):
    require(type(value) is str and len(value) <= 200, "canonical rational string required")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError("invalid rational") from error
    require(str(result) == value, "noncanonical rational")
    return result


def fresh(relative_path, source_bytes):
    """Execute the exact checked bytes, without import/pyc caches."""
    module = types.ModuleType("independent_checkpoint_" + Path(relative_path).stem)
    module.__file__ = str(ROOT / relative_path)
    exec(compile(source_bytes, str(ROOT / relative_path), "exec"), module.__dict__)
    return module


def parent_inputs():
    packets, source_bytes = {}, {}
    for role, identity in PARENTS.items():
        raw = (ROOT / identity["path"]).read_bytes()
        require(len(raw) == identity["bytes"] and sha256(raw).hexdigest() == identity["sha256"],
                "immutable parent bytes: " + role)
        # Byte identities authenticate these already strict-parsed historical
        # encodings; only the old numerical histories contain JSON floats.
        packets[role] = json.loads(raw.decode("utf-8"), object_pairs_hook=pairs)
        for relative, expected in packets[role]["source_pins"].items():
            raw_source = (ROOT / relative).read_bytes()
            require(sha256(raw_source).hexdigest() == expected, "stale parent source: " + relative)
            source_bytes[relative] = raw_source
    return packets, source_bytes


def expected_contract():
    return {
        "coordinate_order": ["alpha", "Re(center)", "Im(center)", "Re(boundary)",
            "Im(boundary)", "alpha_dot", "Re(center_dot)", "Im(center_dot)",
            "Re(boundary_dot)", "Im(boundary_dot)"],
        "coordinate_frame": "original reduced temporal-gauge q/v; not the nine canonical polynomial coordinates",
        "norm": "maximum absolute coordinate difference",
        "time_grid": {"samples": 81, "step": "1/40", "interval": ["0", "2"]},
        "time_alignment": "exact event action_time j/40; historical float t is nominal-grid metadata",
        "decoded_values": "exact rational writes reconstructed from observer events, not copied frame values",
        "historical_values": "immutable binary64 sample coordinates interpreted as exact dyadics",
        "transfer": "historical IVP error plus exact decoded-to-historical coordinate difference",
        "parent_enclosure_freshly_verified": True, "observer_events_exactly_replayed": True,
        "checkpoint_qv_error_certified": True,
        "intermediate_probe_register_error_certified": False,
        "continuous_observer_error_certified": False, "nonlinear_field_error_certified": False,
        "configuration_clock_error_certified": False, "physical_clock_calibrated": False,
        "physical_observer_placement": False, "external_signature_attestation": False,
        "quantum_history": False, "spatial_continuum_error_certified": False,
    }


def check_rows(rows, decoded, events, historical):
    """Exact coordinate comparison and triangle inequality, with no solver."""
    require(type(rows) is list and len(rows) == len(decoded) == len(historical) == 81,
            "81 aligned checkpoints required")
    base, maximum = Fraction(1, 10**10), Fraction(0)
    for n, (row, d, old) in enumerate(zip(rows, decoded, historical, strict=True)):
        require(type(row) is dict and row.keys() == {
            "sample_index", "nominal_time", "decode_event_id", "decode_event_hash",
            "completed_repair_cycles", "decoded_qv", "absolute_reference_differences",
            "checkpoint_error_upper"}, "checkpoint fields")
        exact(row["sample_index"], n, "sample index")
        exact(row["nominal_time"], str(Fraction(n, 40)), "nominal grid time")
        exact(d["action_time_exact"], row["nominal_time"], "decoded event time")
        exact(d["sample_index"], n, "event sample index")
        event_id = d["decode_event_id"]
        exact(row["decode_event_id"], event_id, "decoded event identity")
        exact(row["decode_event_hash"], events[event_id]["event_hash"], "decoded event hash")
        exact(row["completed_repair_cycles"], 5 * (n + 1), "cycle count")
        exact(d["completed_repair_cycles"], row["completed_repair_cycles"], "event cycles")
        exact(row["decoded_qv"], d["q_exact"] + d["velocity_exact"], "event-derived coordinates")
        require(len(row["decoded_qv"]) == 10, "ten original q/v coordinates")
        refs = old["q_reduced"] + old["v_reduced"]
        require(len(refs) == 10, "historical dimension")
        require(type(old["t"]) is float and abs(Fraction(old["t"]) - Fraction(n, 40)) < Fraction(1, 10**14),
                "historical nominal-time metadata")
        require(type(row["absolute_reference_differences"]) is list and
                len(row["absolute_reference_differences"]) == 10, "component difference census")
        worst = Fraction(0)
        for value, ref, exported in zip(row["decoded_qv"], refs,
                                         row["absolute_reference_differences"], strict=True):
            require(type(ref) is float, "historical binary64 coordinate")
            difference = abs(rational(value) - Fraction.from_float(ref))
            require(rational(exported) == difference, "exact component discrepancy")
            worst = max(worst, difference)
        require(rational(row["checkpoint_error_upper"]) == base + worst,
                "checkpoint triangle inequality")
        maximum = max(maximum, worst)
    return maximum


def verify(receipt):
    require(type(receipt) is dict and receipt.keys() == {
        "schema", "scope", "source_pins", "parents", "contract", "events", "event_root",
        "checkpoints", "bounds"}, "checkpoint receipt schema")
    exact(receipt["schema"], "oph.whitney_charged_checkpoint.v1", "schema")
    exact(receipt["scope"], "CERTIFIED_DECODED_CHARGED_CHECKPOINTS__SUPPLIED_ACTION_TIME", "scope")
    exact(receipt["contract"], expected_contract(), "contract")
    exact(receipt["source_pins"], {p: sha256((ROOT / p).read_bytes()).hexdigest() for p in PIN_PATHS},
          "fresh consumer source pins")
    exact(receipt["parents"], PARENTS, "immutable parent identities")
    packets, sources = parent_inputs()
    instrument_path = PREFIX + "verify_whitney_charged_instrument.py"
    instrument = fresh(instrument_path, sources[instrument_path])
    history = packets["instrument"]
    instrument.exact(history["contract"], instrument.expected_contract(), "instrument contract")
    decoded, _, event_root = instrument.replay_events(history["events"])
    exact(receipt["events"], 1782, "event census")
    exact(receipt["event_root"], event_root, "replayed commitment")
    exact(history["event_root"], event_root, "instrument commitment")
    require(len(history["frames"]) == len(decoded), "frame census")
    for d, frame in zip(decoded, history["frames"], strict=True):
        exact({key: frame[key] for key in d}, d, "frame ancestry cross-check")
    maximum = check_rows(receipt["checkpoints"], decoded, history["events"],
                         packets["historical"]["samples"])
    base, simple = Fraction(1, 10**10), Fraction(10001, 10**14)
    bound = base + maximum
    exact(receipt["bounds"], {
        "historical_qv_error_upper": str(base),
        "maximum_decoded_reference_difference": str(maximum),
        "decoded_checkpoint_error_upper": str(bound),
        "simple_checkpoint_error_upper": str(simple)}, "exact transferred bounds")
    require(bound <= simple, "simple upper bound")
    # Expensive proof replay happens only after inexpensive mutation checks.
    # Every accepted call executes it afresh; there is no success cache or
    # public option to skip the independent interval proof.
    enclosure_path = PREFIX + "verify_whitney_charged_enclosure.py"
    enclosure = fresh(enclosure_path, sources[enclosure_path])
    proof = enclosure.verify(packets["enclosure"])
    exact(proof["accepted"], True, "fresh interval proof")
    exact(proof["samples"], 81, "certified sample grid")
    exact(proof["historical_position_velocity_error_upper"], str(base), "certified original-coordinate bound")
    exact(proof["whole_time_interval"], True, "whole-window parent")
    return {
        "accepted": True, "scope": receipt["scope"], "events": 1782,
        "decoded_checkpoints": 81, "original_qv_dimension": 10,
        "exact_model_step": "1/40", "model_time_horizon": "2",
        **receipt["bounds"], "checkpoint_qv_error_certified": True,
        "parent_enclosure_freshly_verified": True, "observer_events_exactly_replayed": True,
        "continuous_observer_error_certified": False, "nonlinear_field_error_certified": False,
        "configuration_clock_error_certified": False, "physical_clock_calibrated": False,
        "external_signature_attestation": False, "quantum_history": False,
    }


if __name__ == "__main__":
    print(json.dumps(verify(load()), sort_keys=True))

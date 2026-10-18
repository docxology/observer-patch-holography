"""Transfer the charged IVP certificate to actual decoded observer checkpoints.

For each nominal t=j/40, let h_j be the historical binary64 sample interpreted
as an exact dyadic vector and d_j the exact rational event decode. The parent
interval proof gives ||h_j-y(t)||_infinity <= 1e-10 in the original reduced
position/velocity coordinates. Thus ||d_j-y(t)|| <= ||d_j-h_j|| + 1e-10.
This certifies checkpoints only; probe registers and clock quadratures are
different objects. This producer does not regenerate or relabel either input history. The current
custody successor binds separately qualified v2 software executions; original
histories remain immutable in Git.
"""
from fractions import Fraction as Q
from hashlib import sha256
import argparse
import json
import math
from pathlib import Path
import types

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUTPUT = HERE / "runtime/whitney_charged_checkpoint_receipt.json"
PREFIX = "code/electromagnetism/"
OWN = [PREFIX + name for name in (
    "whitney_charged_checkpoint.py", "verify_whitney_charged_checkpoint.py",
    "test_whitney_charged_checkpoint.py")]
PARENTS = {'enclosure': ('code/electromagnetism/runtime/whitney_charged_enclosure_receipt.json',
               '509fce37d0df6a3fdd2044c1897415162afb5a541ed2d4ec615731a0d99763c9'),
 'instrument': ('code/electromagnetism/runtime/whitney_charged_instrument_receipt.json',
                '4b7060b48ea3611011b863641a3d706a9496bdc1b0fb81dbf10fe7a84ca3490c'),
 'historical': ('code/electromagnetism/runtime/whitney_charged_dynamics_receipt.json',
                '6062233dc4707ea0b1c6f8eec4b6a474998224f74a417b6fe2dd9faf46fb5264')}
COORDINATES = ["alpha", "Re(center)", "Im(center)", "Re(boundary)",
               "Im(boundary)", "alpha_dot", "Re(center_dot)",
               "Im(center_dot)", "Re(boundary_dot)", "Im(boundary_dot)"]


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       allow_nan=False) + "\n").encode("utf-8")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_parents():
    packets, identities, sources = {}, {}, {}
    for role, (path, expected) in PARENTS.items():
        raw = (ROOT / path).read_bytes()
        require(sha256(raw).hexdigest() == expected, "immutable parent: " + role)
        packets[role] = json.loads(raw.decode("utf-8"))
        identities[role] = {"path": path, "sha256": expected, "bytes": len(raw)}
        for source, digest in packets[role]["source_pins"].items():
            data = (ROOT / source).read_bytes()
            require(sha256(data).hexdigest() == digest, "stale parent source: " + source)
            sources[source] = data
    return packets, identities, sources


def fresh(source, data):
    module = types.ModuleType("checkpoint_parent_" + Path(source).stem)
    module.__file__ = str(ROOT / source)
    exec(compile(data, str(ROOT / source), "exec"), module.__dict__)
    return module


def contract():
    return {
        "coordinate_order": COORDINATES,
        "coordinate_frame": "original reduced temporal-gauge q/v; not the nine canonical polynomial coordinates",
        "norm": "maximum absolute coordinate difference",
        "time_grid": {"samples": 81, "step": "1/40", "interval": ["0", "2"]},
        "time_alignment": "exact event action_time j/40; historical float t is nominal-grid metadata",
        "decoded_values": "exact rational writes reconstructed from observer events, not copied frame values",
        "historical_values": "immutable binary64 sample coordinates interpreted as exact dyadics",
        "transfer": "historical IVP error plus exact decoded-to-historical coordinate difference",
        "parent_enclosure_freshly_verified": True,
        "observer_events_exactly_replayed": True,
        "checkpoint_qv_error_certified": True,
        "intermediate_probe_register_error_certified": False,
        "continuous_observer_error_certified": False,
        "nonlinear_field_error_certified": False,
        "configuration_clock_error_certified": False,
        "physical_clock_calibrated": False,
        "physical_observer_placement": False,
        "external_signature_attestation": False,
        "quantum_history": False,
        "spatial_continuum_error_certified": False,
    }


def build():
    packets, identities, sources = read_parents()
    ep = PREFIX + "verify_whitney_charged_enclosure.py"
    enclosure = fresh(ep, sources[ep])
    proof = enclosure.verify(packets["enclosure"])
    require(proof["accepted"] is True, "parent interval proof")
    base = Q(proof["historical_position_velocity_error_upper"])
    require(base == Q(1, 10**10), "historical certified bound")
    ip = PREFIX + "verify_whitney_charged_instrument.py"
    instrument = fresh(ip, sources[ip])
    history = packets["instrument"]
    instrument.exact(history["contract"], instrument.expected_contract(), "instrument contract")
    decoded, _, event_root = instrument.replay_events(history["events"])
    instrument.exact(event_root, history["event_root"], "event commitment")
    rows, worst = [], Q(0)
    for n, (d, frame, old) in enumerate(zip(decoded, history["frames"],
                                              packets["historical"]["samples"], strict=True)):
        instrument.exact({k: frame[k] for k in d}, d, "decoded frame provenance")
        require(Q(d["action_time_exact"]) == Q(n, 40), "exact checkpoint time")
        values = d["q_exact"] + d["velocity_exact"]
        reference = old["q_reduced"] + old["v_reduced"]
        require(len(values) == len(reference) == 10, "coordinate dimension")
        require(all(type(x) in (float, int) and math.isfinite(x) for x in reference),
                "historical dyadic coordinates")
        errors = [abs(Q(x) - Q(y)) for x, y in zip(values, reference, strict=True)]
        difference = max(errors)
        worst = max(worst, difference)
        event_id = d["decode_event_id"]
        rows.append({"sample_index": n, "nominal_time": str(Q(n, 40)),
                     "decode_event_id": event_id,
                     "decode_event_hash": history["events"][event_id]["event_hash"],
                     "completed_repair_cycles": d["completed_repair_cycles"],
                     "decoded_qv": values,
                     "absolute_reference_differences": list(map(str, errors)),
                     "checkpoint_error_upper": str(base + difference)})
    require(len(rows) == 81, "checkpoint census")
    simple = Q(10001, 10**14)
    require(base + worst <= simple, "simple checkpoint bound")
    return {
        "schema": "oph.whitney_charged_checkpoint.v1",
        "scope": "CERTIFIED_DECODED_CHARGED_CHECKPOINTS__SUPPLIED_ACTION_TIME",
        "source_pins": {p: sha256((ROOT / p).read_bytes()).hexdigest() for p in OWN},
        "parents": identities, "contract": contract(),
        "events": len(history["events"]), "event_root": event_root,
        "checkpoints": rows,
        "bounds": {"historical_qv_error_upper": str(base),
                   "maximum_decoded_reference_difference": str(worst),
                   "decoded_checkpoint_error_upper": str(base + worst),
                   "simple_checkpoint_error_upper": str(simple)},
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    packet = build()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(canonical(packet))
    print(json.dumps({"path": str(args.output), "checkpoints": len(packet["checkpoints"]),
                      "bounds": packet["bounds"]}, sort_keys=True))

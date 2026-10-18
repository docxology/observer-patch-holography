"""Independent software-event and full-action replay of charged readbacks.

The instrument producer is never imported. Rational event operations are
reconstructed from their schedule and read versions. Numerical advances use
the existing independent unrestricted-element action, with fresh source pins
and historical-parent verification. Internal hash provenance is not external
attestation, and exact readback is not an interval-certified ODE solution.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
OUTPUT = HERE/"runtime/whitney_charged_instrument_receipt.json"
PARENT = "code/electromagnetism/runtime/whitney_charged_dynamics_receipt.json"
SCOPE = "SELF_READING_COUPLED_CLASSICAL_EXECUTION__COMPUTATIONAL_PATCHES__MODEL_TIME_ONLY"
PINS = {
    "Lean/Screen/SeamCurrentEdge30Moment.lean", "Lean/Screen/SeamCurrentCarrierQuotient.lean",
    "Lean/ObserverPatchHolography/CoreAxioms.lean", "code/electromagnetism/verify_cone_whitney_bridge.py",
    "code/electromagnetism/whitney_charged_dynamics.py", "code/electromagnetism/verify_whitney_charged_dynamics.py", PARENT,
    "paper/tex_fragments/WHITNEY_CHARGED_MATTER.tex", "paper/tex_fragments/WHITNEY_CHARGED_EXECUTION.tex",
    "paper/tex_fragments/WHITNEY_CHARGED_INSTRUMENT.tex",
    "code/electromagnetism/whitney_charged_instrument.py",
    "code/electromagnetism/verify_whitney_charged_instrument.py",
    "code/electromagnetism/test_whitney_charged_instrument.py",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)+"\n").encode("ascii")


def exact(actual, expected, name):
    require(canonical(actual) == canonical(expected), name)


def keys(value, expected, name):
    require(type(value) is dict and set(value) == set(expected), name)


def fraction(value):
    require(type(value) is str, "rational register string required")
    try:
        result = Q(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError("invalid rational register") from error
    require(str(result) == value, "noncanonical rational register")
    return result


def load(path=OUTPUT):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate JSON key")
            result[key] = value
        return result
    def constant(_):
        raise ValueError("nonfinite JSON constant")
    def finite_float(value):
        result = float(value)
        require(np.isfinite(result), "nonfinite JSON number")
        return result
    return json.loads(Path(path).read_text(encoding="utf-8"), object_pairs_hook=pairs,
                      parse_constant=constant, parse_float=finite_float)


def expected_contract():
    return {
        "patch_count": 5, "real_registers_per_patch": 2,
        "patch_coordinates": ["alpha", "Re(center)", "Im(center)", "Re(boundary)", "Im(boundary)"],
        "ports": [[0, 1], [1, 2], [2, 3], [3, 4], [4, 0]],
        "patch_placement": "computational symmetry coordinates; no physical observer placement",
        "state_encoding": "canonical rational strings; numerical states are exact encodings of binary64 values",
        "readback": "pairwise vector averaging, retained local baselines/responses, exact feedback and neighbor decoding",
        "evolution_input": "only initial data and previously decoded state; historical reference samples are comparison-only",
        "authentication": "hash-pinned replayable software event provenance; no external witness or cryptographic identity attestation",
        "classical_coordinate_basis": "alpha,Re(center),Im(center),Re(boundary),Im(boundary); velocity in the same order",
        "field_basis": "same oriented Whitney one-forms and potential-dressed nodal complex scalar on the fixed cone",
        "field_encoding": "complex readouts are [real,imaginary]; classical coefficients are not quantum amplitudes",
        "units": "supplied dimensionless cone and scalar action; no SI calibration",
        "parameters": {"e": "1/4", "m_squared": "1/2", "g": "1/4"},
        "gauge": "temporal phi=0; real unwrapped edge integrals",
        "integrator": {"method": "DOP853", "rtol": 3e-13, "atol": 3e-14, "max_step": "1/80"},
        "sample_count": 81, "action_step": "1/40", "action_interval": ["0", "2"],
        "clock": "completed feedback cycles are operational events; 5 cycles per decoded sweep; 1/40 model-time per solver advance is supplied",
        "observer_software_history": True, "physical_clock_calibrated": False,
        "physical_observer_placement": False, "quantum_state_history": False,
        "spatial_trajectory_convergence": False, "rigorous_trajectory_enclosure": False,
        "empirical_prediction": False,
    }


def replay_events(events):
    require(type(events) is list and len(events) == 1782, "complete event census")
    state, versions, advances, decoded = {}, {}, [], []
    cursor, previous_hash = 0, "0"*64

    def consume(op, args, read_keys, expected_writes=None):
        nonlocal cursor, previous_hash
        event = events[cursor]
        keys(event, {"id", "op", "args", "reads", "parents", "writes", "previous_hash", "event_hash"}, "event schema")
        exact([event["id"], event["op"], event["args"]], [cursor, op, args], "event operation/order")
        keys(event["reads"], set(read_keys), "operation read footprint")
        for key in read_keys:
            require(key in state, "read before write")
            exact(event["reads"][key], {"writer": versions[key], "value": str(state[key])}, "read value/version provenance")
        exact(event["parents"], sorted({versions[key] for key in read_keys}), "event parents")
        exact(event["previous_hash"], previous_hash, "event chain predecessor")
        body = {key: value for key, value in event.items() if key != "event_hash"}
        require(event["event_hash"] == hashlib.sha256(canonical(body)).hexdigest(), "event content hash")
        require(type(event["writes"]) is dict, "operation write footprint")
        writes = {key: fraction(value) for key, value in event["writes"].items()}
        if expected_writes is not None:
            exact(event["writes"], {key: str(value) for key, value in expected_writes.items()}, "operation result")
        state.update(writes)
        versions.update({key: cursor for key in writes})
        previous_hash, cursor = event["event_hash"], cursor+1
        return writes

    initial = np.array([0, 1, 0, 1, 0, .25*(2+3*(1+np.sqrt(5))/2)/10, 0, 3, 0, -1])
    seed = {"action_time": Q(0), "action_step": Q(1, 40), "cycles": Q(0), "e": Q(1, 4), "m_squared": Q(1, 2), "g": Q(1, 4)}
    for i in range(5):
        seed[f"x/{i}/q"], seed[f"x/{i}/v"] = Q(float(initial[i])), Q(float(initial[i+5]))
    consume("initialize", [], [], seed)
    for n in range(81):
        if n:
            read_keys = [f"d/{n-1}/{i}/{part}" for i in range(5) for part in ("q", "v")]
            read_keys += ["action_time", "action_step"]
            incoming = np.array([float(state[f"d/{n-1}/{i}/{part}"]) for part in ("q", "v") for i in range(5)])
            writes = consume("advance", [n], read_keys)
            keys(writes, {"action_time"}|{f"x/{i}/{part}" for i in range(5) for part in ("q", "v")}, "advance write footprint")
            require(writes["action_time"] == Q(n, 40), "supplied action-time advancement")
            for key, value in writes.items():
                if key != "action_time":
                    require(np.isfinite(float(value)) and Q(float(value)) == value, "advanced binary64 register encoding")
            outgoing = np.array([float(writes[f"x/{i}/{part}"]) for part in ("q", "v") for i in range(5)])
            advances.append((incoming, outgoing))
        for i in range(5):
            consume("baseline", [n, i], [f"x/{i}/q", f"x/{i}/v"],
                    {f"b/{n}/{i}/{part}": state[f"x/{i}/{part}"] for part in ("q", "v")})
        for i in range(5):
            j = (i+1) % 5
            old = {f"x/{patch}/{part}": state[f"x/{patch}/{part}"] for patch in (i, j) for part in ("q", "v")}
            consume("probe", [n, i, j], old, {
                f"x/{patch}/{part}": (old[f"x/{i}/{part}"]+old[f"x/{j}/{part}"])/2
                for patch in (i, j) for part in ("q", "v")})
            consume("response", [n, i, j], [f"x/{i}/{part}" for part in ("q", "v")],
                    {f"r/{n}/{i}/{part}": state[f"x/{i}/{part}"] for part in ("q", "v")})
            read_keys = [f"{prefix}/{n}/{i}/{part}" for prefix in ("b", "r") for part in ("q", "v")]+["cycles"]
            # The expected repair is the saved pre-probe state, not the
            # producer's algebraic expression for that repair.
            consume("feedback", [n, i, j], read_keys, {**old, "cycles": state["cycles"]+1})
        read_keys = [f"{prefix}/{n}/{i}/{part}" for prefix in ("b", "r") for i in range(5) for part in ("q", "v")]+["action_time", "cycles"]
        out = {f"decoded_time/{n}": Q(n, 40), f"decoded_cycles/{n}": Q(5*(n+1))}
        for i in range(5):
            neighbor = (i-1) % 5
            for part in ("q", "v"):
                value = 2*state[f"r/{n}/{neighbor}/{part}"]-state[f"b/{n}/{neighbor}/{part}"]
                require(value == state[f"b/{n}/{i}/{part}"] == state[f"x/{i}/{part}"], "exact restoration and neighbor agreement")
                out[f"d/{n}/{i}/{part}"] = value
        event_id = cursor
        consume("decode", [n], read_keys, out)
        decoded.append({"sample_index": n, "decode_event_id": event_id,
            "q_exact": [str(out[f"d/{n}/{i}/q"]) for i in range(5)],
            "velocity_exact": [str(out[f"d/{n}/{i}/v"]) for i in range(5)],
            "action_time_exact": str(out[f"decoded_time/{n}"]), "completed_repair_cycles": int(out[f"decoded_cycles/{n}"])})
    require(cursor == len(events), "unconsumed events")
    return decoded, advances, previous_hash


def independent_parent():
    spec = importlib.util.spec_from_file_location("charged_instrument_action_verifier", HERE/"verify_whitney_charged_dynamics.py")
    require(spec is not None and spec.loader is not None, "independent action verifier")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def verify(packet):
    keys(packet, {"schema", "scope", "run_id", "source_base_commit", "source_pins", "contract", "mesh", "events", "event_root", "frames", "reference_comparison", "clock_readout"}, "instrument schema")
    exact([packet["schema"], packet["scope"], packet["run_id"], packet["source_base_commit"]],
          ["oph.whitney_charged_instrument.v1", SCOPE, "whitney-charged-self-reading-lean435-20261018-v2", "a8ab45b7530fecbac8c06eb19ee8b7e95a7196a2"], "instrument scope/identity")
    exact(packet["contract"], expected_contract(), "instrument contract")
    keys(packet["source_pins"], PINS, "instrument source pin census")
    for path in PINS:
        require(packet["source_pins"][path] == hashlib.sha256((ROOT/path).read_bytes()).hexdigest(), "source pin: "+path)
    decoded, advances, event_root = replay_events(packet["events"])
    exact(packet["event_root"], event_root, "final event root")
    require(type(packet["frames"]) is list and len(packet["frames"]) == 81, "frame census")
    for frame, header in zip(packet["frames"], decoded, strict=True):
        keys(frame, set(header)|{"configuration", "velocity", "acceleration", "electric_cochain", "magnetic_cochain", "energy", "kinetic_energy", "potential_energy", "lagrangian", "field_readouts"}, "decoded frame schema")
        exact({key: frame[key] for key in header}, header, "frame record provenance")
    exact(packet["clock_readout"], {"completed_repair_cycles": 405, "solver_advances": 80,
        "checkpoint_cycle_counts": [5*(n+1) for n in range(81)], "cycle_intervals": [5]*80,
        "supplied_action_step": "1/40",
        "clock_scope": "event-derived cycle intervals; supplied model-time assignment; no physical or SI calibration"}, "operational clock scope and event intervals")
    parent = independent_parent()
    historical = load(ROOT/PARENT)
    parent.verify(historical)
    mesh = parent.geometry(4)
    keys(packet["mesh"], {"vertices", "edges", "faces", "tetrahedra"}, "field mesh schema")
    parent.close(packet["mesh"]["vertices"], mesh["vertices"], "field vertex geometry", atol=1e-13, rtol=0)
    for key in ("edges", "faces", "tetrahedra"):
        parent.integer_table(packet["mesh"][key], historical["mesh"][key], "field "+key)
    step_errors = []
    for incoming, outgoing in advances:
        replay = solve_ivp(parent.independent_rhs, (0, 1/40), incoming, method="DOP853",
                          rtol=3e-14, atol=3e-15, max_step=1/160)
        require(replay.success, "independent numerical advancement")
        step_errors.append(float(np.max(abs(replay.y[:, -1]-outgoing))))
    require(max(step_errors) < 2e-10, "advance does not follow decoded state and action")
    euler, gauss, energies, reference_errors = [], [], [], []
    for frame, old in zip(packet["frames"], historical["samples"], strict=True):
        state = np.array([float(fraction(v)) for key in ("q_exact", "velocity_exact") for v in frame[key]])
        q, velocity = parent.expanded(state[:5]), parent.expanded(state[5:])
        acceleration = parent.expanded(parent.independent_rhs(0, state)[5:])
        for key, target in (("configuration", q), ("velocity", velocity), ("acceleration", acceleration),
                            ("electric_cochain", -velocity[:42]), ("magnetic_cochain", mesh["C"]@q[:42])):
            parent.close(frame[key], target, "decoded "+key)
        audit = parent.full_audit(q, velocity, parent.numeric(frame["acceleration"], (68,), "acceleration"), mesh)
        euler.append(float(np.max(abs(audit["euler_lagrange"]))))
        gauss.append(float(np.max(abs(audit["gauss"]))))
        for key in ("energy", "lagrangian"):
            parent.close(frame[key], audit[key], "decoded "+key)
        kinetic = (audit["energy"]+audit["lagrangian"])/2
        parent.close(frame["kinetic_energy"], kinetic, "decoded kinetic energy")
        parent.close(frame["potential_energy"], audit["energy"]-kinetic, "decoded potential energy")
        parent.check_readouts(frame["field_readouts"], q, velocity, audit["rho_load"], mesh)
        energies.append(audit["energy"])
        reference_errors.append(float(np.max(abs(state-np.r_[old["q_reduced"], old["v_reduced"]]))))
    drift = max(abs(value-energies[0]) for value in energies)
    require(max(euler) < 2e-9 and max(gauss) < 2e-9 and drift < 2e-9, "full charged action/Gauss/energy controls")
    comparison = packet["reference_comparison"]
    keys(comparison, {"path", "role", "maximum_coordinate_difference"}, "historical comparison schema")
    exact([comparison["path"], comparison["role"]], [PARENT, "comparison only; no inherited event custody or future-state input"], "historical comparison scope")
    parent.close(comparison["maximum_coordinate_difference"], max(reference_errors), "historical difference", atol=1e-14, rtol=1e-8)
    require(max(reference_errors) < 2e-9, "same initial-value action reference")
    return {"accepted": True, "scope": SCOPE, "patches": 5, "writable_real_registers": 10,
        "events": 1782, "decoded_samples": 81, "completed_repair_cycles": 405,
        "solver_advances": 80, "full_equations_per_sample": 68, "gauss_equations_per_sample": 13,
        "exact_record_restoration": True, "observer_software_history": True,
        "physical_clock_calibrated": False, "physical_observer_placement": False,
        "quantum_state_history": False, "spatial_trajectory_convergence": False,
        "rigorous_trajectory_enclosure": False, "empirical_prediction": False,
        "numeric_diagnostics": {"advance_replay_max_abs": max(step_errors), "euler_lagrange_max_abs": max(euler),
            "gauss_max_abs": max(gauss), "energy_drift": drift, "historical_reference_max_abs": max(reference_errors)}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, default=OUTPUT)
    args = parser.parse_args()
    print(json.dumps(verify(load(args.receipt)), sort_keys=True))

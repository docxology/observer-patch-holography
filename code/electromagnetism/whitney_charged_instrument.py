"""Record-assisted self-reading execution of the coupled charged action.

Five bounded software patches hold the symmetry coordinates and velocities.
Every numerical advance reads the previous decoded records. Destructive port
averaging, retained responses and feedback restore the exact dyadic registers.
The patches are computational coordinates, not physically placed observers.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp

import whitney_charged_dynamics as dynamics

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
OUTPUT = HERE/"runtime/whitney_charged_instrument_receipt.json"
PARENT = "code/electromagnetism/runtime/whitney_charged_dynamics_receipt.json"
SCOPE = "SELF_READING_COUPLED_CLASSICAL_EXECUTION__COMPUTATIONAL_PATCHES__MODEL_TIME_ONLY"
PINS = (
    "Lean/Screen/SeamCurrentEdge30Moment.lean",
    "Lean/Screen/SeamCurrentCarrierQuotient.lean",
    "Lean/ObserverPatchHolography/CoreAxioms.lean",
    "code/electromagnetism/verify_cone_whitney_bridge.py",
    "code/electromagnetism/whitney_charged_dynamics.py",
    "code/electromagnetism/verify_whitney_charged_dynamics.py", PARENT,
    "paper/tex_fragments/WHITNEY_CHARGED_MATTER.tex",
    "paper/tex_fragments/WHITNEY_CHARGED_EXECUTION.tex",
    "paper/tex_fragments/WHITNEY_CHARGED_INSTRUMENT.tex",
    "code/electromagnetism/whitney_charged_instrument.py",
    "code/electromagnetism/verify_whitney_charged_instrument.py",
    "code/electromagnetism/test_whitney_charged_instrument.py",
)


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)+"\n").encode("ascii")


def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def contract():
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


class Recorder:
    def __init__(self):
        self.state, self.writer, self.events = {}, {}, []

    def emit(self, op, args, keys, calculate):
        reads = {key: {"writer": self.writer[key], "value": str(self.state[key])} for key in keys}
        values = {key: self.state[key] for key in keys}
        writes = {key: Q(value) for key, value in calculate(values).items()}
        event = {"id": len(self.events), "op": op, "args": args, "reads": reads,
                 "parents": sorted({row["writer"] for row in reads.values()}),
                 "writes": {key: str(value) for key, value in writes.items()},
                 "previous_hash": self.events[-1]["event_hash"] if self.events else "0"*64}
        event["event_hash"] = digest(event)
        self.events.append(event)
        self.state.update(writes)
        self.writer.update({key: event["id"] for key in writes})
        return event["id"]


def state_keys(prefix):
    return [f"{prefix}/{i}/{part}" for i in range(5) for part in ("q", "v")]


def execute():
    rec = Recorder()
    initial = dynamics.initial()
    inputs = {"action_time": Q(0), "action_step": Q(1, 40), "cycles": Q(0),
              "e": Q(1, 4), "m_squared": Q(1, 2), "g": Q(1, 4)}
    for i in range(5):
        inputs[f"x/{i}/q"], inputs[f"x/{i}/v"] = Q(float(initial[i])), Q(float(initial[5+i]))
    rec.emit("initialize", [], [], lambda _: inputs)
    frames, mesh = [], json.loads(canonical(dynamics.mesh_data()))
    for n in range(81):
        if n:
            keys = state_keys(f"d/{n-1}")+["action_time", "action_step"]
            def advance(values):
                y = np.array([float(values[f"d/{n-1}/{i}/{part}"])
                              for part in ("q", "v") for i in range(5)])
                step = float(values["action_step"])
                solution = solve_ivp(dynamics.rhs, (0, step), y, method="DOP853",
                    rtol=3e-13, atol=3e-14, max_step=1/80)
                if not solution.success:
                    raise ValueError("charged instrument advance failed")
                out = {"action_time": values["action_time"]+values["action_step"]}
                for i in range(5):
                    out[f"x/{i}/q"] = Q(float(solution.y[i, -1]))
                    out[f"x/{i}/v"] = Q(float(solution.y[5+i, -1]))
                return out
            rec.emit("advance", [n], keys, advance)
        for i in range(5):
            rec.emit("baseline", [n, i], [f"x/{i}/q", f"x/{i}/v"],
                lambda v, i=i: {f"b/{n}/{i}/{part}": v[f"x/{i}/{part}"] for part in ("q", "v")})
        for i in range(5):
            j = (i+1) % 5
            keys = [f"x/{patch}/{part}" for patch in (i, j) for part in ("q", "v")]
            rec.emit("probe", [n, i, j], keys, lambda v, i=i, j=j: {
                f"x/{patch}/{part}": (v[f"x/{i}/{part}"]+v[f"x/{j}/{part}"])/2
                for patch in (i, j) for part in ("q", "v")})
            rec.emit("response", [n, i, j], [f"x/{i}/{part}" for part in ("q", "v")],
                lambda v, i=i: {f"r/{n}/{i}/{part}": v[f"x/{i}/{part}"] for part in ("q", "v")})
            keys = [f"{prefix}/{n}/{i}/{part}" for prefix in ("b", "r") for part in ("q", "v")]+["cycles"]
            rec.emit("feedback", [n, i, j], keys, lambda v, i=i, j=j: {
                **{f"x/{i}/{part}": v[f"b/{n}/{i}/{part}"] for part in ("q", "v")},
                **{f"x/{j}/{part}": 2*v[f"r/{n}/{i}/{part}"]-v[f"b/{n}/{i}/{part}"] for part in ("q", "v")},
                "cycles": v["cycles"]+1})
        keys = [f"{prefix}/{n}/{i}/{part}" for prefix in ("b", "r") for i in range(5) for part in ("q", "v")]
        keys += ["action_time", "cycles"]
        def decode(values):
            out = {f"decoded_time/{n}": values["action_time"], f"decoded_cycles/{n}": values["cycles"]}
            for i in range(5):
                neighbor = (i-1) % 5
                for part in ("q", "v"):
                    value = 2*values[f"r/{n}/{neighbor}/{part}"]-values[f"b/{n}/{neighbor}/{part}"]
                    if value != values[f"b/{n}/{i}/{part}"]:
                        raise ValueError("neighbor readback disagrees with local baseline")
                    out[f"d/{n}/{i}/{part}"] = value
            return out
        decode_id = rec.emit("decode", [n], keys, decode)
        if any(rec.state[f"x/{i}/{part}"] != rec.state[f"d/{n}/{i}/{part}"] for i in range(5) for part in ("q", "v")):
            raise ValueError("serial feedback failed to restore the exact state")
        q = np.array([float(rec.state[f"d/{n}/{i}/q"]) for i in range(5)])
        velocity = np.array([float(rec.state[f"d/{n}/{i}/v"]) for i in range(5)])
        result = dynamics.reduced(q, velocity)
        full_q, full_v, full_acc = dynamics.lift(q, velocity, result["acceleration"])
        frames.append({"sample_index": n, "decode_event_id": decode_id,
            "q_exact": [str(rec.state[f"d/{n}/{i}/q"]) for i in range(5)],
            "velocity_exact": [str(rec.state[f"d/{n}/{i}/v"]) for i in range(5)],
            "action_time_exact": str(rec.state[f"decoded_time/{n}"]),
            "completed_repair_cycles": int(rec.state[f"decoded_cycles/{n}"]),
            "configuration": full_q.tolist(), "velocity": full_v.tolist(),
            "acceleration": full_acc.tolist(), "electric_cochain": (-full_v[:42]).tolist(),
            "magnetic_cochain": [0.0]*50,
            "energy": result["energy"], "kinetic_energy": result["kinetic"],
            "potential_energy": result["potential"], "lagrangian": result["lagrangian"],
            "field_readouts": dynamics.readouts(q, velocity, mesh)})
    return rec.events, frames, mesh


def build():
    # Historical samples are opened only after every new advance and readback.
    events, frames, mesh = execute()
    historical = json.loads((ROOT/PARENT).read_text(encoding="utf-8"))
    error = max(abs(float(Q(frame[key][i]))-old[old_key][i])
        for frame, old in zip(frames, historical["samples"], strict=True)
        for key, old_key in (("q_exact", "q_reduced"), ("velocity_exact", "v_reduced")) for i in range(5))
    return {"schema": "oph.whitney_charged_instrument.v1", "scope": SCOPE,
        "run_id": "whitney-charged-self-reading-lean435-20261018-v2", "source_base_commit": "a8ab45b7530fecbac8c06eb19ee8b7e95a7196a2",
        "source_pins": {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in PINS},
        "contract": contract(), "mesh": mesh, "events": events, "event_root": events[-1]["event_hash"],
        "frames": frames,
        "reference_comparison": {"path": PARENT, "role": "comparison only; no inherited event custody or future-state input",
            "maximum_coordinate_difference": float(error)},
        "clock_readout": {"completed_repair_cycles": 405, "solver_advances": 80,
            "checkpoint_cycle_counts": [5*(n+1) for n in range(81)],
            "cycle_intervals": [5]*80, "supplied_action_step": "1/40",
            "clock_scope": "event-derived cycle intervals; supplied model-time assignment; no physical or SI calibration"}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    packet = build()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(canonical(packet))
    print(json.dumps({"receipt": str(args.output), "bytes": args.output.stat().st_size,
                      "events": len(packet["events"]), "frames": len(packet["frames"])}))

"""Draft a capture contract; this command does not freeze or run an experiment."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
PARENT = "code/electromagnetism/runtime/serial_maxwell_readout_receipt.json"
PARENT_SHA = "ed20c921d8e03b73acd85a24c9a3abc76f29c642c51dbee53642704a86134f6d"
ADAPTER_SOURCES = ["code/maxwell_measurement/" + name for name in
                   ("contract.py", "verify.py", "test_measurement.py")]


def draft():
    raw = (ROOT / PARENT).read_bytes()
    if hashlib.sha256(raw).hexdigest() != PARENT_SHA:
        raise ValueError("immutable serial episode differs")
    text = (ROOT / "Lean/Screen/SeamCurrentCarrierQuotient.lean").read_text(encoding="utf-8")
    rows = []
    for name in ("seamLeft", "seamRight"):
        part = text.split("def " + name, 1)[1].split("![", 1)[1].split("]", 1)[0]
        rows.append([int(x) for x in re.findall(r"\d+", part)])
    channels = []
    for k in range(42):
        channels.append({
            "channel": f"slot{k}", "coordinate": k,
            "quantity": "node_potential" if k < 12 else "edge_potential",
            "oriented_ports": [k] if k < 12 else [rows[0][k-12], rows[1][k-12]],
            "orientation": 1, "raw_unit": "raw_count",
            "model_unit": "dimensionless_model_potential",
            "calibration": {"id": None, "gain": None, "offset": None,
                            "raw_error": None, "reference_sha256": None,
                            "reference_samples": []}})
    return {
        "schema": "oph.maxwell_measurement.preregistration.v1", "status": "DRAFT",
        "study_id": None, "run_id": None, "capture_kind": None,
        "preregistered_utc": None,
        "parent": {"path": PARENT, "sha256": PARENT_SHA},
        "adapter_sources": {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
                            for path in ADAPTER_SOURCES},
        "apparatus": {"device_id": None, "firmware_sha256": None,
                      "claimant_organization": None,
                      "interpretation": "hardware encoding of supplied model potentials",
                      "physical_electromagnetic_field_claim": False},
        "execution": {"gauge_order": [False, True], "events_per_execution": 585,
                      "state_coordinates": 42, "slices": 3, "probes_per_slice": 60,
                      "feedback_cycles_per_execution": 180,
                      "held_out_slice": 2, "model_action_step": "1/2",
                      "calibration_source": "external references only; no episode samples",
                      "record_order_is_physical_causal_order": False},
        "channels": channels,
        "clock": {"orientation": 1, "raw_unit": "device_tick",
                  "seconds_per_tick": None, "tick_error": None,
                  "reference_sha256": None,
                  "model_action_time_equals_device_time": False},
        "limits": {"maximum_coordinate_width": "1/1000",
                   "maximum_field_width": "1/20",
                   "maximum_action_width": "1/2",
                   "maximum_tick_error": "1/1000",
                   "maximum_clock_relative_width": "1/1000",
                   "minimum_control_separation": "1/4"},
        "controls": ["sham_no_probe", "pair_mean", "feedback_disabled"],
        "decision": "complete interval conformance with held-out slice and gauge controls",
        "physical_completion_claim": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("refusing to overwrite an existing contract")
    raw = (json.dumps(draft(), sort_keys=True, indent=2) + "\n").encode("utf-8")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(raw)
    print(json.dumps({"path": str(args.output), "sha256": hashlib.sha256(raw).hexdigest(),
                      "status": "DRAFT", "experiment_frozen": False}))


if __name__ == "__main__":
    main()

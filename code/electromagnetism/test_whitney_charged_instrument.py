"""Adversarial event provenance and coupled-state readback regressions."""
from copy import deepcopy
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_whitney_charged_instrument as verifier
import whitney_charged_instrument as producer


@pytest.fixture(scope="module")
def packet():
    return verifier.load()


def rehash(packet):
    previous = "0"*64
    for event in packet["events"]:
        event["previous_hash"] = previous
        event["event_hash"] = hashlib.sha256(verifier.canonical({k: v for k, v in event.items() if k != "event_hash"})).hexdigest()
        previous = event["event_hash"]
    packet["event_root"] = previous


def test_complete_instrument_replays(packet):
    result = verifier.verify(packet)
    assert result["accepted"] is True
    assert result["events"] == 1782
    assert result["decoded_samples"] == 81
    assert result["completed_repair_cycles"] == 405
    assert result["exact_record_restoration"] is True
    assert result["observer_software_history"] is True
    assert result["physical_clock_calibrated"] is False
    assert result["physical_observer_placement"] is False
    assert result["quantum_state_history"] is False


def test_fresh_execution_uses_no_historical_future_table(packet, monkeypatch):
    # execute() must finish even if historical receipt reads are unavailable.
    original = Path.read_text
    def guard(path, *args, **kwargs):
        if path == producer.ROOT/producer.PARENT:
            raise AssertionError("future reference sample read during execution")
        return original(path, *args, **kwargs)
    monkeypatch.setattr(Path, "read_text", guard)
    events, frames, _ = producer.execute()
    decoded, advances, _ = verifier.replay_events(events)
    assert len(advances) == 80 and len(decoded) == len(frames) == 81
    assert frames[0]["q_exact"] == packet["frames"][0]["q_exact"]
    assert all(frame["q_exact"] == header["q_exact"] for frame, header in zip(frames, decoded, strict=True))


@pytest.mark.parametrize("mode", ["stale_writer", "future_writer", "wrong_read", "wrong_average", "wrong_response",
    "wrong_feedback", "wrong_port", "missing_parent", "extra_read", "extra_write", "operation_reorder", "clock_skip", "float_index", "bool_parent", "unrecorded_advance_input"])
def test_rehashed_event_mutations_fail(packet, mode):
    changed = deepcopy(packet)
    events = changed["events"]
    target = next(e for e in events if e["op"] == "probe" and e["args"][0] == 3)
    key = next(iter(target["reads"]))
    if mode in {"stale_writer", "future_writer"}:
        target["reads"][key]["writer"] = 0 if mode == "stale_writer" else target["id"]+1
    elif mode == "wrong_read":
        target["reads"][key]["value"] = str(Q(target["reads"][key]["value"])+Q(1, 10**40))
    elif mode == "wrong_average":
        target["writes"][next(iter(target["writes"]))] = "0"
    elif mode in {"wrong_response", "wrong_feedback", "clock_skip"}:
        target = next(e for e in events if e["op"] == ("response" if mode == "wrong_response" else "feedback") and e["args"][0] == 3)
        target["writes"]["cycles" if mode == "clock_skip" else next(iter(target["writes"]))] = "0"
    elif mode == "wrong_port":
        target["args"][2] = (target["args"][2]+1) % 5
    elif mode == "missing_parent":
        target["parents"] = []
    elif mode == "extra_read":
        target["reads"]["future/reference"] = {"writer": 0, "value": "0"}
    elif mode == "extra_write":
        target["writes"]["hidden/trajectory"] = "0"
    elif mode == "operation_reorder":
        target["op"] = "feedback"
    elif mode == "float_index":
        target["id"] = float(target["id"])
    elif mode == "bool_parent":
        target["parents"][0] = True
    elif mode == "unrecorded_advance_input":
        target = next(e for e in events if e["op"] == "advance" and e["args"] == [3])
        key = next(k for k in target["reads"] if k.startswith("d/"))
        target["reads"][key.replace("d/2/", "x/")] = target["reads"].pop(key)
    rehash(changed)
    with pytest.raises(ValueError):
        verifier.replay_events(changed["events"])


@pytest.mark.parametrize("key,value", [("physical_clock_calibrated", True), ("physical_observer_placement", True),
    ("quantum_state_history", True), ("observer_software_history", 1), ("sample_count", 81.0),
    ("rigorous_trajectory_enclosure", True), ("spatial_trajectory_convergence", True), ("empirical_prediction", True)])
def test_scope_and_categorical_types_cannot_be_promoted(packet, key, value):
    changed = deepcopy(packet)
    changed["contract"][key] = value
    with pytest.raises(ValueError, match="contract"):
        verifier.verify(changed)


@pytest.mark.parametrize("mode", ["wrong_frame_state", "wrong_decode_id", "clock_relabel", "missing_event", "extra_frame", "broken_hash"])
def test_projection_and_completeness_fail(packet, mode):
    changed = deepcopy(packet)
    if mode == "wrong_frame_state":
        changed["frames"][40]["q_exact"][0] = "0"
    elif mode == "wrong_decode_id":
        changed["frames"][40]["decode_event_id"] -= 1
    elif mode == "clock_relabel":
        changed["clock_readout"]["clock_scope"] = "derived SI physical clock"
    elif mode == "missing_event":
        changed["events"].pop()
    elif mode == "extra_frame":
        changed["frames"].append(changed["frames"][-1])
    elif mode == "broken_hash":
        changed["events"][90]["event_hash"] = "0"*64
    with pytest.raises(ValueError):
        verifier.verify(changed)


def test_coherent_frozen_future_history_rejected_by_action(packet):
    # Reconstruct a causally consistent but frozen execution; hash chains and
    # exact probe algebra alone must not make it a dynamical solution.
    original = producer.solve_ivp
    class Frozen:
        success = True
        def __init__(self, state):
            import numpy as np
            self.y = np.column_stack((state, state))
    try:
        producer.solve_ivp = lambda rhs, span, state, **kwargs: Frozen(state)
        events, frames, mesh = producer.execute()
    finally:
        producer.solve_ivp = original
    changed = deepcopy(packet)
    changed.update(events=events, frames=frames, mesh=mesh, event_root=events[-1]["event_hash"])
    with pytest.raises(ValueError, match="advance does not follow"):
        verifier.verify(changed)


def test_late_matter_field_corruption_rejected(packet):
    changed = deepcopy(packet)
    changed["frames"][-1]["field_readouts"]["covariant_time_derivative_at_centroids"][5][0] += 1e-5
    with pytest.raises(ValueError, match="readout"):
        verifier.verify(changed)


def test_source_bytes_are_rechecked(packet, monkeypatch):
    original = Path.read_bytes
    parent_path = verifier.ROOT/verifier.PARENT
    def altered(path):
        value = original(path)
        return value+b"\n" if path == parent_path else value
    monkeypatch.setattr(Path, "read_bytes", altered)
    with pytest.raises(ValueError, match="source pin"):
        verifier.verify(packet)


@pytest.mark.parametrize("value", [True, 0.0, 1e-16])
def test_topology_categories_are_exact(packet, value):
    changed = deepcopy(packet)
    changed["mesh"]["edges"][0][0] = value
    with pytest.raises(ValueError, match="integer"):
        verifier.verify(changed)


@pytest.mark.parametrize("raw", ['{"events":[],"events":[]}', '{"event":{"id":0,"id":1}}',
    '{"x":NaN}', '{"x":Infinity}', '{"x":1e9999}'])
def test_ambiguous_json_rejected(tmp_path, raw):
    path = tmp_path/"bad.json"
    path.write_text(raw, encoding="utf-8")
    with pytest.raises(ValueError):
        verifier.load(path)


@pytest.mark.parametrize("field, historical", [
    ("run_id", "whitney-charged-self-reading-2026-09-06-v1"),
    ("source_base_commit", "08486bdba2039c916aff3c698bce93e9e62bdfab"),
])
def test_current_execution_rejects_historical_identity(packet, field, historical):
    changed = deepcopy(packet)
    changed[field] = historical
    rehash(changed)
    with pytest.raises(ValueError, match="scope/identity"):
        verifier.verify(changed)

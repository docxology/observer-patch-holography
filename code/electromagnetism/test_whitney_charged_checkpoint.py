"""Exact transferred bounds, source custody, event ancestry and false greens."""
from copy import deepcopy
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import shutil
import types

import pytest


def module(name):
    path = Path(__file__).with_name(name + ".py")
    result = types.ModuleType(name)
    result.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), "exec"), result.__dict__)
    return result


producer = module("whitney_charged_checkpoint")
verifier = module("verify_whitney_charged_checkpoint")


@pytest.fixture(scope="module")
def packet():
    return verifier.load()


@pytest.fixture(scope="module")
def parents():
    return verifier.parent_inputs()


def test_actual_parent_proof_and_exact_consumer(packet):
    assert producer.canonical(packet) == producer.OUTPUT.read_bytes()
    result = verifier.verify(packet)
    assert result["decoded_checkpoints"] == 81
    assert result["events"] == 1782
    assert result["checkpoint_qv_error_certified"] is True
    assert result["parent_enclosure_freshly_verified"] is True
    assert result["maximum_decoded_reference_difference"] == "5/562949953421312"
    bound = Q(result["decoded_checkpoint_error_upper"])
    assert bound == Q(1, 10**10) + Q(5, 2**49)
    assert bound <= Q(result["simple_checkpoint_error_upper"]) == Q(10001, 10**14)
    for key in ("continuous_observer_error_certified", "configuration_clock_error_certified",
                "nonlinear_field_error_certified", "physical_clock_calibrated", "quantum_history"):
        assert result[key] is False


def test_actual_worst_component_is_event_decoded_not_float_subtraction(packet, parents):
    history = parents[0]["historical"]["samples"]
    row = packet["checkpoints"][79]
    d = Q(row["decoded_qv"][7])
    ref = Q.from_float(history[79]["v_reduced"][2])
    assert abs(d-ref) == Q(5, 2**49)
    assert Q(row["absolute_reference_differences"][7]) == abs(d-ref)
    assert any(Q.from_float(h["t"]) != Q(n, 40) for n, h in enumerate(history))
    assert [r["nominal_time"] for r in packet["checkpoints"]] == [str(Q(n, 40)) for n in range(81)]


def test_intermediate_probe_is_not_enclosed_checkpoint(packet, parents):
    events = parents[0]["instrument"]["events"]
    first_probe = next(e for e in events if e["op"] == "probe")
    assert Q(first_probe["writes"]["x/0/q"]) == Q(1, 2)
    assert Q(packet["checkpoints"][0]["decoded_qv"][0]) == 0
    assert Q(1, 2) > Q(packet["bounds"]["simple_checkpoint_error_upper"])
    assert packet["contract"]["intermediate_probe_register_error_certified"] is False


@pytest.mark.parametrize("mutation", [
    "scope", "physical", "continuous", "probe", "clock", "quantum", "canonical_frame",
    "coordinate_order", "float_count", "bool_count", "missing_row", "reordered_row",
    "float_index", "bool_index", "time", "float_time", "event_id", "event_hash", "cycles",
    "coordinate", "coordinate_swap", "frame_copy", "difference", "negative_difference",
    "row_bound", "global_bound", "historical_bound", "simple_bound", "maximum",
    "parent_hash", "parent_path", "float_parent_bytes", "missing_pin", "stale_pin", "extra_field",
])
def test_coherent_or_partial_receipt_forgery_rejected(packet, mutation):
    p = deepcopy(packet)
    row = p["checkpoints"][79]
    if mutation == "scope": p["scope"] = "PHYSICAL_COMPLETION"
    if mutation == "physical": p["contract"]["physical_clock_calibrated"] = True
    if mutation == "continuous": p["contract"]["continuous_observer_error_certified"] = True
    if mutation == "probe": p["contract"]["intermediate_probe_register_error_certified"] = True
    if mutation == "clock": p["contract"]["configuration_clock_error_certified"] = True
    if mutation == "quantum": p["contract"]["quantum_history"] = True
    if mutation == "canonical_frame": p["contract"]["coordinate_frame"] = "nine canonical coordinates"
    if mutation == "coordinate_order": p["contract"]["coordinate_order"].reverse()
    if mutation == "float_count": p["events"] = 1782.0
    if mutation == "bool_count": p["events"] = True
    if mutation == "missing_row": p["checkpoints"].pop()
    if mutation == "reordered_row": p["checkpoints"][78:80] = p["checkpoints"][79:77:-1]
    if mutation == "float_index": row["sample_index"] = 79.0
    if mutation == "bool_index": p["checkpoints"][1]["sample_index"] = True
    if mutation == "time": row["nominal_time"] = "2"
    if mutation == "float_time": row["nominal_time"] = 1.975
    if mutation == "event_id": row["decode_event_id"] -= 1
    if mutation == "event_hash": row["decode_event_hash"] = "0"*64
    if mutation == "cycles": row["completed_repair_cycles"] += 1
    if mutation == "coordinate": row["decoded_qv"][7] = str(Q(row["decoded_qv"][7]) + Q(1, 10**15))
    if mutation == "coordinate_swap": row["decoded_qv"][1:3] = row["decoded_qv"][2:0:-1]
    if mutation == "frame_copy": row["decoded_qv"] = p["checkpoints"][78]["decoded_qv"]
    if mutation == "difference": row["absolute_reference_differences"][7] = "0"
    if mutation == "negative_difference": row["absolute_reference_differences"][7] = "-1"
    if mutation == "row_bound": row["checkpoint_error_upper"] = "1/10000000000"
    if mutation == "global_bound": p["bounds"]["decoded_checkpoint_error_upper"] = "1/10000000000"
    if mutation == "historical_bound": p["bounds"]["historical_qv_error_upper"] = "1/100000000000"
    if mutation == "simple_bound": p["bounds"]["simple_checkpoint_error_upper"] = "1/10000000000"
    if mutation == "maximum": p["bounds"]["maximum_decoded_reference_difference"] = "0"
    if mutation == "parent_hash": p["parents"]["instrument"]["sha256"] = "0"*64
    if mutation == "parent_path": p["parents"]["instrument"]["path"] = p["parents"]["enclosure"]["path"]
    if mutation == "float_parent_bytes": p["parents"]["instrument"]["bytes"] = 2233726.0
    if mutation == "missing_pin": p["source_pins"].pop(next(iter(p["source_pins"])))
    if mutation == "stale_pin": p["source_pins"][next(iter(p["source_pins"]))] = "0"*64
    if mutation == "extra_field": p["frames"] = p["checkpoints"]
    with pytest.raises(ValueError):
        verifier.verify(p)


@pytest.mark.parametrize("raw", [b'{"x":1,"x":2}', b'{"x":0.0}', b'{"x":1e9999}',
                                  b'{"x":NaN}', b'{"x":Infinity}', b'{"x":-Infinity}'])
def test_strict_json_reader(tmp_path, raw):
    path = tmp_path / "bad.json"
    path.write_bytes(raw)
    with pytest.raises(ValueError):
        verifier.load(path)


@pytest.mark.parametrize("value", [True, 0.0, "01", "-0", "2/2", "1/0", "1e-10", "0.5", "9"*201])
def test_noncanonical_rational_rejected(value):
    with pytest.raises(ValueError):
        verifier.rational(value)


def reseal(events):
    previous = "0"*64
    for event in events:
        event["previous_hash"] = previous
        event.pop("event_hash", None)
        event["event_hash"] = sha256(producer.canonical(event)).hexdigest()
        previous = event["event_hash"]
    return previous


@pytest.mark.parametrize("mutation", ["wrong_writer", "changed_time", "fake_decode", "probe_copy"])
def test_independent_event_replay_rejects_fully_rehashed_forgeries(parents, mutation):
    packets, sources = parents
    events = deepcopy(packets["instrument"]["events"])
    decode = next(e for e in events if e["op"] == "decode")
    if mutation == "wrong_writer":
        read = next(r for r in decode["reads"].values() if r["writer"] != 0)
        read["writer"] = 0
        decode["parents"] = sorted({r["writer"] for r in decode["reads"].values()})
    if mutation == "changed_time": decode["writes"]["decoded_time/0"] = "1/40"
    if mutation == "fake_decode": decode["writes"]["d/0/0/q"] = "1/1000000000000000"
    if mutation == "probe_copy": decode["writes"]["d/0/0/q"] = "1/2"
    reseal(events)
    path = verifier.PREFIX + "verify_whitney_charged_instrument.py"
    checker = verifier.fresh(path, sources[path])
    with pytest.raises(ValueError):
        checker.replay_events(events)


def mirror(tmp_path, parents):
    files = set(verifier.PIN_PATHS)
    files.update(p["path"] for p in verifier.PARENTS.values())
    files.update(parents[1])
    for relative in files:
        path = tmp_path / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(verifier.ROOT / relative, path)


@pytest.mark.parametrize("mutation", ["rehashed_event", "frame_substitution", "historical_time", "enclosure_state"])
def test_changed_parent_rejected_even_with_new_consumer_identity(packet, parents, tmp_path, monkeypatch, mutation):
    mirror(tmp_path, parents)
    role = "instrument" if mutation in ("rehashed_event", "frame_substitution") else (
        "historical" if mutation == "historical_time" else "enclosure")
    path = tmp_path / verifier.PARENTS[role]["path"]
    data = json.loads(path.read_bytes())
    if mutation == "rehashed_event":
        data["events"][1]["writes"]["b/0/0/q"] = "1"
        data["event_root"] = reseal(data["events"])
    if mutation == "frame_substitution": data["frames"][79] = data["frames"][78]
    if mutation == "historical_time": data["samples"][79]["t"] = 2.0
    if mutation == "enclosure_state": data["states"][79]["state"][0] = ["0", "0"]
    raw = producer.canonical(data)
    path.write_bytes(raw)
    p = deepcopy(packet)
    p["parents"][role]["sha256"] = sha256(raw).hexdigest()
    p["parents"][role]["bytes"] = len(raw)
    monkeypatch.setattr(verifier, "ROOT", tmp_path)
    with pytest.raises(ValueError, match="immutable parent"):
        verifier.verify(p)
    # Retaining the original commitment also fails actual file-byte checking.
    with pytest.raises(ValueError, match="immutable parent bytes|stale parent source"):
        verifier.verify(packet)


def test_actual_parent_source_edit_rejected_before_execution(packet, parents, tmp_path, monkeypatch):
    mirror(tmp_path, parents)
    path = tmp_path / (verifier.PREFIX + "verify_whitney_charged_enclosure.py")
    path.write_bytes(path.read_bytes().replace(b"BITS = 256", b"BITS = 255"))
    monkeypatch.setattr(verifier, "ROOT", tmp_path)
    with pytest.raises(ValueError, match="stale parent source"):
        verifier.verify(packet)


def test_fresh_loader_bypasses_same_size_source_cache(tmp_path):
    path = tmp_path / "probe.py"
    path.write_bytes(b"answer = 3\n")
    assert verifier.fresh(str(path), path.read_bytes()).answer == 3
    path.write_bytes(b"answer = 7\n")
    assert verifier.fresh(str(path), path.read_bytes()).answer == 7


def test_every_acceptance_attempt_reaches_new_proof_execution(packet, monkeypatch):
    original, calls = verifier.fresh, []
    def guarded(path, raw):
        if path.endswith("verify_whitney_charged_enclosure.py"):
            calls.append(sha256(raw).hexdigest())
            def fail(_):
                raise ValueError("fresh proof sentinel")
            return types.SimpleNamespace(verify=fail)
        return original(path, raw)
    monkeypatch.setattr(verifier, "fresh", guarded)
    for _ in range(2):
        with pytest.raises(ValueError, match="fresh proof sentinel"):
            verifier.verify(packet)
    assert len(calls) == 2


def test_original_historical_dyadic_witness_is_preserved():
    path = Path(__file__).with_name("fixtures") / "charged_checkpoint_20260906_witness.json"
    raw = path.read_bytes()
    assert sha256(raw).hexdigest() == "3153d6286ec0d9d7d7d3dadf80f6b76edc3276eadd7d5109f21a16637a949e73"
    witness = json.loads(raw)
    assert witness["sample_index"] == 79 and witness["coordinate_index"] == 7
    decoded = Q(witness["decoded_exact"])
    reference = Q.from_float(float.fromhex(witness["reference_binary64_hex"]))
    assert abs(decoded - reference) == Q(21, 2**51)
    assert str(abs(decoded - reference)) == witness["absolute_reference_difference"]

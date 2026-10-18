"""Independent derivatives, gauge controls, and adversarial receipt checks."""
from copy import deepcopy
from pathlib import Path
import sys

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify_whitney_charged_dynamics as audit


@pytest.fixture(scope="module")
def packet():
    return audit.load()


def test_full_receipt_replay(packet):
    summary = audit.verify(packet)
    assert summary["accepted"] and summary["samples"] == 81
    assert summary["full_euler_max_abs"] < 1e-10
    assert summary["gauss_max_abs"] < 1e-10
    assert summary["independent_replay_difference"] < 1e-10
    assert summary["charge_load_change_max_abs"] > 1
    assert not any(summary[key] for key in ("physical_continuum", "observer_history", "quantum_state"))


def generic_state():
    indices = np.arange(68)
    return np.sin(indices+1)/7, np.cos(indices+2)/9


def test_full_jacobians_against_independent_finite_differences():
    mesh = audit.geometry(3)
    element = mesh["elements"][7]
    q, v = generic_state()
    fields = audit.element_fields(q, v, element)
    step = 2e-6
    for column, slot in enumerate(fields["slots"]):
        plus, minus = q.copy(), q.copy()
        plus[slot] += step; minus[slot] -= step
        fplus, fminus = (audit.element_fields(x, v, element) for x in (plus, minus))
        scalar_derivative = (fplus["scalar"]-fminus["scalar"])/(2*step)
        spatial_derivative = (fplus["spatial"]-fminus["spatial"])/(2*step)
        assert np.max(abs(scalar_derivative-fields["jacobian"][:, column])) < 4e-11
        assert np.max(abs(spatial_derivative-fields["spatial_jacobian"][:, column])) < 5e-11
    # Directional second derivative audits every velocity-dependent phase term.
    step = 1e-3
    plus = audit.element_fields(q+step*v, v, element)["scalar"]
    minus = audit.element_fields(q-step*v, v, element)["scalar"]
    second = (plus-2*fields["scalar"]+minus)/step**2
    assert np.max(abs(second-fields["second_velocity"])) < 2e-9
    assert np.max(abs(fields["jacobian"]@v[fields["slots"]]-fields["scalar_dot"])) < 1e-15


def test_time_dependent_gauge_covariance_and_wrong_sign_control():
    mesh = audit.geometry(3)
    q, v = generic_state()
    chi, eta = np.sin(np.arange(13)+2)/3, np.cos(np.arange(13)+3)/5
    charge = .25
    phase = np.exp(1j*charge*chi)
    psi = q[42:55]+1j*q[55:]
    psi_dot = v[42:55]+1j*v[55:]
    transformed_psi = phase*psi
    transformed_dot = phase*(psi_dot+1j*charge*eta*psi)
    qq = np.r_[q[:42]+mesh["D"]@chi, transformed_psi.real, transformed_psi.imag]
    vv = np.r_[v[:42]+mesh["D"]@eta, transformed_dot.real, transformed_dot.imag]
    assert np.max(abs(-vv[:42]+mesh["D"]@eta+v[:42])) < 1e-15
    wrong_sign_defect = 0.0
    for element in mesh["elements"]:
        original = audit.element_fields(q, v, element)
        moved = audit.element_fields(qq, vv, element)
        local_phase = np.exp(1j*charge*(element["lam"]@chi[element["tet"]]))
        phi = -element["lam"]@eta[element["tet"]]
        covariant_dot = moved["scalar_dot"]+1j*charge*phi*moved["scalar"]
        wrong = moved["scalar_dot"]-1j*charge*phi*moved["scalar"]
        assert np.max(abs(moved["scalar"]-local_phase*original["scalar"])) < 1e-15
        assert np.max(abs(moved["spatial"]-local_phase[:, None]*original["spatial"])) < 1e-15
        assert np.max(abs(covariant_dot-local_phase*original["scalar_dot"])) < 1e-15
        wrong_sign_defect = max(wrong_sign_defect, np.max(abs(wrong-local_phase*original["scalar_dot"])))
    assert wrong_sign_defect > 1e-3


def test_signed_rotation_average_has_exactly_five_real_fixed_coordinates():
    assert audit.symmetry_certificate() == {"proper_rotations": 60, "edge_fixed_dimension": 1,
        "node_fixed_dimension": 2, "real_configuration_fixed_dimension": 5}


def test_omitted_dressing_terms_and_insufficient_quadrature_are_detected(packet):
    row = packet["samples"][80]
    q, v, a = (np.array(row[key]) for key in ("q", "velocity", "acceleration"))
    good = audit.full_audit(q, v, a)
    bad = audit.full_audit(q, v, a, omit_dressing=True)
    coarse = audit.full_audit(q, v, a, audit.geometry(3))
    assert max(abs(good["euler_lagrange"])) < 1e-10
    assert max(abs(bad["euler_lagrange"])) > 1e-3
    assert max(abs(coarse["euler_lagrange"])) > 1e-5


@pytest.mark.parametrize("kind", ["run", "units", "clock", "quantum", "observer", "scope", "basis", "pins", "sample_order", "scalar", "outside_fixed_space", "acceleration", "electric", "readout", "nonfinite", "bool"])
def test_false_green_mutations_rejected(packet, kind):
    value = deepcopy(packet)
    row = value["samples"][0]
    if kind == "run": value["run_id"] += "-other"
    elif kind == "units": value["metadata"]["units"] = "SI"
    elif kind == "clock": value["metadata"]["time"] = "physical seconds"
    elif kind == "quantum": value["metadata"]["quantum_state"] = row["q"]
    elif kind == "observer": value["metadata"]["observer_history"] = []
    elif kind == "scope": value["scope"] = "PHYSICAL_CONTINUUM"
    elif kind == "basis": value["metadata"]["coordinate_order"] = "unknown"
    elif kind == "pins": value["source_pins"].pop(next(iter(value["source_pins"])))
    elif kind == "sample_order": row["t"] = .025
    elif kind == "scalar":
        row["q_reduced"][1] += .01
        row["q"] = audit.expanded(np.array(row["q_reduced"])).tolist()
    elif kind == "outside_fixed_space": row["q"][15] = .01
    elif kind == "acceleration":
        row["acceleration_reduced"][1] += .01
        row["acceleration"] = audit.expanded(np.array(row["acceleration_reduced"])).tolist()
    elif kind == "electric": row["electric_cochain"][0] *= -1
    elif kind == "readout": row["field_readouts"]["scalar_at_centroids"][0][0] += .01
    elif kind == "nonfinite": row["q"][0] = float("nan")
    elif kind == "bool": row["q"][0] = False
    with pytest.raises(ValueError):
        audit.verify(value)


def test_cached_geometry_does_not_hide_source_byte_changes(packet, monkeypatch):
    audit.geometry()
    original = Path.read_bytes
    target = audit.ROOT/"Lean/Screen/SeamCurrentEdge30Moment.lean"
    def changed(path):
        return original(path)+(b"\n--changed\n" if path == target else b"")
    monkeypatch.setattr(Path, "read_bytes", changed)
    with pytest.raises(ValueError, match="source pin"):
        audit.verify(packet)


def test_duplicate_and_nonfinite_json_rejected(tmp_path):
    path = tmp_path/"invalid.json"
    for content in ('{"a":1,"a":2}', '{"a":NaN}', '{"a":Infinity}'):
        path.write_text(content, encoding="utf-8")
        with pytest.raises(ValueError):
            audit.load(path)


def test_source_reads_are_utf8_with_windows_defaults(monkeypatch):
    original = Path.read_text
    def windows(path, *args, **kwargs):
        if not args and "encoding" not in kwargs:
            kwargs["encoding"] = "cp1252"
        return original(path, *args, **kwargs)
    monkeypatch.setattr(Path, "read_text", windows)
    audit.geometry.cache_clear()
    try:
        assert audit.geometry(2)["vertices"].shape == (13, 3)
    finally:
        audit.geometry.cache_clear()


def test_off_shell_noether_identity_in_all_thirteen_directions():
    mesh = audit.geometry(4)
    q, v = generic_state()
    a = np.sin(np.arange(68)+4)/11
    center = audit.full_audit(q, v, a, mesh)
    step = 2e-5
    plus = audit.full_audit(q+step*v+step**2*a/2, v+step*a, a, mesh)
    minus = audit.full_audit(q-step*v+step**2*a/2, v-step*a, a, mesh)
    gauss_dot = (plus["gauss"]-minus["gauss"])/(2*step)
    residual = center["euler_lagrange"]
    identity = gauss_dot-mesh["D"].T@residual[:42]-.25*(q[42:55]*residual[55:]-q[55:]*residual[42:55])
    assert max(abs(identity)) < 2e-10
    wrong_sign = gauss_dot+mesh["D"].T@residual[:42]-.25*(q[42:55]*residual[55:]-q[55:]*residual[42:55])
    assert max(abs(wrong_sign)) > .01


def test_duffy_rule_integrates_every_barycentric_monomial_through_degree_five():
    from math import factorial
    element = audit.geometry(4)["elements"][0]
    volume = sum(element["weights"])
    for a in range(6):
        for b in range(6-a):
            for c in range(6-a-b):
                for d in range(6-a-b-c):
                    powers = np.array([a, b, c, d])
                    actual = element["weights"]@np.prod(element["lam"]**powers, axis=1)
                    exact = 6*volume*np.prod([factorial(int(p)) for p in powers])/factorial(int(sum(powers))+3)
                    assert abs(actual-exact) < 2e-15


def test_counterfeit_rk4_endpoint_with_recomputed_error_is_rejected(packet):
    value = deepcopy(packet)
    row = value["controls"]["rk4"][0]
    row["endpoint"][0] += .001
    reference = np.array(value["controls"]["tight_reference"])[-1]
    row["endpoint_max_error"] = float(max(abs(np.array(row["endpoint"])-reference)))
    with pytest.raises(ValueError, match="independent RK4 replay"):
        audit.verify(value)


@pytest.mark.parametrize("surface", ["edges", "faces", "tetrahedra"])
@pytest.mark.parametrize("mutation", ["sub_ulp_float", "integral_float", "bool", "fractional_string", "wrong_integer", "missing_entry", "extra_entry"])
def test_topology_has_exact_integer_semantics(packet, surface, mutation):
    value = deepcopy(packet)
    row = value["mesh"][surface][0]
    if mutation == "sub_ulp_float": row[0] += 1e-16
    elif mutation == "integral_float": row[0] = float(row[0])
    elif mutation == "bool": row[0] = False
    elif mutation == "fractional_string": row[0] = str(row[0])+".0"
    elif mutation == "wrong_integer": row[0] = (row[0]+1) % 13
    elif mutation == "missing_entry": row.pop()
    elif mutation == "extra_entry": row.append(row[-1])
    with pytest.raises(ValueError, match="mesh "+surface):
        audit.verify(value)


@pytest.mark.parametrize("surface", ["sample_count", "quadrature_orders", "evaluation_count", "time_window"])
@pytest.mark.parametrize("mutation", ["float", "bool", "string"])
def test_count_and_schedule_types_are_not_accepted_by_numeric_equality(packet, surface, mutation):
    value = deepcopy(packet)
    if surface == "sample_count":
        parent, key = value["integrator"], "sample_count"
    elif surface == "quadrature_orders":
        parent, key = value["controls"]["quadrature_orders"], 0
    elif surface == "evaluation_count":
        parent, key = value["integrator"], "function_evaluations"
    else:
        parent, key = value["integrator"]["t_span"], 0
        if mutation == "float":
            # Continuous times permit real floats; categorical indices do not.
            parent[key] = 1e-16
            with pytest.raises(ValueError, match="integration window"):
                audit.verify(value)
            return
    old = parent[key]
    parent[key] = float(old) if mutation == "float" else bool(old) if mutation == "bool" else str(old)
    with pytest.raises(ValueError):
        audit.verify(value)


def test_standalone_file_spec_import_from_unrelated_directory(tmp_path):
    import subprocess
    code = """
import importlib.util, sys
from pathlib import Path
target = Path(sys.argv[1])
sys.path = [entry for entry in sys.path if Path(entry).resolve() != target.parent]
assert importlib.util.find_spec('verify_cone_whitney_bridge') is None
spec = importlib.util.spec_from_file_location('charged_standalone', target)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
assert module.load()['schema'] == 'oph.whitney_charged_dynamics.v1'
assert module.geometry(2)['vertices'].shape == (13, 3)
"""
    result = subprocess.run([sys.executable, "-c", code, str(Path(audit.__file__).resolve())],
                            cwd=tmp_path, capture_output=True, text=True, encoding="utf-8", check=False)
    assert result.returncode == 0, result.stderr


@pytest.mark.parametrize("field, historical", [
    ("run_id", "whitney-charged-symmetric-2026-09-06-v1"),
    ("source_base_commit", "79b0a4a5bb7242f7ea733ebe502df48f774cf997"),
])
def test_current_dynamics_rejects_historical_identity(packet, field, historical):
    changed = deepcopy(packet)
    changed[field] = historical
    with pytest.raises(ValueError, match="run identity|source base commit"):
        audit.verify(changed)

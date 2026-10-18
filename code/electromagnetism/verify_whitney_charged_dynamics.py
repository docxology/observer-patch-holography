"""Independent full-coordinate audit of the symmetric charged trajectory.

Does not import its producer. Rebuilds oriented geometry and full scalar
Jacobians, evaluates all 68 Euler--Lagrange and 13 Gauss equations, and checks
sample-time defects, energy, quadrature and fixed-step refinement controls.
Acceptance is numerical evidence, not an interval trajectory error bound.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import solve_ivp

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
_cone_spec = importlib.util.spec_from_file_location("charged_dynamics_cone_verifier", HERE/"verify_cone_whitney_bridge.py")
if _cone_spec is None or _cone_spec.loader is None:
    raise RuntimeError("independent cone verifier unavailable")
cone = importlib.util.module_from_spec(_cone_spec)
_cone_spec.loader.exec_module(cone)
OUTPUT = HERE / "runtime/whitney_charged_dynamics_receipt.json"
PINS = {
    "Lean/Screen/SeamCurrentEdge30Moment.lean",
    "Lean/Screen/SeamCurrentCarrierQuotient.lean",
    "Lean/ObserverPatchHolography/CoreAxioms.lean",
    "code/electromagnetism/verify_cone_whitney_bridge.py",
    "code/electromagnetism/whitney_charged_dynamics.py",
    "code/electromagnetism/verify_whitney_charged_dynamics.py",
}
PAIRS = list(itertools.combinations(range(4), 2))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(path=OUTPUT):
    return cone.load(path)


def numeric(value, shape, name):
    def valid(x):
        return all(valid(v) for v in x) if isinstance(x, list) else type(x) in (int, float)
    require(valid(value), name+" numeric types")
    result = np.asarray(value, dtype=float)
    require(result.shape == shape and np.isfinite(result).all(), name+" shape/finiteness")
    return result


def close(value, expected, name, atol=2e-10, rtol=2e-10):
    result = numeric(value, np.shape(expected), name)
    require(np.allclose(result, expected, atol=atol, rtol=rtol), name)
    return result


def integer_sequence(value, expected, name):
    """Discrete indices/count schedules have exact JSON integer semantics."""
    require(isinstance(value, list) and all(type(x) is int for x in value),
            name+" integer types")
    require(value == list(expected), name+" exact values")


def integer_table(value, expected, name):
    require(isinstance(value, list) and len(value) == len(expected), name+" row census")
    for row, reference in zip(value, expected, strict=True):
        integer_sequence(row, reference, name)


@lru_cache(maxsize=4)
def geometry(order=4):
    raw, boundary_edges, faces = cone.source_mesh()
    xyz = np.array([[0.0]*3]+[[float(x) for x in v] for v in raw])
    edges = [(0, i) for i in range(1, 13)]+[(i+1, j+1) for i, j in boundary_edges]
    triangles = [(i+1, j+1, k+1) for i, j, k in faces]
    tetrahedra = [(0,)+t for t in triangles]
    all_faces = [(0, i, j) for i, j in edges[12:]]+triangles
    d = np.zeros((42, 13))
    for e, (i, j) in enumerate(edges):
        d[e, i], d[e, j] = -1, 1
    c = cone.coboundary(edges, all_faces)
    nodes, weights = leggauss(order)
    nodes, weights = (nodes+1)/2, weights/2
    lam, qw = [], []
    for i, j, k in itertools.product(range(order), repeat=3):
        x, y, z = nodes[i], nodes[j], nodes[k]
        lam.append([(1-x)*(1-y)*(1-z), x, (1-x)*y, (1-x)*(1-y)*z])
        qw.append(weights[i]*weights[j]*weights[k]*(1-x)**2*(1-y))
    lam, qw = np.array(lam), np.array(qw)
    elements = []
    mass, stiffness = np.zeros((42, 42)), np.zeros((42, 42))
    for tet in tetrahedra:
        points = xyz[list(tet)]
        inverse = np.linalg.inv(np.column_stack((np.ones(4), points)))
        grad = inverse[1:].T
        determinant = abs(np.linalg.det(points[1:]-points[0]))
        ids, signs = [], []
        for i, j in PAIRS:
            edge = (tet[i], tet[j])
            sign = 1 if edge in edges else -1
            ids.append(edges.index(edge if sign == 1 else edge[::-1]))
            signs.append(sign)
        signs = np.array(signs)
        basis = np.array([lam[:, i, None]*grad[j]-lam[:, j, None]*grad[i]
                          for i, j in PAIRS]).transpose(1, 0, 2)
        curls = np.array([2*np.cross(grad[i], grad[j]) for i, j in PAIRS])
        theta_jac = np.zeros((len(lam), 4, 6))
        grad_theta_jac = np.zeros((4, 6, 3))
        for e, (i, j) in enumerate(PAIRS):
            theta_jac[:, i, e], theta_jac[:, j, e] = lam[:, j], -lam[:, i]
            grad_theta_jac[i, e], grad_theta_jac[j, e] = grad[j], -grad[i]
        w = determinant*qw
        local_m = np.einsum("q,qic,qjc->ij", w, basis, basis)
        local_k = sum(w)*(curls@curls.T)
        mass[np.ix_(ids, ids)] += local_m*signs[:, None]*signs[None, :]
        stiffness[np.ix_(ids, ids)] += local_k*signs[:, None]*signs[None, :]
        elements.append({"tet": np.array(tet), "ids": np.array(ids), "signs": signs,
            "lam": lam, "weights": w, "grad": grad, "basis": basis,
            "curls": curls, "theta_jac": theta_jac, "grad_theta_jac": grad_theta_jac})
    require(np.max(abs(c@d)) == 0 and np.linalg.eigvalsh(mass).min() > 0, "geometry incidence/mass")
    return {"vertices": xyz, "edges": edges, "faces": all_faces,
            "tetrahedra": tetrahedra, "D": d, "C": c, "M": mass,
            "K": stiffness, "elements": elements}


def element_fields(q, velocity, element, charge=0.25, omit_dressing=False):
    """Full fourteen local real-coordinate derivatives at arbitrary fields."""
    tet, ids, signs = element["tet"], element["ids"], element["signs"]
    lam, grad, theta_jac = element["lam"], element["grad"], element["theta_jac"]
    a, av = q[ids]*signs, velocity[ids]*signs
    psi, pv = q[42+tet]+1j*q[55+tet], velocity[42+tet]+1j*velocity[55+tet]
    theta = np.einsum("qie,e->qi", theta_jac, a)
    theta_dot = np.einsum("qie,e->qi", theta_jac, av)
    theta_grad = np.einsum("iec,e->ic", element["grad_theta_jac"], a)
    phase = np.exp(1j*charge*theta)
    dressed = phase*psi
    scalar = np.einsum("qi,qi->q", lam, dressed)
    base = phase*lam
    ja = 1j*charge*np.einsum("qi,qie->qe", lam*dressed, theta_jac)
    jac = np.column_stack((ja, base, 1j*base))
    scalar_dot = np.sum(base*pv, axis=1)+ja@av
    second = np.sum(base*(2j*charge*theta_dot*pv-charge**2*theta_dot**2*psi), axis=1)
    spatial_basis = grad[None, :, :]+1j*charge*lam[:, :, None]*theta_grad[None]
    potential = np.einsum("e,qec->qc", a, element["basis"])
    spatial = np.einsum("qi,qic->qc", dressed, spatial_basis)-1j*charge*potential*scalar[:, None]
    ga = (1j*charge*np.einsum("qi,qie,qic->qec", dressed, theta_jac, spatial_basis)
          +1j*charge*np.einsum("qi,iec->qec", lam*dressed, element["grad_theta_jac"])
          -1j*charge*element["basis"]*scalar[:, None, None]
          -1j*charge*potential[:, None, :]*ja[:, :, None])
    gp = phase[:, :, None]*spatial_basis-1j*charge*potential[:, None, :]*base[:, :, None]
    gjac = np.concatenate((ga, gp, 1j*gp), axis=1)
    if omit_dressing:
        # Plausible wrong model: freeze W(a) when varying/time-differentiating.
        jac[:, :6] = 0
        gjac[:, :6] = -1j*charge*element["basis"]*scalar[:, None, None]
        scalar_dot = np.sum(base*pv, axis=1)
        second = np.zeros_like(second)
    slots = np.r_[ids, 42+tet, 55+tet]
    orientation = np.r_[signs, np.ones(8)]
    return {"scalar": scalar, "scalar_dot": scalar_dot, "spatial": spatial,
            "jacobian": jac*orientation[None, :], "second_velocity": second,
            "spatial_jacobian": gjac*orientation[None, :, None], "slots": slots}


def full_audit(q, velocity, acceleration, mesh=None, omit_dressing=False):
    mesh = geometry() if mesh is None else mesh
    e, m2, g = 0.25, 0.5, 0.25
    residual = np.r_[mesh["M"]@acceleration[:42]+mesh["K"]@q[:42], np.zeros(26)]
    rho = np.zeros(13)
    energy = (velocity[:42]@mesh["M"]@velocity[:42]+q[:42]@mesh["K"]@q[:42])/2
    lagrangian = (velocity[:42]@mesh["M"]@velocity[:42]-q[:42]@mesh["K"]@q[:42])/2
    for element in mesh["elements"]:
        data = element_fields(q, velocity, element, omit_dressing=omit_dressing)
        w, scalar, j, gj = element["weights"], data["scalar"], data["jacobian"], data["spatial_jacobian"]
        slots = data["slots"]
        scalar_acc = j@acceleration[slots]+data["second_velocity"]
        local = 2*np.real(j.conj().T@(w*(scalar_acc+(m2+g*abs(scalar)**2)*scalar)))
        local += 2*np.real(np.einsum("q,qic,qc->i", w, gj.conj(), data["spatial"]))
        residual[slots] += local
        charge_density = 2*e*np.imag(scalar.conj()*data["scalar_dot"])
        rho[element["tet"]] += element["lam"].T@(w*charge_density)
        kinetic = w@abs(data["scalar_dot"])**2
        potential = w@(np.sum(abs(data["spatial"])**2, axis=1)+m2*abs(scalar)**2+g*abs(scalar)**4/2)
        energy += kinetic+potential
        lagrangian += kinetic-potential
    gauss = rho+mesh["D"].T@mesh["M"]@velocity[:42]
    return {"euler_lagrange": residual, "gauss": gauss, "rho_load": rho,
            "energy": float(energy), "lagrangian": float(lagrangian)}


def symmetry_certificate(mesh=None):
    """Enumerate geometric rotations and their signed edge representations."""
    mesh = geometry(2) if mesh is None else mesh
    vertices = mesh["vertices"][1:]
    first = mesh["tetrahedra"][0][1:]
    reference = mesh["vertices"][list(first)].T
    permutations = []
    for tet in mesh["tetrahedra"]:
        for ordered in itertools.permutations(tet[1:]):
            matrix = mesh["vertices"][list(ordered)].T@np.linalg.inv(reference)
            if np.linalg.det(matrix) < 0:
                continue
            require(np.allclose(matrix.T@matrix, np.eye(3), atol=2e-12), "rotation metric")
            moved = vertices@matrix.T
            perm = [0]
            for point in moved:
                distances = np.linalg.norm(vertices-point, axis=1)
                require(distances.min() < 2e-12, "rotation vertex image")
                perm.append(int(distances.argmin())+1)
            require(len(set(perm)) == 13, "rotation bijection")
            permutations.append(perm)
    require(len(permutations) == len({tuple(p) for p in permutations}) == 60, "rotation group census")
    edge_average, node_average = np.zeros((42, 42)), np.zeros((13, 13))
    for perm in permutations:
        for i in range(13):
            node_average[perm[i], i] += 1/60
        for i, (a, b) in enumerate(mesh["edges"]):
            target = (perm[a], perm[b])
            sign = 1 if target in mesh["edges"] else -1
            row = mesh["edges"].index(target if sign == 1 else target[::-1])
            edge_average[row, i] += sign/60
    expected_edge = np.zeros((42, 42)); expected_edge[:12, :12] = 1/12
    expected_node = np.zeros((13, 13)); expected_node[0, 0] = 1; expected_node[1:, 1:] = 1/12
    require(np.allclose(edge_average, expected_edge, atol=2e-12), "signed edge fixed subspace")
    require(np.allclose(node_average, expected_node, atol=2e-12), "nodal fixed subspace")
    return {"proper_rotations": 60, "edge_fixed_dimension": 1, "node_fixed_dimension": 2,
            "real_configuration_fixed_dimension": 5}


def expanded(x):
    return np.r_[np.full(12, x[0]), np.zeros(30), x[1], np.full(12, x[3]), x[2], np.full(12, x[4])]




def check_readouts(recorded, q, velocity, rho, mesh):
    expected = {"rho_load", "centroid_positions", "scalar_at_centroids",
        "covariant_time_derivative_at_centroids", "covariant_spatial_derivative_at_centroids",
        "electric_at_centroids", "magnetic_at_centroids"}
    require(set(recorded) == expected, "readout catalogue")
    close(recorded["rho_load"], rho, "readout charge load")
    positions, scalar, dot, spatial, electric, magnetic = [], [], [], [], [], []
    for element in mesh["elements"]:
        center = dict(element)
        center["lam"] = np.full((1, 4), .25)
        center["basis"] = np.array([[.25*(element["grad"][j]-element["grad"][i]) for i, j in PAIRS]])
        theta = np.zeros((1, 4, 6))
        for edge, (i, j) in enumerate(PAIRS):
            theta[0, i, edge], theta[0, j, edge] = .25, -.25
        center["theta_jac"] = theta
        data = element_fields(q, velocity, center)
        positions.append(mesh["vertices"][element["tet"]].mean(axis=0))
        scalar.append([data["scalar"][0].real, data["scalar"][0].imag])
        dot.append([data["scalar_dot"][0].real, data["scalar_dot"][0].imag])
        field = data["spatial"][0]
        spatial.append(np.column_stack((field.real, field.imag)))
        electric.append(-np.einsum("e,ec->c", velocity[element["ids"]]*element["signs"], center["basis"][0]))
        magnetic.append(np.einsum("e,ec->c", q[element["ids"]]*element["signs"], element["curls"]))
    for name, value in (("centroid_positions", positions), ("scalar_at_centroids", scalar),
            ("covariant_time_derivative_at_centroids", dot), ("covariant_spatial_derivative_at_centroids", spatial),
            ("electric_at_centroids", electric), ("magnetic_at_centroids", magnetic)):
        close(recorded[name], value, "readout "+name)


def independent_rhs(_time, state):
    """One congruent tetrahedron, full Jacobians pulled back to the fixed space.

    This is independent of the producer's one-dimensional phase-cancelled
    formulas and Gauss-Jacobi assembly. Twenty congruent cells have the same
    invariant action. Full-space checks still assemble each cell separately.
    """
    mesh = geometry(4)
    q, v = expanded(state[:5]), expanded(state[5:])
    element = mesh["elements"][0]
    data = element_fields(q, v, element)
    embedding = np.column_stack([expanded(row) for row in np.eye(5)])
    pullback = embedding[data["slots"]]
    j = data["jacobian"]@pullback
    gj = np.einsum("qic,ij->qjc", data["spatial_jacobian"], pullback)
    weights, scalar = 20*element["weights"], data["scalar"]
    metric = 2*np.real(j.conj().T@(weights[:, None]*j))
    metric[0, 0] += float(np.ones(12)@mesh["M"][:12, :12]@np.ones(12))
    force = -2*np.real(j.conj().T@(weights*(data["second_velocity"]+(.5+.25*abs(scalar)**2)*scalar)))
    force -= 2*np.real(np.einsum("q,qic,qc->i", weights, gj.conj(), data["spatial"]))
    return np.r_[state[5:], np.linalg.solve(metric, force)]


def independent_rk4(steps, initial):
    value = initial.copy()
    step = 2/steps
    for _ in range(steps):
        k1 = independent_rhs(0, value)
        k2 = independent_rhs(0, value+step*k1/2)
        k3 = independent_rhs(0, value+step*k2/2)
        k4 = independent_rhs(0, value+step*k3)
        value += step*(k1+2*k2+2*k3+k4)/6
    return value


def verify(packet):
    require(set(packet) == {"schema", "scope", "source_pins", "parameters", "mesh", "metadata",
        "initial_contract", "integrator", "samples", "controls", "run_id", "source_base_commit"}, "receipt schema fields")
    require(packet["run_id"] == "whitney-charged-symmetric-lean435-20261018-v2", "run identity")
    require(packet["source_base_commit"] == "a8ab45b7530fecbac8c06eb19ee8b7e95a7196a2", "source base commit")
    require(packet["schema"] == "oph.whitney_charged_dynamics.v1", "schema")
    require(packet["scope"] == "NUMERICAL_COUPLED_CHARGED_MATTER__SYMMETRIC_SECTOR_OF_FULL_FINITE_ACTION", "scope")
    require(set(packet["source_pins"]) == PINS, "source pin census")
    # Always hash current bytes, including when geometry is already cached.
    for name, digest in packet["source_pins"].items():
        require(hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, "source pin: "+name)
    require(packet["parameters"] == {"e": 0.25, "m_squared": 0.5, "g": 0.25}, "supplied parameters")
    meta = packet["metadata"]
    expected_meta = {
        "action": "0.5 E^T M E -0.5 a^T K a + integral(|Dt Psi|^2-|Dx Psi|^2-m2|Psi|^2-g|Psi|^4/2)",
        "basis": "oriented real Whitney one-forms; potential-dressed nodal complex scalar",
        "charge_sign": "rho_load=2e integral(lambda Im(conj(Psi) DtPsi)); conventional physical charge has opposite sign",
        "complex_encoding": "[real,imaginary]; all scalar coefficients are classical fields, not quantum amplitudes",
        "coordinate_order": "a[42], Re(psi)[13], Im(psi)[13]",
        "embedding": "first 12 radial a=alpha; boundary a=0; one center psi and 12 equal boundary psi",
        "gauge": "temporal phi=0; unwrapped real edge integrals",
        "imports": ["regular cone geometry", "scalar species and action", "charge, mass and quartic coupling", "temporal gauge", "initial data", "numerical evolution and supplied time"],
        "nonclaims": ["no source-selected geometry, clock or matter", "no authenticated observer execution", "no quantum-state evolution", "no spatial convergence or interval-certified trajectory", "no physical measurement or empirical prediction"],
        "observer_history": None, "quantum_state": None,
        "quadrature": "degree at most five after symmetric phase cancellation; four-node Gauss-Jacobi exact in real arithmetic",
        "readout_locations": "one barycentric centroid per tetrahedron in mesh order; each sample has the same supplied time",
        "reduced_order": "alpha, Re(center), Im(center), Re(boundary), Im(boundary)",
        "time": "supplied dimensionless continuous action parameter; not event order or calibrated physical time",
        "units": "dimensionless supplied geometry and couplings; no SI calibration"}
    require(meta == expected_meta, "metadata contract")
    require(packet["initial_contract"] == "a=0; psi=1; psi_dot(center)=3i, psi_dot(boundary)=-i; alpha_dot=e(2+3golden)/10", "initial contract")
    integrator = packet["integrator"]
    require(set(integrator) == {"method", "rtol", "atol", "max_step", "sample_count", "t_span", "function_evaluations"}, "integrator schema")
    require(integrator["method"] == "DOP853" and integrator["rtol"] == 2e-12 and integrator["atol"] == 2e-13 and integrator["max_step"] == .025, "integration method")
    require(type(integrator["function_evaluations"]) is int and 0 < integrator["function_evaluations"] < 10000, "integration evaluation count")
    require(meta["observer_history"] is None and meta["quantum_state"] is None, "absent layers")
    require(meta["coordinate_order"] == "a[42], Re(psi)[13], Im(psi)[13]", "coordinate basis")
    require(meta["gauge"] == "temporal phi=0; unwrapped real edge integrals", "gauge convention")
    require(meta["time"] == "supplied dimensionless continuous action parameter; not event order or calibrated physical time", "clock convention")
    mesh = geometry(4)
    require(set(packet["mesh"]) == {"vertices", "edges", "faces", "tetrahedra"}, "mesh schema")
    close(packet["mesh"]["vertices"], mesh["vertices"], "mesh vertices", atol=1e-14, rtol=1e-14)
    for key in ("edges", "faces", "tetrahedra"):
        integer_table(packet["mesh"][key], mesh[key], "mesh "+key)
    require(type(integrator["sample_count"]) is int and integrator["sample_count"] == 81,
            "integration sample count")
    close(integrator["t_span"], [0, 2], "integration window", atol=0, rtol=0)
    integer_sequence(packet["controls"]["quadrature_orders"], [3, 4, 5], "quadrature orders")
    samples = packet["samples"]
    require(isinstance(samples, list) and len(samples) == 81, "sample census")
    times = np.linspace(0, 2, 81)
    result, ys, accs, energies, loads = [], [], [], [], []
    expected_keys = {"t", "q_reduced", "v_reduced", "acceleration_reduced", "q", "velocity",
        "acceleration", "electric_cochain", "magnetic_cochain", "energy", "lagrangian", "kinetic_energy", "potential_energy", "field_readouts"}
    for n, row in enumerate(samples):
        require(set(row) == expected_keys, "sample schema")
        close(row["t"], times[n], "sample clock", atol=2e-15, rtol=0)
        q = numeric(row["q_reduced"], (5,), "reduced position")
        v = numeric(row["v_reduced"], (5,), "reduced velocity")
        acc = numeric(row["acceleration_reduced"], (5,), "reduced acceleration")
        fq = close(row["q"], expanded(q), "position lift", atol=0, rtol=0)
        fv = close(row["velocity"], expanded(v), "velocity lift", atol=0, rtol=0)
        fa = close(row["acceleration"], expanded(acc), "acceleration lift", atol=0, rtol=0)
        close(row["electric_cochain"], -fv[:42], "electric field", atol=0, rtol=0)
        close(row["magnetic_cochain"], mesh["C"]@fq[:42], "magnetic field", atol=1e-14, rtol=0)
        audit = full_audit(fq, fv, fa, mesh)
        require(max(abs(audit["euler_lagrange"])) < 3e-10, "all full Euler-Lagrange equations")
        require(max(abs(audit["gauss"])) < 3e-10, "all Gauss equations")
        check_readouts(row["field_readouts"], fq, fv, audit["rho_load"], mesh)
        close(row["energy"], audit["energy"], "integrated energy")
        close(row["lagrangian"], audit["lagrangian"], "integrated action density")
        close(row["kinetic_energy"], (audit["energy"]+audit["lagrangian"])/2, "kinetic energy")
        close(row["potential_energy"], (audit["energy"]-audit["lagrangian"])/2, "potential energy")
        ys.append(np.r_[q, v]); accs.append(acc); energies.append(audit["energy"]); loads.append(audit["rho_load"])
        result.append(audit)
    ys, accs, energies, loads = np.array(ys), np.array(accs), np.array(energies), np.array(loads)
    beta = 0.25*(2+3*(1+np.sqrt(5))/2)/10
    initial = np.array([0, 1, 0, 1, 0, beta, 0, 3, 0, -1])
    close(ys[0].tolist(), initial, "charged neutral initial data", atol=1e-14, rtol=0)
    volume_tet = (3+np.sqrt(5))/6
    close(loads[0].tolist(), np.r_[6*.25*volume_tet, np.full(12, -.25*volume_tet/2)], "initial load")
    energy_drift = float(max(abs(energies-energies[0])))
    require(energy_drift < 2e-9, "energy drift")
    # Consecutive pairs of intervals supply actual midpoint states. Simpson
    # defects audit the stored positions AND velocities, separately from the
    # algebraic acceleration residual. This is observed consistency only.
    derivatives = np.column_stack((ys[:, 5:], accs))
    defects = ys[2::2]-ys[:-2:2]-.05/6*(derivatives[:-2:2]+4*derivatives[1::2]+derivatives[2::2])
    temporal_defect = float(np.max(abs(defects)))
    require(temporal_defect < 3e-7, "sample-time consistency")
    controls = packet["controls"]
    require(set(controls) == {"tight_reference", "tight_reference_max_difference", "rk4", "quadrature_orders"}, "controls schema")
    tight = numeric(controls["tight_reference"], (81, 10), "tight reference")
    difference = float(np.max(abs(ys-tight)))
    close(controls["tight_reference_max_difference"], difference, "tight difference", atol=1e-14, rtol=1e-6)
    require(difference < 2e-9, "tight refinement agreement")
    replay_solution = solve_ivp(independent_rhs, (0, 2), initial, method="DOP853",
        t_eval=times, rtol=3e-13, atol=3e-14, max_step=.02)
    require(replay_solution.success, "independent integration completed")
    close(ys.tolist(), replay_solution.y.T, "independent whole-trajectory replay", atol=3e-10, rtol=3e-10)
    independent_difference = float(np.max(abs(ys-replay_solution.y.T)))
    quadrature_difference, underintegration_defect = 0.0, 0.0
    for index in (0, 40, 80):
        row = samples[index]
        q, v, a = (np.array(row[key]) for key in ("q", "velocity", "acceleration"))
        audits = [full_audit(q, v, a, geometry(order)) for order in (3, 4, 5)]
        underintegration_defect = max(underintegration_defect, float(max(abs(audits[0]["euler_lagrange"]))))
        for audit in audits[1:]:
            for key in ("euler_lagrange", "gauss", "energy", "lagrangian"):
                quadrature_difference = max(quadrature_difference, float(np.max(abs(np.asarray(audit[key])-audits[-1][key]))))
    require(quadrature_difference < 3e-10, "exact-degree quadrature agreement")
    require(underintegration_defect > 1e-5, "underintegration negative control")
    require(len(controls["rk4"]) == 3, "RK4 control census")
    errors = []
    for row, steps in zip(controls["rk4"], (80, 160, 320), strict=True):
        require(set(row) == {"steps", "endpoint", "endpoint_max_error"} and type(row["steps"]) is int and row["steps"] == steps, "RK4 schedule")
        endpoint = numeric(row["endpoint"], (10,), "RK4 endpoint")
        replay = independent_rk4(steps, initial)
        close(row["endpoint"], replay, "independent RK4 replay", atol=3e-11, rtol=3e-11)
        error = float(max(abs(endpoint-tight[-1])))
        close(row["endpoint_max_error"], error, "RK4 endpoint error", atol=1e-15, rtol=1e-8)
        errors.append(error)
    require(errors[-1] < 2e-7 and all(10 < errors[i]/errors[i+1] < 25 for i in (0, 1)), "fourth-order refinement evidence")
    omitted = full_audit(np.array(samples[40]["q"]), np.array(samples[40]["velocity"]), np.array(samples[40]["acceleration"]), mesh, omit_dressing=True)
    omitted_defect = float(max(abs(omitted["euler_lagrange"])))
    require(omitted_defect > 1e-3, "missing dressing derivative control")
    symmetry = symmetry_certificate(mesh)
    return {"accepted": True, "samples": 81, "full_equations_per_sample": 68,
        "gauss_equations_per_sample": 13, "symmetry": symmetry,
        "full_euler_max_abs": float(max(max(abs(row["euler_lagrange"])) for row in result)),
        "gauss_max_abs": float(max(max(abs(row["gauss"])) for row in result)),
        "energy_drift": energy_drift, "simpson_defect_max_abs": temporal_defect,
        "quadrature_max_difference": quadrature_difference, "underintegration_euler_defect": underintegration_defect,
        "tight_reference_difference": difference, "independent_replay_difference": independent_difference,
        "rk4_endpoint_errors": errors, "omitted_dressing_euler_defect": omitted_defect,
        "charge_load_change_max_abs": float(np.max(abs(loads-loads[0]))),
        "trajectory_error_status": "observed numerical convergence and residuals; no rigorous trajectory error enclosure",
        "observer_history": False, "quantum_state": False, "physical_continuum": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, default=OUTPUT)
    args = parser.parse_args()
    print(json.dumps(verify(load(args.receipt)), sort_keys=True))

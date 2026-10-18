"""Bounded classical evolution of the actual dressed scalar/Whitney action.

The fixed icosahedral sector has five real coordinates. Finite-group symmetry
lifts its equations to all 68 real temporal-gauge equations; the independent
verifier reconstructs those full equations. No observer readback, physical
clock, quantum state, or spatial-refinement certificate is supplied here.

Run contract (fixed before execution): e=1/4, m^2=1/2, g=1/4, t in [0,2];
DOP853 reference plus fixed-step RK4 at 80,160,320 steps; retain all controls.
The outcome is accepted only by the independent verifier. A failed numerical
or schema check rejects the packet, never promotes a physical claim.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import roots_jacobi

import verify_cone_whitney_bridge as cone

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
OUTPUT = HERE / "runtime/whitney_charged_dynamics_receipt.json"
SCHEMA = "oph.whitney_charged_dynamics.v1"
PINS = (
    "Lean/Screen/SeamCurrentEdge30Moment.lean",
    "Lean/Screen/SeamCurrentCarrierQuotient.lean",
    "Lean/ObserverPatchHolography/CoreAxioms.lean",
    "code/electromagnetism/verify_cone_whitney_bridge.py",
    "code/electromagnetism/whitney_charged_dynamics.py",
    "code/electromagnetism/verify_whitney_charged_dynamics.py",
)
PARAMETERS = {"e": 0.25, "m_squared": 0.5, "g": 0.25}
GOLDEN = (1+np.sqrt(5))/2
VOLUME = 20*GOLDEN**2/3
GRADIENT_SQUARED = 3/(2+3*GOLDEN)
KAPPA = VOLUME*GRADIENT_SQUARED


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       allow_nan=False)+"\n").encode("ascii")


def rule(order=4):
    # The marginal simplex density is 3(1-s)^2 on [0,1]. Four-point
    # Gauss-Jacobi integrates every required polynomial, degree at most five.
    x, w = roots_jacobi(order, 2, 0)
    return (x+1)/2, VOLUME*3*w/8


def reduced(q, velocity, order=4):
    """Exact-degree action integrals, evaluated in floating point."""
    charge, mass, coupling = PARAMETERS["e"], PARAMETERS["m_squared"], PARAMETERS["g"]
    alpha, cr, ci, br, bi = q
    c, b = cr+1j*ci, br+1j*bi
    adot, cv, bv = velocity[0], velocity[1]+1j*velocity[2], velocity[3]+1j*velocity[4]
    s, weights = rule(order)
    rotation = np.exp(1j*charge*alpha)
    phase = np.exp(-1j*charge*alpha*s)
    big_c = rotation*c
    difference = big_c-b
    scalar = phase*(s*big_c+(1-s)*b)
    jacobian = np.column_stack((1j*charge*s*(1-s)*phase*difference,
        phase*s*rotation, 1j*phase*s*rotation, phase*(1-s), 1j*phase*(1-s)))
    second = phase*(s*rotation*(2j*charge*(1-s)*adot*cv
        -charge**2*(1-s)**2*adot**2*c)+(1-s)*(-2j*charge*s*adot*bv
        -charge**2*s**2*adot**2*b))
    scalar_dot = jacobian@velocity
    difference_jacobian = np.array([1j*charge*big_c, rotation, 1j*rotation, -1, -1j])
    metric = 2*np.real(jacobian.conj().T@(weights[:, None]*jacobian))
    metric[0, 0] += KAPPA
    potential_gradient = 2*KAPPA*np.real(difference_jacobian.conj()*difference)
    potential_gradient += 2*np.real(jacobian.conj().T@(weights*(mass+coupling*abs(scalar)**2)*scalar))
    force = -potential_gradient-2*np.real(jacobian.conj().T@(weights*second))
    acceleration = np.linalg.solve(metric, force)
    kinetic = KAPPA*adot**2/2+weights@abs(scalar_dot)**2
    potential = KAPPA*abs(difference)**2+weights@(mass*abs(scalar)**2+coupling*abs(scalar)**4/2)
    return {"acceleration": acceleration, "energy": float(kinetic+potential),
            "lagrangian": float(kinetic-potential), "metric": metric,
            "kinetic": float(kinetic), "potential": float(potential)}


def rhs(_time, y):
    return np.r_[y[5:], reduced(y[:5], y[5:])["acceleration"]]


def initial():
    beta = PARAMETERS["e"]*(2+3*GOLDEN)/10
    return np.array([0, 1, 0, 1, 0, beta, 0, 3, 0, -1], dtype=float)


def rk4(steps):
    step, y = 2/steps, initial()
    for _ in range(steps):
        k1 = rhs(0, y)
        k2 = rhs(0, y+step*k1/2)
        k3 = rhs(0, y+step*k2/2)
        k4 = rhs(0, y+step*k3)
        y = y+step*(k1+2*k2+2*k3+k4)/6
    return y


def mesh_data():
    points, boundary_edges, boundary_faces = cone.source_mesh()
    vertices = [[0.0]*3]+[[float(x) for x in row] for row in points]
    edges = [(0, i) for i in range(1, 13)]+[(i+1, j+1) for i, j in boundary_edges]
    faces = [(i+1, j+1, k+1) for i, j, k in boundary_faces]
    tets = [(0,)+face for face in faces]
    all_faces = [(0, i, j) for i, j in edges[12:]]+faces
    return {"vertices": vertices, "edges": edges, "faces": all_faces, "tetrahedra": tets}


def lift(q, velocity, acceleration):
    def one(x):
        return np.r_[np.full(12, x[0]), np.zeros(30), x[1], np.full(12, x[3]),
                     x[2], np.full(12, x[4])]
    return one(q), one(velocity), one(acceleration)



def readouts(q, velocity, mesh):
    charge = PARAMETERS["e"]
    alpha, c, b = q[0], q[1]+1j*q[2], q[3]+1j*q[4]
    av, cv, bv = velocity[0], velocity[1]+1j*velocity[2], velocity[3]+1j*velocity[4]
    rotation = np.exp(1j*charge*alpha)
    difference = rotation*c-b
    def at(s):
        phase = np.exp(-1j*charge*alpha*s)
        scalar = phase*(s*rotation*c+(1-s)*b)
        dot = phase*(s*rotation*cv+(1-s)*bv+1j*charge*av*s*(1-s)*difference)
        return scalar, dot
    s, weights = rule()
    scalar, dot = at(s)
    density = 2*charge*np.imag(scalar.conj()*dot)
    rho = np.r_[weights@(s*density), np.full(12, weights@((1-s)*density)/12)]
    value, rate = at(.25)
    phase = np.exp(-1j*charge*alpha*.25)
    points, electric, covariant_gradient = [], [], []
    for tet in mesh["tetrahedra"]:
        xyz = np.array(mesh["vertices"])[list(tet)]
        gradient = np.linalg.inv(np.column_stack((np.ones(4), xyz)))[1:, 0]
        points.append(xyz.mean(axis=0).tolist())
        electric.append((av*gradient).tolist())
        field = phase*difference*gradient
        covariant_gradient.append(np.column_stack((field.real, field.imag)).tolist())
    return {"rho_load": rho.tolist(), "centroid_positions": points,
        "scalar_at_centroids": [[float(value.real), float(value.imag)]]*20,
        "covariant_time_derivative_at_centroids": [[float(rate.real), float(rate.imag)]]*20,
        "covariant_spatial_derivative_at_centroids": covariant_gradient,
        "electric_at_centroids": electric, "magnetic_at_centroids": [[0.0]*3]*20}


def build():
    times = np.linspace(0, 2, 81)
    solution = solve_ivp(rhs, (0, 2), initial(), method="DOP853", t_eval=times,
                         rtol=2e-12, atol=2e-13, max_step=0.025)
    if not solution.success:
        raise ValueError("reference integration failed")
    tighter = solve_ivp(rhs, (0, 2), initial(), method="DOP853", t_eval=times,
                       rtol=3e-14, atol=3e-15, max_step=0.0125)
    if not tighter.success:
        raise ValueError("tight integration failed")
    mesh = mesh_data()
    records = []
    for time, state in zip(times, solution.y.T, strict=True):
        q, v = state[:5], state[5:]
        dynamics = reduced(q, v)
        full_q, full_v, full_acc = lift(q, v, dynamics["acceleration"])
        records.append({"t": float(time), "q_reduced": q.tolist(), "v_reduced": v.tolist(),
            "acceleration_reduced": dynamics["acceleration"].tolist(),
            "q": full_q.tolist(), "velocity": full_v.tolist(), "acceleration": full_acc.tolist(),
            "electric_cochain": (-full_v[:42]).tolist(), "magnetic_cochain": [0.0]*50,
            "energy": dynamics["energy"], "lagrangian": dynamics["lagrangian"],
            "kinetic_energy": dynamics["kinetic"], "potential_energy": dynamics["potential"],
            "field_readouts": readouts(q, v, mesh)})
    controls = []
    endpoint = tighter.y[:, -1]
    for steps in (80, 160, 320):
        value = rk4(steps)
        controls.append({"steps": steps, "endpoint": value.tolist(),
                         "endpoint_max_error": float(max(abs(value-endpoint)))})
    packet = {"schema": SCHEMA, "run_id": "whitney-charged-symmetric-lean435-20261018-v2",
        "source_base_commit": "a8ab45b7530fecbac8c06eb19ee8b7e95a7196a2",
        "scope": "NUMERICAL_COUPLED_CHARGED_MATTER__SYMMETRIC_SECTOR_OF_FULL_FINITE_ACTION",
        "source_pins": {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in PINS},
        "parameters": PARAMETERS, "mesh": mesh,
        "metadata": {"coordinate_order": "a[42], Re(psi)[13], Im(psi)[13]",
            "reduced_order": "alpha, Re(center), Im(center), Re(boundary), Im(boundary)",
            "embedding": "first 12 radial a=alpha; boundary a=0; one center psi and 12 equal boundary psi",
            "basis": "oriented real Whitney one-forms; potential-dressed nodal complex scalar",
            "gauge": "temporal phi=0; unwrapped real edge integrals",
            "time": "supplied dimensionless continuous action parameter; not event order or calibrated physical time",
            "units": "dimensionless supplied geometry and couplings; no SI calibration",
            "action": "0.5 E^T M E -0.5 a^T K a + integral(|Dt Psi|^2-|Dx Psi|^2-m2|Psi|^2-g|Psi|^4/2)",
            "charge_sign": "rho_load=2e integral(lambda Im(conj(Psi) DtPsi)); conventional physical charge has opposite sign",
            "quadrature": "degree at most five after symmetric phase cancellation; four-node Gauss-Jacobi exact in real arithmetic",
            "observer_history": None, "quantum_state": None,
            "complex_encoding": "[real,imaginary]; all scalar coefficients are classical fields, not quantum amplitudes",
            "readout_locations": "one barycentric centroid per tetrahedron in mesh order; each sample has the same supplied time",
            "imports": ["regular cone geometry", "scalar species and action", "charge, mass and quartic coupling", "temporal gauge", "initial data", "numerical evolution and supplied time"],
            "nonclaims": ["no source-selected geometry, clock or matter", "no authenticated observer execution", "no quantum-state evolution", "no spatial convergence or interval-certified trajectory", "no physical measurement or empirical prediction"]},
        "initial_contract": "a=0; psi=1; psi_dot(center)=3i, psi_dot(boundary)=-i; alpha_dot=e(2+3golden)/10",
        "integrator": {"method": "DOP853", "rtol": 2e-12, "atol": 2e-13, "max_step": 0.025,
            "sample_count": 81, "t_span": [0, 2], "function_evaluations": solution.nfev},
        "samples": records,
        "controls": {"tight_reference": tighter.y.T.tolist(),
            "tight_reference_max_difference": float(np.max(abs(solution.y-tighter.y))),
            "rk4": controls, "quadrature_orders": [3, 4, 5]}}
    return json.loads(canonical(packet))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    packet = build()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(canonical(packet))
    print(json.dumps({"receipt": str(args.output), "samples": len(packet["samples"]),
        "tight_max_difference": packet["controls"]["tight_reference_max_difference"],
        "rk4_errors": [x["endpoint_max_error"] for x in packet["controls"]["rk4"]]}, sort_keys=True))

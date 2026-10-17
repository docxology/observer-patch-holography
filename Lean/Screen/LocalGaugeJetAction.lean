module
public import WeylYukawaConventions
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-!
# Local gauge jet identities

The inhomogeneous connection variation cancels derivatives of the gauge
parameter. Symmetry of the second parameter jet yields curvature covariance.
These identities hold in an associative ring and do not commute fermionic
factors. They supply algebraic ingredients for the separately analytic local
Grassmann action, not a formalization of spacetime, Spin, integration, the full
Standard Model action or a source-selected connection.
-/

namespace OPH.LocalGaugeJetAction

variable {R : Type*} [Ring R]

def bracket (x y : R) : R := x*y-y*x

def connectionVariation (θ dθ A : R) : R := -dθ+bracket θ A

def covariantJet (A ψ dψ : R) : R := dψ+A*ψ

def curvatureJet (A B dA dB : R) : R := dA-dB+bracket A B

/-- The derivative of the local parameter is retained and cancels. -/
theorem covariant_first_jet (θ dθ A ψ dψ : R) :
    dθ*ψ+θ*dψ+connectionVariation θ dθ A*ψ+A*(θ*ψ) =
      θ*covariantJet A ψ dψ := by
  dsimp [connectionVariation, bracket, covariantJet]
  noncomm_ring

/-- Both derivative orders use the same second parameter jet. -/
theorem curvature_second_jet (θ dθ eθ ddθ A B dA dB : R) :
    (-ddθ+bracket dθ B+bracket θ dA) -
      (-ddθ+bracket eθ A+bracket θ dB) +
      bracket (connectionVariation θ dθ A) B +
      bracket A (connectionVariation θ eθ B) =
        bracket θ (curvatureJet A B dA dB) := by
  dsimp [connectionVariation, bracket, curvatureJet]
  noncomm_ring

/-- An additive cyclic trace annihilates the quadratic curvature variation. -/
theorem quadratic_trace_ward {S : Type*} [AddCommGroup S]
    (τ : R →+ S) (cyclic : ∀ x y : R, τ (x*y) = τ (y*x))
    (θ F : R) : τ (bracket θ F*F+F*bracket θ F) = 0 := by
  have h : bracket θ F*F+F*bracket θ F = θ*(F*F)-(F*F)*θ := by
    dsimp [bracket]
    noncomm_ring
  rw [h, map_sub, cyclic θ (F*F), sub_self]

/-- With anticommuting components the antisymmetric spin contraction doubles,
rather than vanishes as it would for commuting scalar replacements. -/
theorem anticommuting_spin_pair (x y : R) (h : y*x = -(x*y)) :
    x*y-y*x = (2 : R)*(x*y) := by
  rw [h]
  noncomm_ring

/-- Omitting the connection's derivative term fails even in a scalar fixture. -/
theorem missing_parameter_derivative_control :
    (1 : ℤ)*1 + 0*0 + bracket 0 0*1 + 0*(0*1) ≠
      0*covariantJet 0 1 0 := by
  norm_num [bracket, covariantJet]

#print axioms covariant_first_jet
#print axioms curvature_second_jet
#print axioms quadratic_trace_ward
#print axioms anticommuting_spin_pair

end OPH.LocalGaugeJetAction

module
public import Mathlib.Tactic

@[expose] public section

/-!
# Cartan normalization and local Gauss-preserving subflows

These identities support the analytic local classical reduction. Spacetime,
the full Euler--Lagrange system, logarithmic plaquette chart, source family,
quantization and numerical roundoff are not formalized here.
-/

namespace OPH.CartanScalarReduction

noncomputable section

def d (k₁ k₂ : ℝ) := (2*k₁+k₂)/(8*k₁*k₂)
def w₁ (k₁ k₂ : ℝ) := 4*k₁/(2*k₁+k₂)
def w₂ (k₁ k₂ : ℝ) := 2*k₂/(2*k₁+k₂)

/-- Unit scalar charge and the two full Cartan equations have one coefficient. -/
theorem cartan_normalization (k₁ k₂ : ℝ) (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    (w₁ k₁ k₂ + w₂ k₁ k₂)/2 = 1 ∧
      k₂*w₁ k₁ k₂ = 1/(2*d k₁ k₂) ∧
      2*k₁*w₂ k₁ k₂ = 1/(2*d k₁ k₂) := by
  have hn : 2*k₁+k₂ ≠ 0 := ne_of_gt (by positivity)
  have h1 : k₁ ≠ 0 := ne_of_gt h₁
  have h2 : k₂ ≠ 0 := ne_of_gt h₂
  dsimp [w₁, w₂, d]
  constructor
  · field_simp
    ring
  constructor <;> field_simp <;> ring

/-- The restricted kinetic coefficient includes both trace normalizations. -/
theorem restricted_kinetic (k₁ k₂ : ℝ) (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    k₂*(w₁ k₁ k₂)^2 + 2*k₁*(w₂ k₁ k₂)^2 = 1/d k₁ k₂ := by
  have hn : 2*k₁+k₂ ≠ 0 := ne_of_gt (by positivity)
  have h1 : k₁ ≠ 0 := ne_of_gt h₁
  have h2 : k₂ ≠ 0 := ne_of_gt h₂
  dsimp [w₁, w₂, d]
  field_simp
  ring

def charge (x y px py : ℝ) := 2*(x*py-y*px)
def current (c u v xi yi xj yj : ℝ) :=
  -2*c*(xi*(v*xj+u*yj)-yi*(u*xj-v*yj))

/-- Each edge potential kick preserves both endpoint Gauss constraints.
The unit-phase hypothesis is unnecessary for this algebraic cancellation. -/
theorem edge_kick_gauss (c u v h xi yi xj yj pix piy pjx pjy P : ℝ) :
    charge xi yi (pix+h*c*(u*xj-v*yj-xi)) (piy+h*c*(v*xj+u*yj-yi)) +
      (P+h*current c u v xi yi xj yj) = charge xi yi pix piy + P ∧
    charge xj yj (pjx+h*c*(u*xi+v*yi-xj)) (pjy+h*c*(-v*xi+u*yi-yj)) -
      (P+h*current c u v xi yi xj yj) = charge xj yj pjx pjy - P := by
  dsimp [charge, current]
  constructor <;> ring

/-- Scalar kinetic drift leaves the vertex charge unchanged. -/
theorem scalar_drift_charge (x y px py h m : ℝ) :
    charge (x+h*px/m) (y+h*py/m) px py = charge x y px py := by
  dsimp [charge]
  ring

/-- A real onsite potential kick leaves the vertex charge unchanged. -/
theorem onsite_kick_charge (x y px py h r : ℝ) :
    charge x y (px-h*r*x) (py-h*r*y) = charge x y px py := by
  dsimp [charge]
  ring

#print axioms cartan_normalization
#print axioms restricted_kinetic
#print axioms edge_kick_gauss
#print axioms scalar_drift_charge
#print axioms onsite_kick_charge

end
end OPH.CartanScalarReduction

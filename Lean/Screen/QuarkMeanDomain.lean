module
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace OPH.QuarkMeanDomain

/-!
# Domain of the rational quark-mean ray interface

For a positive ray parameter, the auxiliary factors below are well defined,
but positivity of the parameter does not ensure a nonzero mean denominator.
Two disjoint positive intervals contain zeros of that denominator. These are
domain restrictions of this rational interface, not a physical exclusion.
Lean's totalized division at zero is not interpreted as a defined ray mean.
-/

def rho (r : ℝ) : ℝ := 3 / (2 + r)

def rayCoordinate (r : ℝ) : ℝ := (r - 1) / (r + 1)

/-- The bracket in the mean formula `B = 1 / (2 * denominator r)`. -/
def denominator (r : ℝ) : ℝ :=
  1 - rayCoordinate r ^ 2 - rayCoordinate r ^ 2 / (1 + rho r)

def polePolynomial (r : ℝ) : ℝ := -r ^ 3 + 4 * r ^ 2 + 23 * r - 2

/-- The remaining singularities are exactly controlled by this cubic. -/
theorem denominator_identity (r : ℝ) (hr : 0 < r) :
    denominator r = polePolynomial r / ((r + 1) ^ 2 * (r + 5)) := by
  have h1 : r + 1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : 2 + r ≠ 0 := ne_of_gt (by linarith)
  have h5 : r + 5 ≠ 0 := ne_of_gt (by linarith)
  have haux : 1 + 3 / (2 + r) = (r + 5) / (2 + r) := by
    field_simp
    ring
  unfold denominator rayCoordinate rho polePolynomial
  rw [haux]
  field_simp
  ring

/-- Domain condition for the full denominator of `B`, including its factor 2. -/
theorem mean_denominator_ne_zero_iff (r : ℝ) (hr : 0 < r) :
    2 * denominator r ≠ 0 ↔ polePolynomial r ≠ 0 := by
  rw [denominator_identity r hr]
  have hfactor : (r + 1) ^ 2 * (r + 5) ≠ 0 := by positivity
  simp [hfactor]

/-- The reciprocal mean excludes at least these two distinct positive
parameters. The proof brackets actual zeros, rather than inferring a pole
from a sampled floating-point sign or from totalized division. -/
theorem two_positive_singularities :
    ∃ a b : ℝ, 2 / 25 < a ∧ a < 9 / 100 ∧
      71 / 10 < b ∧ b < 36 / 5 ∧
      denominator a = 0 ∧ denominator b = 0 := by
  have hcont : Continuous polePolynomial := by unfold polePolynomial; fun_prop
  have ha_sign : (0 : ℝ) ∈ Set.Ioo (polePolynomial (2 / 25))
      (polePolynomial (9 / 100)) := by
    constructor <;> norm_num [polePolynomial]
  have hb_sign : (0 : ℝ) ∈ Set.Ioo (polePolynomial (36 / 5))
      (polePolynomial (71 / 10)) := by
    constructor <;> norm_num [polePolynomial]
  obtain ⟨a, ha, hpa⟩ := intermediate_value_Ioo
    (show (2 : ℝ) / 25 ≤ 9 / 100 by norm_num) hcont.continuousOn ha_sign
  obtain ⟨b, hb, hpb⟩ := intermediate_value_Ioo'
    (show (71 : ℝ) / 10 ≤ 36 / 5 by norm_num) hcont.continuousOn hb_sign
  refine ⟨a, b, ha.1, ha.2, hb.1, hb.2, ?_, ?_⟩
  · rw [denominator_identity a (lt_trans (by norm_num) ha.1), hpa, zero_div]
  · rw [denominator_identity b (lt_trans (by norm_num) hb.1), hpb, zero_div]

end OPH.QuarkMeanDomain

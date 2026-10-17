module
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace OPH.MagneticMatterStability

/-!
# Cubic stability for real or complex magnetic matter

These norm estimates apply to the cubic nonlinearity of the supplied
defocusing scalar equation, including complex fields viewed as real normed
spaces. The spatial Sobolev embedding, Ritz projection and continuum energy
argument are analytic hypotheses and proofs in the accompanying paper.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cubic (x : E) : E := (‖x‖ ^ 2 : ℝ) • x

omit [NormedSpace ℝ E] in
theorem norm_square_difference_le (x y : E) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  calc
    _ = |‖x‖ - ‖y‖| * (‖x‖ + ‖y‖) := by
      rw [show ‖x‖ ^ 2 - ‖y‖ ^ 2 = (‖x‖ - ‖y‖) * (‖x‖ + ‖y‖) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y))]
    _ ≤ ‖x - y‖ * (‖x‖ + ‖y‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le x y)
        (add_nonneg (norm_nonneg x) (norm_nonneg y))
    _ = _ := mul_comm _ _

theorem norm_cubic_difference_le (x y : E) :
    ‖cubic x - cubic y‖ ≤
      (3 / 2 : ℝ) * (‖x‖ ^ 2 + ‖y‖ ^ 2) * ‖x - y‖ := by
  have hsplit : cubic x - cubic y =
      (‖x‖ ^ 2 : ℝ) • (x - y) + (‖x‖ ^ 2 - ‖y‖ ^ 2 : ℝ) • y := by
    unfold cubic
    module
  have hbound : ‖cubic x - cubic y‖ ≤
      ‖x‖ ^ 2 * ‖x - y‖ + (‖x‖ + ‖y‖) * ‖x - y‖ * ‖y‖ := by
    rw [hsplit]
    calc
      _ ≤ ‖(‖x‖ ^ 2 : ℝ) • (x - y)‖ +
          ‖(‖x‖ ^ 2 - ‖y‖ ^ 2 : ℝ) • y‖ := norm_add_le _ _
      _ = ‖x‖ ^ 2 * ‖x - y‖ + |‖x‖ ^ 2 - ‖y‖ ^ 2| * ‖y‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
      _ ≤ _ := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (norm_square_difference_le x y) (norm_nonneg y))
  have hnonneg : 0 ≤ (‖x‖ - ‖y‖) ^ 2 * ‖x - y‖ :=
    mul_nonneg (sq_nonneg _) (norm_nonneg _)
  nlinarith

theorem norm_cubic_difference_on_ball (R : ℝ) (x y : E)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖cubic x - cubic y‖ ≤ 3 * R ^ 2 * ‖x - y‖ := by
  have hR : 0 ≤ R := le_trans (norm_nonneg x) hx
  have hx2 : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg x]
  have hy2 : ‖y‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg y]
  calc
    _ ≤ (3 / 2 : ℝ) * (‖x‖ ^ 2 + ‖y‖ ^ 2) * ‖x - y‖ :=
      norm_cubic_difference_le x y
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)

#print axioms norm_cubic_difference_le
#print axioms norm_cubic_difference_on_ball

end OPH.MagneticMatterStability

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact algebra for count clocks

These lemmas certify the finite positive-root comparison and scale
cancellation used by the analytic count-clock theorem. They do not formalize
the source count-volume limit, Lorentzian volume formula or curve limit.
-/
namespace OPH.SourceCountClock

/-- Fourth powers reflect order on the nonnegative half-line. -/
theorem fourth_power_order {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 4 ≤ y ^ 4 ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hn
    have hxy : y < x := lt_of_not_ge hn
    have hp : y ^ 4 < x ^ 4 := pow_lt_pow_left₀ hxy hy (by norm_num)
    linarith
  · intro h
    exact pow_le_pow_left₀ hx h 4

/-- A positive fourth-root representation is unique. -/
theorem fourth_root_unique {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 4 = y ^ 4) : x = y := by
  exact le_antisymm ((fourth_power_order hx hy).mp h.le)
    ((fourth_power_order hy hx).mp h.ge)

/-- A common positive event weight cancels from a count ratio. -/
theorem common_weight_cancels (w n m : ℝ) (hw : 0 < w) :
    (w * n) / (w * m) = n / m := by
  exact mul_div_mul_left n m (ne_of_gt hw)

/-- Interval division for the true positive volumes of two diamonds. -/
theorem volume_ratio_enclosure {A B EI EJ V W : ℝ}
    (hV : 0 ≤ V) (hW : 0 < W) (hden : EJ < B)
    (hVI : A - EI ≤ V) (hVA : V ≤ A + EI)
    (hWI : B - EJ ≤ W) (hWA : W ≤ B + EJ) :
    max 0 (A - EI) / (B + EJ) ≤ V / W ∧
      V / W ≤ (A + EI) / (B - EJ) := by
  have hlo : max 0 (A - EI) ≤ V := max_le hV hVI
  have hbm : 0 < B - EJ := by linarith
  have hua : 0 ≤ A + EI := le_trans hV hVA
  constructor
  · exact div_le_div₀ hV hlo hW hWA
  · exact div_le_div₀ hua hVA hbm hWI

/-- Fourth-power enclosures imply clock enclosures without root numerics. -/
theorem clock_enclosure {lo clock hi : ℝ} (hlo : 0 ≤ lo)
    (hc : 0 ≤ clock) (hhi : 0 ≤ hi)
    (hleft : lo ^ 4 ≤ clock ^ 4) (hright : clock ^ 4 ≤ hi ^ 4) :
    lo ≤ clock ∧ clock ≤ hi :=
  ⟨(fourth_power_order hlo hc).mp hleft,
    (fourth_power_order hc hhi).mp hright⟩

end OPH.SourceCountClock

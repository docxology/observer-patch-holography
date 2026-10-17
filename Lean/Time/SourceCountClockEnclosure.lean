module
public import Time.SourceCountClock
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-!
# Finite enclosure of the count clock

INPUTS.  Two weighted interval counts `A = w N` and `B = w M` with a common
positive event weight `w`, two true diamond volumes `V_I` and `V_J` with
`V_J > 0`, independently justified error bounds `|A - V_I| ≤ E_I` and
`|B - V_J| ≤ E_J` with `B > E_J`, and two proper-time separations whose
fourth powers stand in the volume ratio, `τ_I⁴ / τ_J⁴ = V_I / V_J`.  The
fourth root is the real power `x ^ (1 / 4)`.

WHAT IS PROVED.  The finite clock enclosure proposition of the count-clock
section:
`((A - E_I)₊ / (B + E_J)) ^ (1/4) ≤ τ_I / τ_J ≤ ((A + E_I) / (B - E_J)) ^ (1/4)`
(`finite_clock_enclosure`), its count form with `N`, `M` and the errors
`E_I / w`, `E_J / w` (`finite_clock_enclosure_counts`), and the relative-error
form: for `A = V_I (1 + d_I)`, `B = V_J (1 + d_J)` with `|d_I| ≤ η_I < 1` and
`|d_J| ≤ η_J < 1`, the measured clock `(A / B) ^ (1/4)` divided by the exact
ratio `τ_I / τ_J` lies in
`[((1 - η_I) / (1 + η_J)) ^ (1/4), ((1 + η_I) / (1 - η_J)) ^ (1/4)]`
(`relative_error_enclosure`).  The interval and root lemmas of
`Time/SourceCountClock.lean` are the ingredients.

NOT CLAIMED.  The volume error bounds are inputs: counts alone do not supply
them, and the count-volume limit, the Lorentzian volume formula and the
curve limit are analytic statements in the paper.  No physical clock is
identified, no population is selected by native repair, and no manifold is
reconstructed.
-/

namespace OPH.SourceCountClockEnclosure

open OPH.SourceCountClock

/-- The fourth root as a real power. -/
noncomputable def fourthRoot (x : ℝ) : ℝ := x ^ ((1 : ℝ) / 4)

theorem fourthRoot_pow_four {x : ℝ} (hx : 0 ≤ x) : fourthRoot (x ^ 4) = x := by
  unfold fourthRoot
  rw [show ((1 : ℝ) / 4) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast hx (by norm_num)

theorem fourthRoot_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    fourthRoot x ≤ fourthRoot y :=
  Real.rpow_le_rpow hx hxy (by norm_num)

/-- Finite clock enclosure: the true proper-time ratio lies between the
fourth roots of the two interval quotients. -/
theorem finite_clock_enclosure {A B VI VJ EI EJ τI τJ : ℝ}
    (hVI : 0 ≤ VI) (hVJ : 0 < VJ) (hden : EJ < B)
    (hI : |A - VI| ≤ EI) (hJ : |B - VJ| ≤ EJ)
    (hτI : 0 ≤ τI) (hτJ : 0 < τJ)
    (hratio : τI ^ 4 / τJ ^ 4 = VI / VJ) :
    fourthRoot (max 0 (A - EI) / (B + EJ)) ≤ τI / τJ ∧
      τI / τJ ≤ fourthRoot ((A + EI) / (B - EJ)) := by
  have hI' := abs_le.mp hI
  have hJ' := abs_le.mp hJ
  have hEJ : 0 ≤ EJ := le_trans (abs_nonneg _) hJ
  obtain ⟨hlo, hhi⟩ := volume_ratio_enclosure (A := A) (B := B) (EI := EI) (EJ := EJ)
    hVI hVJ hden (by linarith [hI'.2]) (by linarith [hI'.1])
    (by linarith [hJ'.2]) (by linarith [hJ'.1])
  have hq : (τI / τJ) ^ 4 = VI / VJ := by
    rw [div_pow]
    exact hratio
  have hτ : 0 ≤ τI / τJ := div_nonneg hτI hτJ.le
  have hlo0 : 0 ≤ max 0 (A - EI) / (B + EJ) :=
    div_nonneg (le_max_left _ _) (by linarith)
  rw [← hq] at hlo hhi
  constructor
  · calc fourthRoot (max 0 (A - EI) / (B + EJ))
        ≤ fourthRoot ((τI / τJ) ^ 4) := fourthRoot_mono hlo0 hlo
      _ = τI / τJ := fourthRoot_pow_four hτ
  · calc τI / τJ = fourthRoot ((τI / τJ) ^ 4) := (fourthRoot_pow_four hτ).symm
      _ ≤ fourthRoot ((A + EI) / (B - EJ)) := fourthRoot_mono (pow_nonneg hτ 4) hhi

/-- The same enclosure in count form: counts `N`, `M`, weight `w`, errors
`E_I / w` and `E_J / w`. -/
theorem finite_clock_enclosure_counts {w N M VI VJ EI EJ τI τJ : ℝ} (hw : 0 < w)
    (hVI : 0 ≤ VI) (hVJ : 0 < VJ) (hden : EJ < w * M)
    (hI : |w * N - VI| ≤ EI) (hJ : |w * M - VJ| ≤ EJ)
    (hτI : 0 ≤ τI) (hτJ : 0 < τJ)
    (hratio : τI ^ 4 / τJ ^ 4 = VI / VJ) :
    fourthRoot (max 0 (N - EI / w) / (M + EJ / w)) ≤ τI / τJ ∧
      τI / τJ ≤ fourthRoot ((N + EI / w) / (M - EJ / w)) := by
  have h := finite_clock_enclosure hVI hVJ hden hI hJ hτI hτJ hratio
  have hw0 : w ≠ 0 := hw.ne'
  have e1 : max 0 (w * N - EI) / (w * M + EJ) = max 0 (N - EI / w) / (M + EJ / w) := by
    have a1 : w * N - EI = w * (N - EI / w) := by
      field_simp
    have a2 : w * M + EJ = w * (M + EJ / w) := by
      field_simp
    have a3 : max 0 (w * (N - EI / w)) = w * max 0 (N - EI / w) := by
      rw [mul_max_of_nonneg _ _ hw.le, mul_zero]
    rw [a1, a2, a3, common_weight_cancels _ _ _ hw]
  have e2 : (w * N + EI) / (w * M - EJ) = (N + EI / w) / (M - EJ / w) := by
    have a1 : w * N + EI = w * (N + EI / w) := by
      field_simp
    have a2 : w * M - EJ = w * (M - EJ / w) := by
      field_simp
    rw [a1, a2, common_weight_cancels _ _ _ hw]
  rw [e1, e2] at h
  exact h

/-- Relative volume errors: the measured clock over the exact ratio. -/
theorem relative_error_enclosure {VI VJ dI dJ ηI ηJ τI τJ : ℝ}
    (hdI : |dI| ≤ ηI) (hηI : ηI < 1) (hdJ : |dJ| ≤ ηJ) (hηJ : ηJ < 1)
    (hτI : 0 < τI) (hτJ : 0 < τJ)
    (hratio : τI ^ 4 / τJ ^ 4 = VI / VJ) :
    fourthRoot ((1 - ηI) / (1 + ηJ))
        ≤ fourthRoot ((VI * (1 + dI)) / (VJ * (1 + dJ))) / (τI / τJ) ∧
      fourthRoot ((VI * (1 + dI)) / (VJ * (1 + dJ))) / (τI / τJ)
        ≤ fourthRoot ((1 + ηI) / (1 - ηJ)) := by
  have hdI' := abs_le.mp hdI
  have hdJ' := abs_le.mp hdJ
  have h1I : 0 < 1 + dI := by linarith
  have h1J : 0 < 1 + dJ := by linarith
  have hq : (τI / τJ) ^ 4 = VI / VJ := by
    rw [div_pow]
    exact hratio
  have hτ : 0 < τI / τJ := div_pos hτI hτJ
  have hfac : (VI * (1 + dI)) / (VJ * (1 + dJ)) = (τI / τJ) ^ 4 * ((1 + dI) / (1 + dJ)) := by
    rw [hq, div_mul_div_comm]
  have hroot : fourthRoot ((VI * (1 + dI)) / (VJ * (1 + dJ))) / (τI / τJ)
      = fourthRoot ((1 + dI) / (1 + dJ)) := by
    rw [hfac]
    have hsplit : fourthRoot ((τI / τJ) ^ 4 * ((1 + dI) / (1 + dJ)))
        = fourthRoot ((τI / τJ) ^ 4) * fourthRoot ((1 + dI) / (1 + dJ)) := by
      unfold fourthRoot
      exact Real.mul_rpow (pow_nonneg hτ.le 4) (div_nonneg h1I.le h1J.le)
    rw [hsplit, fourthRoot_pow_four hτ.le, mul_div_cancel_left₀ _ hτ.ne']
  rw [hroot]
  constructor
  · exact fourthRoot_mono (div_nonneg (by linarith) (by linarith))
      (div_le_div₀ h1I.le (by linarith) h1J (by linarith))
  · exact fourthRoot_mono (div_nonneg h1I.le h1J.le)
      (div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith))

#print axioms finite_clock_enclosure
#print axioms finite_clock_enclosure_counts
#print axioms relative_error_enclosure

-- Time/SourceCountClock.lean is byte-pinned by its source-count-clock receipt,
-- so the axiom audit of its five public theorems sits here, in the first
-- module that imports it.
#print axioms OPH.SourceCountClock.fourth_power_order
#print axioms OPH.SourceCountClock.fourth_root_unique
#print axioms OPH.SourceCountClock.common_weight_cancels
#print axioms OPH.SourceCountClock.volume_ratio_enclosure
#print axioms OPH.SourceCountClock.clock_enclosure

end OPH.SourceCountClockEnclosure

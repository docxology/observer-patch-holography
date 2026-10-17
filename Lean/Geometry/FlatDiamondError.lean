module
public import Geometry.FlatDiamondVolume
public import Geometry.SourcePopulationQuadrature

@[expose] public section

set_option autoImplicit false

namespace OPH.FlatDiamondError

open MeasureTheory Set Real
open OPH.FlatDiamondVolume OPH.SourcePopulationQuadrature
open scoped BigOperators

noncomputable section

/-- The actual cubic ball-volume function has the advertised shell modulus. -/
theorem radial_shell_bound {r s R : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrR : r ≤ R) (hsR : s ≤ R) :
    |(4 * Real.pi / 3) * r ^ 3 - (4 * Real.pi / 3) * s ^ 3| ≤
      4 * Real.pi * R ^ 2 * |r - s| := by
  have hR : 0 ≤ R := hr.trans hrR
  have hsum0 : 0 ≤ r ^ 2 + r * s + s ^ 2 := by positivity
  have hsum : r ^ 2 + r * s + s ^ 2 ≤ 3 * R ^ 2 := by
    nlinarith [pow_le_pow_left₀ hr hrR 2, pow_le_pow_left₀ hs hsR 2,
      mul_le_mul hrR hsR hs hR]
  rw [← mul_sub, show r ^ 3 - s ^ 3 = (r - s) * (r ^ 2 + r * s + s ^ 2) by ring,
    abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * Real.pi / 3),
    abs_of_nonneg hsum0]
  nlinarith [mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (show 0 ≤ 4 * Real.pi / 3 by positivity) (abs_nonneg (r - s)))]

theorem sectionVolume_lipschitz {c T s t : ℝ} (hc : 0 ≤ c)
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    |sectionVolume c T s - sectionVolume c T t| ≤ Real.pi * c ^ 3 * T ^ 2 * |s - t| := by
  have hmin (u : ℝ) (hu : u ∈ Icc 0 T) :
      0 ≤ c * min u (T - u) ∧ c * min u (T - u) ≤ c * T / 2 := by
    refine ⟨mul_nonneg hc (le_min hu.1 (sub_nonneg.mpr hu.2)), ?_⟩
    have hm : min u (T - u) ≤ T / 2 := by
      linarith [min_le_left u (T - u), min_le_right u (T - u)]
    nlinarith [mul_le_mul_of_nonneg_left hm hc]
  have hd : |min s (T - s) - min t (T - t)| ≤ |s - t| := by
    have hh := abs_min_sub_min_le_max s (T - s) t (T - t)
    have he : |(T - s) - (T - t)| = |s - t| := by
      rw [show (T - s) - (T - t) = -(s - t) by ring, abs_neg]
    simpa only [he, max_self] using hh
  have hdist : |c * min s (T - s) - c * min t (T - t)| ≤ c * |s - t| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hd hc
  calc
    _ ≤ 4 * Real.pi * (c * T / 2) ^ 2 *
        |c * min s (T - s) - c * min t (T - t)| :=
      radial_shell_bound (hmin s hs).1 (hmin t ht).1 (hmin s hs).2 (hmin t ht).2
    _ ≤ 4 * Real.pi * (c * T / 2) ^ 2 * (c * |s - t|) :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = _ := by ring

theorem interval_first_moment {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Icc a b, dist a t) = (b - a) ^ 2 / 2 := by
  have heq : (∫ t in Icc a b, dist a t) = ∫ t in Icc a b, t - a := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.1)]
    ring
  rw [heq, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => (t - a) ^ 2 / 2) (t - a) t := by
    convert (((hasDerivAt_id' (x := t)).sub_const a).pow 2).div_const 2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((by fun_prop : Continuous fun t : ℝ => t - a).intervalIntegrable a b)]
  ring

theorem left_cell_error (F : ℝ → ℝ) (hF : Continuous F) {a b K : ℝ} (hab : a ≤ b)
    (hlip : ∀ t ∈ Icc a b, |F a - F t| ≤ K * |a - t|) :
    |(b - a) * F a - ∫ t in a..b, F t| ≤ K * (b - a) ^ 2 / 2 := by
  let : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    isFiniteMeasure_restrict.mpr (by simp [Real.volume_Icc])
  have hh := cell_local_first_moment (volume.restrict (Icc a b)) F a K
    (hF.integrableOn_Icc) ((continuous_const.dist continuous_id).integrableOn_Icc)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simpa only [Real.norm_eq_abs, Real.dist_eq] using hlip t ht)
  rw [measureReal_restrict_apply_univ, Real.volume_real_Icc,
    max_eq_left (sub_nonneg.mpr hab), smul_eq_mul, Real.norm_eq_abs,
    interval_first_moment hab, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab] at hh
  nlinarith

theorem left_riemann_error (F : ℝ → ℝ) (hF : Continuous F) (N : ℕ)
    {δ K : ℝ} (hδ : 0 < δ)
    (hlip : ∀ s ∈ Icc 0 ((N : ℝ) * δ), ∀ t ∈ Icc 0 ((N : ℝ) * δ),
      |F s - F t| ≤ K * |s - t|)
    (hend : F ((N : ℝ) * δ) = 0) :
    |δ * (∑ j ∈ Finset.range (N + 1), F ((j : ℝ) * δ)) -
      ∫ t in (0 : ℝ)..((N : ℝ) * δ), F t| ≤ K * ((N : ℝ) * δ) * δ / 2 := by
  have hint : (∑ j ∈ Finset.range N, ∫ t in ((j : ℝ) * δ)..(((j + 1 : ℕ) : ℝ) * δ), F t) =
      ∫ t in (0 : ℝ)..((N : ℝ) * δ), F t := by
    simpa only [Nat.cast_zero, zero_mul] using
      (intervalIntegral.sum_integral_adjacent_intervals (a := fun j => (j : ℝ) * δ)
        (n := N) (fun j _ => hF.intervalIntegrable _ _))
  have herr (j : ℕ) (hj : j < N) :
      |δ * F ((j : ℝ) * δ) - ∫ t in ((j : ℝ) * δ)..(((j + 1 : ℕ) : ℝ) * δ), F t| ≤
        K * δ ^ 2 / 2 := by
    have hwidth : (((j + 1 : ℕ) : ℝ) * δ) - (j : ℝ) * δ = δ := by push_cast; ring
    have hjN : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hj
    have hb : ((j + 1 : ℕ) : ℝ) * δ ≤ (N : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hjN hδ.le
    have ha : (j : ℝ) * δ ∈ Icc 0 ((N : ℝ) * δ) :=
      ⟨mul_nonneg (Nat.cast_nonneg _) hδ.le, by nlinarith⟩
    have hcell := left_cell_error F hF (show (j : ℝ) * δ ≤ ((j + 1 : ℕ) : ℝ) * δ by linarith)
      (fun t ht => hlip _ ha t ⟨ha.1.trans ht.1, ht.2.trans hb⟩)
    simpa only [hwidth] using hcell
  rw [Finset.sum_range_succ, hend, add_zero, Finset.mul_sum, ← hint, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        |δ * F ((j : ℝ) * δ) - ∫ t in ((j : ℝ) * δ)..(((j + 1 : ℕ) : ℝ) * δ), F t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.range N, K * δ ^ 2 / 2 :=
      Finset.sum_le_sum (fun j hj => herr j (Finset.mem_range.mp hj))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- The explicit temporal term in the paper, with the inclusive final layer. -/
theorem section_riemann_error (N : ℕ) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) :
    |δ * (∑ j ∈ Finset.range (N + 1), sectionVolume c ((N : ℝ) * δ) ((j : ℝ) * δ)) -
      Real.pi * c ^ 3 * ((N : ℝ) * δ) ^ 4 / 24| ≤
      Real.pi * c ^ 3 * ((N : ℝ) * δ) ^ 3 * δ / 2 := by
  have hT : 0 ≤ (N : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
  have hend : sectionVolume c ((N : ℝ) * δ) ((N : ℝ) * δ) = 0 := by
    simp [sectionVolume, min_eq_right hT]
  have hh := left_riemann_error (sectionVolume c ((N : ℝ) * δ))
    (sectionVolume_continuous c ((N : ℝ) * δ)) N hδ
    (fun _ hs _ ht => sectionVolume_lipschitz hc hs ht) hend
  rw [sectionVolume_integral hT c] at hh
  convert hh using 1
  ring

#print axioms section_riemann_error
#print axioms radial_shell_bound
#print axioms sectionVolume_lipschitz
#print axioms left_cell_error

end
end OPH.FlatDiamondError

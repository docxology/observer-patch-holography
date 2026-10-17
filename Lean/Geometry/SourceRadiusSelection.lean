module
public import Geometry.GoldenSourceCountLimit
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! A continuum-compatible radius family and the premise needed for balance.
Neither a shrinking mesh/radius ratio nor continuity-set counting selects
the exponent one half. The minimax functional below is explicitly supplied. -/

set_option autoImplicit false

namespace OPH.SourceRadiusSelection
noncomputable section
open Filter
open scoped Topology

def radius (q L α : ℝ) : ℝ := L*q^(-α)

theorem radius_positive {q L : ℝ} (hq : 0 < q) (hL : 0 < L) (α : ℝ) :
    0 < radius q L α := mul_pos hL (Real.rpow_pos_of_pos hq _)

theorem radius_tendsto (q : ℕ → ℝ) (hq : Tendsto q atTop atTop)
    (L : ℝ) {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n => radius (q n) L α) atTop (𝓝 0) := by
  simpa only [radius, mul_zero, Function.comp_def] using ((tendsto_rpow_neg_atTop hα).comp hq).const_mul L

theorem mesh_ratio (q L C α : ℝ) (hq : 0 < q) (hL : L ≠ 0) :
    (C*L/q)/radius q L α = C*q^(-(1-α)) := by
  rw [neg_sub,Real.rpow_sub hq,Real.rpow_one]
  unfold radius
  rw [Real.rpow_neg hq.le]
  field_simp

theorem mesh_ratio_tendsto (q : ℕ → ℝ) (hq : Tendsto q atTop atTop)
    (hpos : ∀ n, 0 < q n) (L C : ℝ) (hL : L ≠ 0) {α : ℝ} (hα : α < 1) :
    Tendsto (fun n => (C*L/q n)/radius (q n) L α) atTop (𝓝 0) := by
  simp_rw [mesh_ratio _ _ _ _ (hpos _) hL]
  simpa only [mul_zero, Function.comp_def] using
    ((tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp hq).const_mul C

/-- Actual golden event counting has the same limit for every positive
exponent, with duration a/c. Cone stability additionally requires α<1. -/
theorem golden_count_family {T L c α : ℝ} (hT : 0 ≤ T) (hL : 0 < L)
    (hc : 0 < c) (hα : 0 < α)
    (A : Set (ℝ × (Fin 3 → ℝ))) (hA : MeasurableSet A)
    (hfront : OPH.GoldenSourceCountLimit.spaceTimeVolume T L (frontier A) = 0) :
    Tendsto (fun n =>
      ((radius (Nat.fib (n+2)) L α/c)*(L^3/(Nat.fib (n+2) : ℝ)^3))*
        (OPH.GoldenSourceCountLimit.eventCount (n+2) T L
          (radius (Nat.fib (n+2)) L α/c) A : ℝ))
      atTop (𝓝 ((OPH.GoldenSourceCountLimit.spaceTimeVolume T L).real A)) := by
  apply OPH.GoldenSourceCountLimit.event_count_tendsto hT hL
  · intro n
    exact div_pos (radius_positive (by exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < n+2)) hL α) hc
  · have hq : Tendsto (fun n => (Nat.fib (n+2) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp Nat.fib_add_two_strictMono.tendsto_atTop
    simpa only [zero_div] using (radius_tendsto _ hq L hα).div_const c
  · exact hA
  · exact hfront

/-- Exact characterization of the minimax balance, not an A3 objective. -/
theorem balance_unique {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    max r (ε/r) ≤ Real.sqrt ε ↔ r = Real.sqrt ε := by
  have hs := Real.sqrt_pos.mpr hε
  have he := Real.sq_sqrt hε.le
  constructor
  · intro h
    obtain ⟨h₁,h₂⟩ := max_le_iff.mp h
    have h₃ := (div_le_iff₀ hr).mp h₂
    nlinarith
  · rintro rfl
    apply max_le
    · exact le_rfl
    · apply (div_le_iff₀ hs).mpr
      nlinarith

end
end OPH.SourceRadiusSelection

module
public import Geometry.SourceNetLayeredOrder
public import Geometry.SourceRadiusSelection

@[expose] public section

/-! Removing every spatial restriction collapses the generated order.
The interval fraction below is the explicit combinatorial formula derived
in the accompanying analysis; its algebra and uniform bound are checked here.
The error balance uses the actual normalized volume-error expression. -/

set_option autoImplicit false

namespace OPH.SourceRadiusRemoval
noncomputable section
open Filter OPH.SourceNetLayeredOrder
open scoped Topology

theorem complete_walk {S : Type*} (x y : S) {k : ℕ} (hk : 0 < k) :
    Walk (fun _ _ : S => True) k x y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact Walk.cons trivial (Walk.wait (fun _ => trivial) y n)

theorem complete_order {S : Type*} (e f : ℕ × S) :
    LayerPrec (fun _ _ : S => True) e f ↔ e.1 < f.1 ∨ e = f := by
  constructor
  · rintro ⟨hle, hw⟩
    by_cases h : e.1 < f.1
    · exact Or.inl h
    · have he : e.1 = f.1 := by omega
      have hz : f.1 - e.1 = 0 := by omega
      rw [hz] at hw
      exact Or.inr (Prod.ext he hw.zero_eq)
  · rintro (hlt | rfl)
    · exact ⟨hlt.le, complete_walk _ _ (Nat.sub_pos_of_lt hlt)⟩
    · exact layerPrec_refl _

/-- Fraction for the interval with K full interior layers of N sites and
two singleton tips. Same-layer distinct sites are the only incomparable pairs. -/
def completeIntervalFraction (N K : ℝ) : ℝ :=
  1 - K*N*(N-1)/((K*N+2)*(K*N+1))

theorem interval_fraction_bounds {N K : ℝ} (hN : 1 ≤ N) (hK : 0 < K) :
    1 - 1/K ≤ completeIntervalFraction N K ∧ completeIntervalFraction N K ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have hp : 0 < K*N := mul_pos hK hN0
  have hd : 0 < (K*N+2)*(K*N+1) := by positivity
  have hnum : 0 ≤ K*N*(N-1) := mul_nonneg hp.le (by linarith)
  have hbound : K*N*(N-1)/((K*N+2)*(K*N+1)) ≤ 1/K := by
    apply (div_le_div_iff₀ hd hK).mpr
    nlinarith [sq_nonneg K, mul_nonneg (sq_nonneg K) hN0.le]
  unfold completeIntervalFraction
  constructor
  · linarith
  · exact sub_le_self _ (div_nonneg hnum hd.le)

theorem interval_fraction_tendsto (N K : ℕ → ℝ) (hN : ∀ n, 1 ≤ N n)
    (hK : ∀ n, 0 < K n) (hlim : Tendsto K atTop atTop) :
    Tendsto (fun n => completeIntervalFraction (N n) (K n)) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun n => 1 - 1/K n) atTop (𝓝 1) from by
      simpa using tendsto_const_nhds.sub (hlim.inv_tendsto_atTop))
    tendsto_const_nhds
  · exact fun n => (interval_fraction_bounds (hN n) (hK n)).1
  · exact fun n => (interval_fraction_bounds (hN n) (hK n)).2

/-- A complete one-layer read between two sites at fixed positive distance
eventually violates every fixed finite positive speed as layer duration vanishes. -/
theorem complete_read_exceeds_speed (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) {d c : ℝ} (hd : 0 < d) :
    ∀ᶠ n in atTop, c*δ n < d := by
  have ht : Tendsto (fun n => c*δ n) atTop (𝓝 0) := by
    simpa using hδ.const_mul c
  exact ht.eventually (gt_mem_nhds hd)

/-- Unit-window (c=1,T≤1) specialization of the proved finite volume bound,
with covering and assignment bounded by h≤1. No convergence premise is used. -/
theorem normalized_volume_bound {T a h : ℝ} (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    4*Real.pi*(T+a)*(T/2+h)^2*(h+T*h/a) + Real.pi*T^3*a/2 ≤
      18*Real.pi*h + Real.pi*(a/2+18*h/a) := by
  have hp := Real.pi_pos
  have hta : 0 ≤ T+a := by linarith
  have hsq : (T/2+h)^2 ≤ (3/2 : ℝ)^2 := by
    nlinarith [sq_nonneg (T/2+h-3/2)]
  have hth : T*h/a ≤ h/a := div_le_div_of_nonneg_right (by nlinarith) ha.le
  have hs : 0 ≤ h+T*h/a := by positivity
  have hf : 4*Real.pi*(T+a)*(T/2+h)^2 ≤ 18*Real.pi := by
    have h₁ := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4*Real.pi*(T+a) by positivity)
    nlinarith
  have hb := mul_le_mul hf (show h+T*h/a ≤ h+h/a by linarith) hs (by positivity)
  have ht2 : T^2 ≤ 1 := by nlinarith
  have ht3 : T^3 ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left ht2 hT]
  have ht := mul_le_mul_of_nonneg_right ht3 (show 0 ≤ Real.pi*a/2 by positivity)
  convert add_le_add hb ht using 1 <;> ring

/-- The radius-dependent part of that certified bound, not the physical error,
has its unique minimum at a=6 sqrt(h). Its coefficient is bound-dependent. -/
theorem certified_balance {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    6*Real.sqrt h ≤ a/2+18*h/a ∧
      (a/2+18*h/a = 6*Real.sqrt h ↔ a = 6*Real.sqrt h) := by
  have hs := Real.sq_sqrt hh.le
  have hm : (18*h/a)*a = 18*h := div_mul_cancel₀ _ ha.ne'
  have hsq := sq_nonneg (a-6*Real.sqrt h)
  constructor
  · nlinarith
  · constructor
    · intro he
      nlinarith
    · intro he
      rw [he] at hm ⊢
      have hp := Real.sqrt_pos.mpr hh
      nlinarith

end
end OPH.SourceRadiusRemoval

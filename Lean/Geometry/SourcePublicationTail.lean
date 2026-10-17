module
public import Geometry.SourcePublicationMass

@[expose] public section

/-! Quantitative approximation of the eventual-publication potential.
The block hypothesis is explicit; connected native completion and a uniform
positive reference bound provide it analytically. No spectral gap is assumed. -/

set_option autoImplicit false

namespace OPH.SourcePublicationTail
noncomputable section
open OPH.SourceCheckpointPolicy OPH.SourcePublicationMass

variable {S A : Type*} [Fintype A]

theorem mass_sub (step : S → A → S) (weight : S → A → ℝ)
    (f g : S → ℝ) (n : ℕ) (s : S) :
    mass step weight (fun t => f t - g t) n s =
      mass step weight f n s - mass step weight g n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [mass,ih,mul_sub,Finset.sum_sub_distrib]

theorem mass_scale (step : S → A → S) (weight : S → A → ℝ)
    (f : S → ℝ) (v : ℝ) (n : ℕ) (s : S) :
    mass step weight (fun t => v * f t) n s = v * mass step weight f n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [mass,ih,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring

/-- A block success bound contracts the residual continuation mass. -/
theorem residual_block (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (f h : S → ℝ)
    (hh : ∀ s, ∑ a, weight s a * h (step s a) = h s)
    (B n : ℕ) (δ : ℝ)
    (hb : ∀ s, h s - mass step weight f B s ≤ (1-δ) * (h s-f s)) (s : S) :
    h s - mass step weight f (n+B) s ≤ (1-δ) * (h s-mass step weight f n s) := by
  have hm := mass_mono_terminal step weight hw
    (fun t => h t-mass step weight f B t) (fun t => (1-δ)*(h t-f t)) hb n s
  simpa only [mass_sub,mass_scale,mass_harmonic step weight h hh,← mass_add_steps] using hm

theorem residual_geometric (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (f h : S → ℝ)
    (hh : ∀ s, ∑ a, weight s a * h (step s a) = h s)
    (B : ℕ) (δ : ℝ) (hδ : δ ≤ 1)
    (hb : ∀ s, h s - mass step weight f B s ≤ (1-δ) * (h s-f s)) (k : ℕ) (s : S) :
    h s - mass step weight f (k*B) s ≤ (1-δ)^k * (h s-f s) := by
  induction k with
  | zero => simp only [Nat.zero_mul,mass,pow_zero,one_mul,le_refl]
  | succ k ih =>
    rw [Nat.succ_mul]
    calc
      _ ≤ (1-δ)*(h s-mass step weight f (k*B) s) :=
        residual_block step weight hw f h hh B (k*B) δ hb s
      _ ≤ (1-δ)*((1-δ)^k*(h s-f s)) :=
        mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hδ)
      _ = _ := by rw [pow_succ]; ring

/-- An absolute success bound on every positive-potential unpublished state
is sufficient. Published states and dead states are handled separately. -/
theorem block_from_success (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (hs : ∀ s, ∑ a, weight s a = 1)
    (f : S → ℝ) (hf : ∀ s, f s = 0 ∨ f s = 1)
    (hp : ∀ s, f s ≤ ∑ a, weight s a * f (step s a))
    (B : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hb : ∀ s, f s = 0 → 0 < eventual step weight f s → δ ≤ mass step weight f B s)
    (s : S) :
    eventual step weight f s - mass step weight f B s ≤
      (1-δ)*(eventual step weight f s-f s) := by
  have hf0 : ∀ t, 0 ≤ f t := by intro t; rcases hf t with h|h <;> simp [h]
  have hf1 : ∀ t, f t ≤ 1 := by intro t; rcases hf t with h|h <;> simp [h]
  have hn := eventual_nonneg step weight hw hs f hf1 hf0 s
  have hu := eventual_le_one step weight hw hs f hf1 s
  have hm := mass_le_eventual step weight hw hs f hf1 B s
  have hl : f s ≤ mass step weight f B s :=
    mass_mono_time step weight hw f hp s (Nat.zero_le B)
  rcases hf s with he|he
  · by_cases ht : 0 < eventual step weight f s
    · have hb' := hb s he ht
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_left hu hδ]
    · have hz : eventual step weight f s = 0 := le_antisymm (le_of_not_gt ht) hn
      have hv : mass step weight f B s = 0 :=
        le_antisymm (by simpa [hz] using hm) (by simpa [he] using hl)
      simp only [he,hz,hv,sub_self,mul_zero,le_refl]
  · have hh := eventual_eq_one step weight hw hs f hf1 s he
    have hv : mass step weight f B s = 1 :=
      le_antisymm (by simpa [hh] using hm) (by simpa [he] using hl)
    simp only [he,hh,hv,sub_self,mul_zero,le_refl]

end
end OPH.SourcePublicationTail

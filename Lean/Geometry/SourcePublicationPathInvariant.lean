module
public import Geometry.SourcePublicationPath

@[expose] public section

/-! An ordered-minor invariant for arbitrary nearest-neighbour native words.
Each nonadjacent two-row minor persists under every adjacent pair mean.
Applied to rows 0 and 2 after the first safe edge, this extends the analytic
eventual-publication classification to every finite path length. -/

set_option autoImplicit false

namespace OPH.SourcePublicationPathInvariant
noncomputable section
open ObserverPatchHolography.ScalarSeamRepair

def minor (x y : ℕ → ℝ) (i j : ℕ) : ℝ := x i*y j-x j*y i
def Ordered (x y : ℕ → ℝ) : Prop := ∀ i j, i<j → 0 ≤ minor x y i j

theorem mean_ordered (x y : ℕ → ℝ) (h : Ordered x y) (e : ℕ) :
    Ordered (pairAverage e (e+1) x) (pairAverage e (e+1) y) := by
  intro i j hij
  by_cases hi : i=e ∨ i=e+1
  · by_cases hj : j=e ∨ j=e+1
    · simp [minor,pairAverage,hi,hj]
    · have he : e<j := by omega
      have he' : e+1<j := by omega
      have h₁ := h e j he
      have h₂ := h (e+1) j he'
      simp [minor,pairAverage,hi,hj]
      unfold minor at h₁ h₂
      nlinarith
  · by_cases hj : j=e ∨ j=e+1
    · have he : i<e := by omega
      have he' : i<e+1 := by omega
      have h₁ := h i e he
      have h₂ := h i (e+1) he'
      simp [minor,pairAverage,hi,hj]
      unfold minor at h₁ h₂
      nlinarith
    · simpa [minor,pairAverage,hi,hj] using h i j hij

theorem separated_minor_half (x y : ℕ → ℝ) (h : Ordered x y) (e : ℕ) :
    minor x y 0 2 / 2 ≤ minor (pairAverage e (e+1) x) (pairAverage e (e+1) y) 0 2 := by
  rcases e with _|e
  · have hh := h 1 2 (by omega)
    simp [minor,pairAverage] at *
    nlinarith
  rcases e with _|e
  · have hh := h 0 1 (by omega)
    simp [minor,pairAverage] at *
    nlinarith
  rcases e with _|e
  · have hh := h 0 3 (by omega)
    simp [minor,pairAverage] at *
    nlinarith
  · have hh := h 0 2 (by omega)
    have h₀ : ¬(0=e+1+1+1 ∨ 0=e+1+1+1+1) := by omega
    have h₂ : ¬(2=e+1+1+1 ∨ 2=e+1+1+1+1) := by omega
    have hfix (a : ℕ → ℝ) (i : ℕ)
        (hi : ¬ (i = e+1+1+1 ∨ i = e+1+1+1+1)) :
        pairAverage (e+1+1+1) (e+1+1+1+1) a i = a i := by
      change (if i = e+1+1+1 ∨ i = e+1+1+1+1 then _ else _) = _
      rw [ite_eq_right hi]
    simpa only [minor, hfix x 0 h₀, hfix y 0 h₀,
      hfix x 2 h₂, hfix y 2 h₂] using (half_le_self hh)

def run : List ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | [], x => x
  | e::es, x => run es (pairAverage e (e+1) x)

theorem run_ordered (x y : ℕ → ℝ) (h : Ordered x y) (es : List ℕ) :
    Ordered (run es x) (run es y) := by
  induction es generalizing x y with
  | nil => exact h
  | cons e es ih => exact ih _ _ (mean_ordered x y h e)

/-- No future adjacent mean can erase the two independent response columns.
The explicit lower bound also exposes exponential attenuation. -/
theorem run_minor_bound (x y : ℕ → ℝ) (h : Ordered x y) (es : List ℕ) :
    minor x y 0 2 / 2^es.length ≤ minor (run es x) (run es y) 0 2 := by
  induction es generalizing x y with
  | nil => simp only [List.length_nil,pow_zero,div_one,run,le_refl]
  | cons e es ih =>
    have hm := separated_minor_half x y h e
    have ht := ih _ _ (mean_ordered x y h e)
    have hp : 0 < (2 : ℝ)^es.length := by positivity
    have hd := div_le_div_of_nonneg_right hm hp.le
    simp only [List.length_cons,run]
    calc
      _ = (minor x y 0 2/2)/2^es.length := by rw [pow_succ]; field_simp
      _ ≤ _ := hd
      _ ≤ _ := ht

def seed (j : ℕ) : ℕ → ℝ := fun i => if i=j then 1 else 0

theorem seed_ordered : Ordered (seed 0) (seed 1) := by
  intro i j hij
  unfold minor seed
  by_cases hi : i=0 <;> by_cases hj : j=1 <;> by_cases hi' : i=1 <;> by_cases hj' : j=0
  all_goals simp_all

theorem safe_initial_minor :
    minor (pairAverage 1 2 (seed 0)) (pairAverage 1 2 (seed 1)) 0 2 = 1/2 := by
  norm_num [minor,pairAverage,seed]

theorem safe_word_minor (es : List ℕ) :
    (1/2 : ℝ)/2^es.length ≤
      minor (run es (pairAverage 1 2 (seed 0)))
        (run es (pairAverage 1 2 (seed 1))) 0 2 := by
  have h := run_minor_bound _ _ (mean_ordered _ _ seed_ordered 1) es
  norm_num only [show (1 : ℕ)+1=2 from rfl,safe_initial_minor] at h
  exact h

theorem safe_word_positive (es : List ℕ) :
    0 < minor (run es (pairAverage 1 2 (seed 0)))
      (run es (pairAverage 1 2 (seed 1))) 0 2 :=
  lt_of_lt_of_le (by positivity) (safe_word_minor es)

end
end OPH.SourcePublicationPathInvariant

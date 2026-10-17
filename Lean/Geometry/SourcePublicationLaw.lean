module
public import Geometry.SourcePublicationMass

@[expose] public section

/-!
# Consistent publication laws from the derived continuation potential

A harmonic continuation potential defines compatible finite word laws.
Specializing to the least publication potential identifies these laws as
limits of finite-deadline marginals. A recoverable unpublished prefix is
an explicit obstruction to compatibility of the finite-deadline laws.
-/

set_option autoImplicit false

namespace OPH.SourcePublicationLaw
noncomputable section
open OPH.SourceCheckpointPolicy OPH.SourcePublicationMass Filter
open scoped Topology

variable {S A : Type*} [Fintype A]

omit [Fintype A] in
theorem finish_append (step : S → A → S) (s : S) (as bs : List A) :
    finish step s (as ++ bs) = finish step (finish step s as) bs := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => exact ih _

omit [Fintype A] in
theorem pathWeight_append (step : S → A → S) (weight : S → A → ℝ)
    (s : S) (as bs : List A) :
    pathWeight step weight s (as ++ bs) =
      pathWeight step weight s as * pathWeight step weight (finish step s as) bs := by
  induction as generalizing s with
  | nil => simp only [List.nil_append,pathWeight,finish,one_mul]
  | cons a as ih => simp only [List.cons_append,pathWeight,finish,ih,mul_assoc]

def cylinder (step : S → A → S) (weight : S → A → ℝ) (h : S → ℝ)
    (s : S) (as : List A) : ℝ :=
  pathWeight step weight s as * h (finish step s as) / h s

def finitePrefix (step : S → A → S) (weight : S → A → ℝ) (f : S → ℝ)
    (s : S) (as : List A) (extra : ℕ) : ℝ :=
  pathWeight step weight s as * mass step weight f extra (finish step s as) /
    mass step weight f (as.length + extra) s

/-- The displayed finite-prefix ratio is the actual marginal of the
complete conditioned word law, with all suffixes included. -/
theorem finitePrefix_is_marginal (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 < weight s a) (f : S → ℝ) (hf : ∀ s, 0 ≤ f s)
    (s : S) (as : List A) (n : ℕ)
    (hm : 0 < mass step weight f (as.length+n) s) :
    (∑ w : Fin n → A, pathLaw step weight f s (as ++ List.ofFn w)) =
      finitePrefix step weight f s as n := by
  have he (w : Fin n → A) :
      pathLaw step weight f s (as ++ List.ofFn w) =
        (pathWeight step weight s as *
          (pathWeight step weight (finish step s as) (List.ofFn w) *
            f (finish step (finish step s as) (List.ofFn w)))) /
              mass step weight f (as.length+n) s := by
    rw [pathLaw_formula step weight f hw hf s _ (by simpa using hm)]
    simp only [pathWeight_append,finish_append,List.length_append,List.length_ofFn,mul_assoc]
  simp_rw [he]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul,← Finset.mul_sum,← mass_eq_word_sum]
  rfl

theorem cylinder_eq_pathLaw (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 < weight s a) (h : S → ℝ) (hn : ∀ s, 0 ≤ h s)
    (hh : ∀ s, ∑ a, weight s a * h (step s a) = h s)
    (s : S) (hs : 0 < h s) (as : List A) :
    cylinder step weight h s as = pathLaw step weight h s as := by
  have hm : 0 < mass step weight h as.length s := by
    rw [mass_harmonic step weight h hh]
    exact hs
  rw [pathLaw_formula step weight h hw hn s as hm,mass_harmonic step weight h hh]
  rfl

omit [Fintype A] in
theorem cylinder_nonneg (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 < weight s a) (h : S → ℝ) (hn : ∀ s, 0 ≤ h s)
    (s : S) (as : List A) : 0 ≤ cylinder step weight h s as :=
  div_nonneg (mul_nonneg (pathWeight_positive step weight hw s as).le (hn _)) (hn s)

theorem cylinder_normalized (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 < weight s a) (h : S → ℝ) (hn : ∀ s, 0 ≤ h s)
    (hh : ∀ s, ∑ a, weight s a * h (step s a) = h s)
    (s : S) (hs : 0 < h s) (n : ℕ) :
    ∑ w : Fin n → A, cylinder step weight h s (List.ofFn w) = 1 := by
  simp_rw [cylinder_eq_pathLaw step weight hw h hn hh s hs]
  apply pathLaw_normalized step weight h hw hn s n
  rwa [mass_harmonic step weight h hh]

/-- Every cylinder is the sum of its one-move extensions, including a
zero-mass prefix. This is consistency of the whole word law. -/
theorem cylinder_consistent (step : S → A → S) (weight : S → A → ℝ)
    (h : S → ℝ) (hh : ∀ s, ∑ a, weight s a * h (step s a) = h s)
    (s : S) (as : List A) :
    ∑ a, cylinder step weight h s (as ++ [a]) = cylinder step weight h s as := by
  simp only [cylinder,pathWeight_append,finish_append,pathWeight,finish,mul_one]
  simp_rw [mul_assoc]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul,← Finset.mul_sum,hh]

omit [Fintype A] in
theorem cylinder_positive_iff (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 < weight s a) (h : S → ℝ) (s : S) (hs : 0 < h s)
    (as : List A) :
    0 < cylinder step weight h s as ↔ 0 < h (finish step s as) := by
  exact (div_pos_iff_of_pos_right hs).trans
    (mul_pos_iff_of_pos_left (pathWeight_positive step weight hw s as))

/-- The prefix law is obtained by letting the deadline recede; the prefix
length stays fixed. This differs from conditioning at the prefix's own length. -/
theorem finitePrefix_tendsto (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (hs : ∀ s, ∑ a, weight s a = 1)
    (f : S → ℝ) (hf : ∀ s, f s ≤ 1)
    (hp : ∀ s, f s ≤ ∑ a, weight s a * f (step s a))
    (s : S) (hh : 0 < eventual step weight f s) (as : List A) :
    Tendsto (finitePrefix step weight f s as) atTop
      (𝓝 (cylinder step weight (eventual step weight f) s as)) := by
  have ht := mass_tendsto step weight hw hs f hf hp (finish step s as)
  have hd := (mass_tendsto step weight hw hs f hf hp s).comp
    (tendsto_add_atTop_nat as.length)
  have hl := (ht.const_mul (pathWeight step weight s as)).div hd (ne_of_gt hh)
  unfold finitePrefix cylinder
  convert hl using 1; simp [funext_iff,Function.comp_def,Nat.add_comm]

theorem own_deadline_zero (step : S → A → S) (weight : S → A → ℝ)
    (f : S → ℝ) (s : S) (as : List A) (hf : f (finish step s as) = 0) :
    finitePrefix step weight f s as 0 = 0 := by
  simp only [finitePrefix,mass,hf,mul_zero,zero_div]

/-- When its own deadline is feasible, a viable unpublished prefix has zero
mass in that finite law and positive mass in the harmonic cylinder law. -/
theorem recoverable_prefix_mismatch (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 < weight s a) (h : S → ℝ) (f : S → ℝ)
    (hn : ∀ s, 0 ≤ f s) (s : S) (hs : 0 < h s) (as : List A)
    (hm : 0 < mass step weight f as.length s)
    (hf : f (finish step s as) = 0) (hh : 0 < h (finish step s as)) :
    pathLaw step weight f s as = 0 ∧ 0 < cylinder step weight h s as := by
  constructor
  · rw [pathLaw_formula step weight f hw hn s as hm,hf,mul_zero,zero_div]
  · exact (cylinder_positive_iff step weight hw h s hs as).mpr hh

end
end OPH.SourcePublicationLaw

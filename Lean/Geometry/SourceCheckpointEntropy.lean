module
public import Mathlib.InformationTheory.KullbackLeibler.KLFun

@[expose] public section

/-!
# Unique information projection onto a checkpoint face

The finite index type consists of all terminally valid native histories.
Its reference weights are inherited from the complete history reference,
without renormalizing individual prefixes. The normalized restriction is
proved to be the unique minimizer, including candidate laws with zeros.
This proves selection on the named full-history cover; it does not select
that cover, the reference, the horizon or the public record domain.
-/

set_option autoImplicit false

namespace OPH.SourceCheckpointEntropy
noncomputable section
open InformationTheory

variable {W : Type*} [Fintype W]

def objective (reference p : W → ℝ) : ℝ :=
  ∑ w, p w * Real.log (p w / reference w)

theorem term_decomposition (p q z : ℝ) (hq : 0 < q) (hz : 0 < z) :
    p * Real.log (p / (z*q)) =
      q * klFun (p/q) + p - q - p*Real.log z := by
  by_cases he : p = 0
  · simp [he,klFun]
  · have hlog : Real.log (p/(z*q)) = Real.log (p/q) - Real.log z := by
      rw [show p/(z*q) = (p/q)/z by ring]
      exact Real.log_div (div_ne_zero he (ne_of_gt hq)) (ne_of_gt hz)
    rw [hlog,klFun]
    field_simp
    ring

/-- The entropy gap is an explicit sum of nonnegative terms. -/
theorem objective_decomposition (q p : W → ℝ) (z : ℝ)
    (hq : ∀ w, 0 < q w) (_hp : ∀ w, 0 ≤ p w) (hz : 0 < z)
    (sq : ∑ w, q w = 1) (sp : ∑ w, p w = 1) :
    objective (fun w => z*q w) p =
      (∑ w, q w * klFun (p w/q w)) - Real.log z := by
  unfold objective
  simp_rw [term_decomposition _ _ _ (hq _) hz]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_mul,sp,sq,one_mul]
  ring

theorem objective_self (q : W → ℝ) (z : ℝ) (hq : ∀ w, 0 < q w)
    (hz : 0 < z) (sq : ∑ w, q w = 1) :
    objective (fun w => z*q w) q = -Real.log z := by
  rw [objective_decomposition q q z hq (fun w => (hq w).le) hz sq sq]
  simp [div_self (ne_of_gt (hq _)),klFun_one]

theorem normalized_restriction_minimal (q p : W → ℝ) (z : ℝ)
    (hq : ∀ w, 0 < q w) (hp : ∀ w, 0 ≤ p w) (hz : 0 < z)
    (sq : ∑ w, q w = 1) (sp : ∑ w, p w = 1) :
    objective (fun w => z*q w) q ≤ objective (fun w => z*q w) p := by
  rw [objective_self q z hq hz sq,objective_decomposition q p z hq hp hz sq sp]
  have h : 0 ≤ ∑ w, q w * klFun (p w/q w) :=
    Finset.sum_nonneg (fun w _ => mul_nonneg (hq w).le (klFun_nonneg (div_nonneg (hp w) (hq w).le)))
  linarith

/-- Equality is possible only at the normalized inherited reference. -/
theorem normalized_restriction_unique (q p : W → ℝ) (z : ℝ)
    (hq : ∀ w, 0 < q w) (hp : ∀ w, 0 ≤ p w) (hz : 0 < z)
    (sq : ∑ w, q w = 1) (sp : ∑ w, p w = 1)
    (he : objective (fun w => z*q w) p ≤ objective (fun w => z*q w) q) : p = q := by
  rw [objective_self q z hq hz sq,objective_decomposition q p z hq hp hz sq sp] at he
  have hn : ∀ w, 0 ≤ q w * klFun (p w/q w) :=
    fun w => mul_nonneg (hq w).le (klFun_nonneg (div_nonneg (hp w) (hq w).le))
  have hs : ∑ w, q w * klFun (p w/q w) = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg (fun w _ => hn w))
  funext w
  have hw : q w * klFun (p w/q w) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hn w)).mp hs w (Finset.mem_univ w)
  have hk : klFun (p w/q w) = 0 := (mul_eq_zero.mp hw).resolve_left (ne_of_gt (hq w))
  have hr : p w/q w = 1 := (klFun_eq_zero_iff (div_nonneg (hp w) (hq w).le)).mp hk
  exact (div_eq_one_iff_eq (ne_of_gt (hq w))).mp hr

/-- The weights and their normalization are constructed, not supplied as
properties of a presumed optimizer. Apply this to the complete accepted
history subtype with its inherited full-reference word weights. -/
theorem inherited_reference_selected [Nonempty W] (r : W → ℝ)
    (hr : ∀ w, 0 < r w) :
    let z := ∑ w, r w
    let q := fun w => r w / z
    (∑ w, q w = 1) ∧ (∀ w, 0 < q w) ∧
      ∀ p : W → ℝ, (∀ w, 0 ≤ p w) → (∑ w, p w = 1) →
        objective r q ≤ objective r p ∧ (objective r p ≤ objective r q → p = q) := by
  let z := ∑ w, r w
  have hz : 0 < z := Finset.sum_pos (fun w _ => hr w) Finset.univ_nonempty
  have sq : ∑ w, r w / z = 1 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ (ne_of_gt hz)
  have hq : ∀ w, 0 < r w / z := fun w => div_pos (hr w) hz
  refine ⟨sq,hq,?_⟩
  intro p hp sp
  have he : (fun w => z * (r w / z)) = r := by
    funext w
    field_simp
  constructor
  · simpa [he] using normalized_restriction_minimal (fun w => r w/z) p z hq hp hz sq sp
  · intro h
    apply normalized_restriction_unique (fun w => r w/z) p z hq hp hz sq sp
    simpa [he] using h

end
end OPH.SourceCheckpointEntropy

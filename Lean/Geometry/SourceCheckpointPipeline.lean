module
public import Geometry.SourceCheckpointNative

@[expose] public section

/-!
# Algebra for the shortest two-wave path pipeline

Disjoint native means commute. The analytic cut-capacity and precedence
proof in DERIVATION.md classifies the shortest path histories and derives
the two displayed response rows. This module kernel-checks the native
commutation, exact reconstruction and sharp two-sample error coefficient;
it does not claim a kernel proof of the full path-language classification.
-/

set_option autoImplicit false

namespace OPH.SourceCheckpointPipeline
noncomputable section
open ObserverPatchHolography.ScalarSeamRepair

theorem disjoint_means_commute {P : Type*} [DecidableEq P] (a b c d : P)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (x : P → ℝ) :
    pairAverage a b (pairAverage c d x) = pairAverage c d (pairAverage a b x) := by
  have hca := Ne.symm hac
  have hda := Ne.symm had
  have hcb := Ne.symm hbc
  have hdb := Ne.symm hbd
  funext p
  by_cases ha : p = a <;> by_cases hb : p = b <;>
    by_cases hc : p = c <;> by_cases hd : p = d <;>
    simp_all [pairAverage]

def firstSample (k : ℕ) (y : ℝ) : ℝ := y / 2^k
def finalSample (k : ℕ) (x y : ℝ) : ℝ :=
  x / 2^(k+1) + (k+2 : ℝ)*y / 2^(k+2)

theorem recover_second (k : ℕ) (y : ℝ) : 2^k * firstSample k y = y := by
  unfold firstSample
  field_simp

theorem recover_first (k : ℕ) (x y : ℝ) :
    2^(k+1)*finalSample k x y - ((k+2 : ℝ)*2^k/2)*firstSample k y = x := by
  unfold finalSample firstSample
  rw [pow_succ,show 2^(k+2) = (2:ℝ)^k*4 by ring]
  field_simp
  ring

/-- Independent bounded errors in the two informative receiver samples
have this exact worst-case coefficient. No probabilistic noise model is used. -/
theorem sample_error_bound (k : ℕ) (e₁ e₂ eps : ℝ) (_he : 0 ≤ eps)
    (h₁ : |e₁| ≤ eps) (h₂ : |e₂| ≤ eps) :
    |2^(k+1)*e₂ - ((k+2 : ℝ)*2^k/2)*e₁| ≤ ((k+6 : ℝ)*2^k/2)*eps := by
  have hA : (0:ℝ) ≤ 2^(k+1) := by positivity
  have hB : (0:ℝ) ≤ (k+2 : ℝ)*2^k/2 := by positivity
  calc
    _ ≤ |2^(k+1)*e₂| + |((k+2 : ℝ)*2^k/2)*e₁| := by
      simpa only [sub_eq_add_neg,neg_mul,abs_neg] using
        abs_add_le (2^(k+1)*e₂) (-((k+2 : ℝ)*2^k/2)*e₁)
    _ = 2^(k+1)*|e₂| + ((k+2 : ℝ)*2^k/2)*|e₁| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hA,abs_of_nonneg hB]
    _ ≤ 2^(k+1)*eps + ((k+2 : ℝ)*2^k/2)*eps :=
      add_le_add (mul_le_mul_of_nonneg_left h₂ hA) (mul_le_mul_of_nonneg_left h₁ hB)
    _ = _ := by rw [pow_succ]; ring

theorem sample_error_attained (k : ℕ) (eps : ℝ) (he : 0 ≤ eps) :
    |2^(k+1)*eps - ((k+2 : ℝ)*2^k/2)*(-eps)| = ((k+6 : ℝ)*2^k/2)*eps := by
  have heq : 2^(k+1)*eps - ((k+2 : ℝ)*2^k/2)*(-eps) = ((k+6 : ℝ)*2^k/2)*eps := by
    rw [pow_succ]
    ring
  rw [heq,abs_of_nonneg (by positivity)]

end
end OPH.SourceCheckpointPipeline

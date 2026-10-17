module
public import Geometry.SourceNativeStoredProgram

@[expose] public section

/-!
# Finite precision and stationary evaluation

The precision inequality includes a whole-history residual allowance.
Stationary evaluation is an exact shortcut for a deterministic repeated word;
the word's operation count includes every repetition.
-/

set_option autoImplicit false

namespace OPH.SourceNativeProgramBudget
noncomputable section

/-- With maximum decoding gain `M`, sufficient grid and cleanup precision
give a strict singleton margin. The inequality is independent of the values
of the stored integers. `R` is the sum of all comparison-state residuals. -/
theorem precision_margin (M W Q R : ℝ) (hM : 1 ≤ M) (hW : 0 ≤ W)
    (hQ : 64*(W+1)*M ≤ Q) (hR : 0 ≤ R) (hcleanup : R ≤ 1/(64*M)) :
    2*(M/(Q-3))*((4+5*W)/8+Q*R) < 1 := by
  have hM0 : 0 < M := by linarith
  have hMW : 0 ≤ M*W := mul_nonneg (le_of_lt hM0) hW
  have hQ6 : 6 ≤ Q := by nlinarith
  have hd : 0 < Q-3 := by linarith
  have hround : M*(4+5*W)/(8*(Q-3)) ≤ 1/16 := by
    apply (div_le_iff₀ (by positivity : 0 < 8*(Q-3))).mpr
    nlinarith
  have hMR : M*R ≤ 1/64 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 64*M)).mp hcleanup
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hMR (by linarith : 0 ≤ Q)
  have hres : M*Q*R/(Q-3) ≤ 1/16 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  calc
    2*(M/(Q-3))*((4+5*W)/8+Q*R) =
        2*(M*(4+5*W)/(8*(Q-3))+M*Q*R/(Q-3)) := by field_simp
    _ ≤ 2*((1:ℝ)/16+1/16) := by linarith
    _ < 1 := by norm_num

def iterate {α : Type*} (f : α → α) : ℕ → α → α
  | 0, x => x
  | n+1, x => iterate f n (f x)

theorem fixed_point {α : Type*} (f : α → α) (x : α) (h : f x = x) (n : ℕ) :
    iterate f n x = x := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [iterate, h] using ih

theorem repeated_word_length {α : Type*} (word : List α) (n : ℕ) :
    (List.replicate n word).flatten.length = n*word.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.add_mul, Nat.add_comm]

end
end OPH.SourceNativeProgramBudget

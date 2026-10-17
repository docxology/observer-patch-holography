module
public import Geometry.SourceBankCompiler

@[expose] public section

/-!
# Finite precision exists for the compiled word

Cleanup and grid precision are chosen after the payload-independent
instruction stream. The native work includes every chosen cleanup mean.
These sufficient choices establish finiteness, not efficient hardware or
attainable physical error bounds.
-/

set_option autoImplicit false

namespace OPH.SourceBankPrecision
noncomputable section
open OPH.SourceBankMachine OPH.SourceBankCompiler

theorem nat_le_two_pow (n : ℕ) : (n:ℝ) ≤ (2:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
    rw [Nat.cast_succ,pow_succ]
    nlinarith

theorem real_le_dyadic_ceil (x : ℝ) : x ≤ (2:ℝ)^⌈x⌉₊ :=
  (Nat.le_ceil x).trans (nat_le_two_pow _)

/-- The cleanup bound is independent of payloads and of the subsequently
chosen grid. The grid pays for the word with that cleanup count included. -/
theorem exists_precision {ops : List Op} (p : Placed ops) (e : Scales)
    (A M : ℝ) (hA : 0 ≤ A) (hM : 1 ≤ M) :
    ∃ k B : ℕ, 3 < (2:ℝ)^B ∧
      2*(M/((2:ℝ)^B-3))*
        ((4+5*(work ops k e:ℝ))/8+(2:ℝ)^B*error p k A) < 1 := by
  let k := ⌈64*M*A*(cleanupBudget ops:ℝ)⌉₊
  have hM0 : 0 < M := by linarith
  have hk : 64*M*A*(cleanupBudget ops:ℝ) ≤ (2:ℝ)^k := real_le_dyadic_ceil _
  have hb : error p k A ≤ 1/(64*M) := by
    apply (error_bound p k A hA).trans
    apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 2^k)
      (by positivity : (0:ℝ) < 64*M)).mpr
    nlinarith [hk]
  let B := ⌈64*((work ops k e:ℝ)+1)*M⌉₊
  have hQ : 64*((work ops k e:ℝ)+1)*M ≤ (2:ℝ)^B := real_le_dyadic_ceil _
  have hW : (0:ℝ) ≤ work ops k e := Nat.cast_nonneg _
  have hQ3 : 3 < (2:ℝ)^B := by nlinarith
  exact ⟨k,B,hQ3,OPH.SourceNativeProgramBudget.precision_margin M (work ops k e)
    ((2:ℝ)^B) (error p k A) hM hW hQ (error_nonneg p k A hA) hb⟩

/-- One finite grid gives a strict publication margin at every final
register, under the stated preparation, per-mean and sample allowances.
Those physical allowances are hypotheses, not a source-derived instrument. -/
theorem exists_global_margin {ops : List Op} (p : Placed ops) (e : Scales)
    (M : ℕ) (he : ∀ i, e i ≤ M) (A : ℝ) (hA : 0 ≤ A) :
    ∃ k B : ℕ, 3 < (2:ℝ)^B ∧ ∀ i,
      2*((2:ℝ)^(scales ops e i) / (((2:ℝ)^B-3)/(2:ℝ)^B))*
        (1/(4*(2:ℝ)^B)+(nativeWord p k e).length*(5/(8*(2:ℝ)^B))+
          error p k A+1/(4*(2:ℝ)^B)) < 1 := by
  let E := M+(ops.map scaleCharge).sum
  have hpow : (1:ℝ) ≤ 2^E := one_le_pow₀ (by norm_num)
  obtain ⟨k,B,hQ,hm⟩ := exists_precision p e A ((2:ℝ)^E) hA hpow
  refine ⟨k,B,hQ,?_⟩
  intro i
  have hi : scales ops e i ≤ E := scales_bound ops e M he i
  have hpi : (2:ℝ)^(scales ops e i) ≤ (2:ℝ)^E := pow_le_pow_right₀ (by norm_num) hi
  have hq0 : (2:ℝ)^B ≠ 0 := by positivity
  have hqd : 0 < (2:ℝ)^B-3 := by linarith
  have hr := error_nonneg p k A hA
  rw [native_word_length]
  have hid :
      2*((2:ℝ)^(scales ops e i) / (((2:ℝ)^B-3)/(2:ℝ)^B))*
        (1/(4*(2:ℝ)^B)+(work ops k e:ℝ)*(5/(8*(2:ℝ)^B))+
          error p k A+1/(4*(2:ℝ)^B)) =
      2*((2:ℝ)^(scales ops e i)/((2:ℝ)^B-3))*
        ((4+5*(work ops k e:ℝ))/8+(2:ℝ)^B*error p k A) := by
    field_simp
    ring
  rw [hid]
  apply lt_of_le_of_lt _ hm
  gcongr

end
end OPH.SourceBankPrecision

module
public import Geometry.SourceNativeProgramError
public import Geometry.SourceAccumulatorDecoder

@[expose] public section

/-!
# Reusable arithmetic core with a flexible input polarity

The workspace has a reset rung. The accumulator is cleared to a quantified
residual by a finite native word, so it needs no reset rectangle. A retained
unit then supplies the start value. The operand rectangle permits either
route polarity; no data-dependent sign correction or host write is used.
-/

set_option autoImplicit false

namespace OPH.SourceNativeCore
noncomputable section
open OPH.SourceEncodedMemory OPH.SourceReusableBus OPH.SourceNativeAccumulator
open OPH.SourceNativeShuttle OPH.SourceNativeProgramError

def resetSweep : List (Instruction ℕ) := [.clear 1, .copy 0 1]

def resetSweeps : ℕ → List (Instruction ℕ)
  | 0 => []
  | k+1 => resetSweep ++ resetSweeps k

def resetCore (k : ℕ) : List (Instruction ℕ) := resetSweeps k ++ [.clear 1]

theorem resetSweep_formula (a : ℕ → ℝ) :
    execute resetSweep a = fun i => if i = 0 ∨ i = 1 then a 0/2 else a i := by
  ext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
    simp [resetSweep, execute, step, copied, cleared, h0, h1]

theorem resetCore_formula (k : ℕ) (a : ℕ → ℝ) :
    execute (resetCore k) a =
      fun i => if i = 1 then 0 else if i = 0 then a 0/(2:ℝ)^k else a i := by
  induction k generalizing a with
  | zero =>
    ext i
    by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
      simp [resetCore, resetSweeps, execute, step, cleared, h0, h1]
  | succ k ih =>
    have hc : resetCore (k+1) = resetSweep ++ resetCore k := by
      simp [resetCore, resetSweeps, List.append_assoc]
    rw [hc, execute_append, resetSweep_formula, ih]
    ext i
    by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
      simp [h0, h1, pow_succ, div_div, mul_comm]

theorem resetCore_length (k : ℕ) : (compile (resetCore k)).length = 3*k+1 := by
  have hs : (compile (resetSweeps k)).length = 3*k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp [resetSweeps, resetSweep, compile, word, clearWord, copyWord, ih]
      omega
  simp [resetCore, compile_append, compile, word, clearWord, hs]

theorem resetCore_error (k : ℕ) (A : ℝ) (a : ℕ → ℝ)
    (hA : 0 ≤ A) (ha : |a 0| ≤ A) :
    Near (A/(2:ℝ)^k) (execute (resetCore k) a) (cleared 0 (cleared 1 a)) := by
  rw [resetCore_formula]
  intro i
  by_cases h1 : i = 1
  · simp [h1, cleared, div_nonneg hA (by positivity : (0:ℝ) ≤ 2^k)]
  by_cases h0 : i = 0
  · subst i
    simpa [cleared, abs_div] using
      div_le_div_of_nonneg_right ha (by positivity : (0:ℝ) ≤ 2^k)
  · simp [h1, h0, cleared, div_nonneg hA (by positivity : (0:ℝ) ≤ 2^k)]

def startCore (k : ℕ) : List (Instruction ℕ) := resetCore k ++ [.copy 2 0]

theorem ideal_start (v : ℕ → ℝ) (e : ℕ → ℕ) :
    copied 2 0 (cleared 0 (cleared 1 (represented v e))) =
      represented (startedValues v) (startedScales e) := by
  ext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;>
    simp [represented, copied, cleared, startedValues, startedScales, h0, h1, h2,
      pow_succ, div_div]

theorem encoded_near (a c : ℕ → ℝ) (b E : ℝ) (h : Near E a c) :
    Near E (encode b a) (encode b c) := by
  intro ⟨i,r⟩
  have hi := h i
  cases r
  · change |(b+a i)-(b+c i)| ≤ _
    convert hi using 1; congr 1; ring
  · change |(b-a i)-(b-c i)| ≤ _
    have hn : |-(a i-c i)| ≤ E := by simpa only [abs_neg] using hi
    convert hn using 1; congr 1; ring

/-- Native start from one retained unit. The residual from the previous
accumulator is charged even though its logical version has been retired. -/
theorem startCore_native_error (k : ℕ) (b A : ℝ) (v : ℕ → ℝ) (e : ℕ → ℕ)
    (hA : 0 ≤ A) (ha : |represented v e 0| ≤ A) :
    Near (A/(2:ℝ)^k) (run (compile (startCore k)) (encode b (represented v e)))
      (encode b (represented (startedValues v) (startedScales e))) := by
  have hr := encoded_near _ _ b _ (resetCore_error k A (represented v e) hA ha)
  have hc := run_near (copyWord 2 0) _ _ _ hr
  rw [← OPH.SourceReusableBus.program_native (resetCore k) b (represented v e)] at hc
  rw [copy_native, ideal_start] at hc
  simpa [startCore, compile_append, compile, word, run_append] using hc

theorem startCore_length (k : ℕ) : (compile (startCore k)).length = 3*k+3 := by
  simp [startCore, compile_append, resetCore_length, compile, word, copyWord]

end
end OPH.SourceNativeCore

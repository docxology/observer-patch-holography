module
public import Geometry.SourceBusScaling

@[expose] public section

/-!
# Native transfer into a reusable record

A source is retained at half amplitude, a retired destination is overwritten,
and the intervening bus is cleaned by a finite word of scalar means. The
reference state sets the bus to zero only for the error comparison. Every
physical cleanup mean is present in the word and its residual is charged.
The destination has a reset rung; only the first bus cell needs a bus rung.
-/

set_option autoImplicit false

namespace OPH.SourceNativeShuttle
noncomputable section
open OPH.SourceEncodedMemory OPH.SourceReusableBus OPH.SourceBusScaling

def Bounded (A : ℝ) (a : ℕ → ℝ) : Prop := ∀ i, |a i| ≤ A

theorem step_bounded (op : Instruction ℕ) (A : ℝ) (a : ℕ → ℝ)
    (hA : 0 ≤ A) (ha : Bounded A a) : Bounded A (step op a) := by
  intro i
  cases op with
  | clear t =>
    by_cases hi : i = t
    · simp [step, cleared, hi, hA]
    · simpa [step, cleared, hi] using ha i
  | copy s t =>
    by_cases hi : i = s ∨ i = t
    · have hs := abs_le.mp (ha s)
      have ht := abs_le.mp (ha t)
      simp only [step, copied, ite_eq_left hi]
      apply abs_le.mpr
      constructor <;> linarith
    · simpa [step, copied, hi] using ha i

theorem execute_bounded (ops : List (Instruction ℕ)) (A : ℝ) (a : ℕ → ℝ)
    (hA : 0 ≤ A) (ha : Bounded A a) : Bounded A (execute ops a) := by
  induction ops generalizing a with
  | nil => exact ha
  | cons op ops ih => exact ih _ (step_bounded op A a hA ha)

theorem carry_blanks (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 < j → j ≤ n → a j = 0) :
    carry a n = a 0/(2:ℝ)^n := by
  induction n with
  | zero => simp [carry]
  | succ n ih =>
    rw [carry, ih (fun j hj hk => ha j hj (by omega)),
      ha (n+1) (by omega) (by omega)]
    simp [pow_succ, div_div]

def pickup (n : ℕ) : List (Instruction ℕ) :=
  [.clear (n+1), .copy (n+2) 0]

def transfer (n : ℕ) : List (Instruction ℕ) := pickup n ++ forward (n+1)

def handoff (n k : ℕ) : List (Instruction ℕ) :=
  transfer n ++ cleaning n ((n+1)^2*k)

def reference (n : ℕ) (a : ℕ → ℝ) : ℕ → ℝ :=
  fun i => if i = n+2 then a (n+2)/2 else
    if i = n+1 then a (n+2)/(2:ℝ)^(n+2) else if i ≤ n then 0 else a i

def residual (n k : ℕ) (A : ℝ) : ℝ :=
  A*mass n/(2*(n:ℝ)+1)*(1/2:ℝ)^k

theorem pickup_root (n : ℕ) (a : ℕ → ℝ) (h0 : a 0 = 0) :
    execute (pickup n) a 0 = a (n+2)/2 := by
  simp [pickup, execute, step, copied, cleared, h0]

theorem pickup_blanks (n j : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i ≤ n, a i = 0) (hj : 0 < j) (hk : j ≤ n+1) :
    execute (pickup n) a j = 0 := by
  have hs : j ≠ n+2 := by omega
  have hz : j ≠ 0 := by omega
  by_cases hd : j = n+1
  · simp [pickup, execute, step, copied, cleared, hd]
  · have h := ha j (by omega)
    simp [pickup, execute, step, copied, cleared, hs, hz, hd, h]

theorem transfer_receiver (n : ℕ) (a : ℕ → ℝ) (ha : ∀ i ≤ n, a i = 0) :
    execute (transfer n) a (n+1) = a (n+2)/(2:ℝ)^(n+2) := by
  rw [transfer, execute_append, forward_last,
    carry_blanks (n+1) _ (fun j hj hk => pickup_blanks n j a ha hj hk),
    pickup_root n a (ha 0 (by omega))]
  rw [div_div]
  congr 1
  rw [show n+2 = (n+1)+1 by omega, pow_succ]
  ring

theorem transfer_source (n : ℕ) (a : ℕ → ℝ) (h0 : a 0 = 0) :
    execute (transfer n) a (n+2) = a (n+2)/2 := by
  rw [transfer, execute_append, forward_later (n+1) (n+2) _ (by omega)]
  simp [pickup, execute, step, copied, cleared, h0]

theorem transfer_outside (n j : ℕ) (a : ℕ → ℝ) (hj : n+2 < j) :
    execute (transfer n) a j = a j := by
  rw [transfer, execute_append, forward_later (n+1) j _ (by omega)]
  simp [pickup, execute, step, copied, cleared,
    show j ≠ n+2 by omega, show j ≠ n+1 by omega, show j ≠ 0 by omega]

theorem handoff_receiver (n k : ℕ) (a : ℕ → ℝ) (ha : ∀ i ≤ n, a i = 0) :
    execute (handoff n k) a (n+1) = a (n+2)/(2:ℝ)^(n+2) := by
  rw [handoff, execute_append, cleaning_archives n _ (n+1) _ (by omega)]
  exact transfer_receiver n a ha

theorem handoff_source (n k : ℕ) (a : ℕ → ℝ) (h0 : a 0 = 0) :
    execute (handoff n k) a (n+2) = a (n+2)/2 := by
  rw [handoff, execute_append, cleaning_archives n _ (n+2) _ (by omega)]
  exact transfer_source n a h0

theorem handoff_outside (n k j : ℕ) (a : ℕ → ℝ) (hj : n+2 < j) :
    execute (handoff n k) a j = a j := by
  rw [handoff, execute_append, cleaning_archives n _ j _ (by omega)]
  exact transfer_outside n j a hj

theorem handoff_bus (n k i : ℕ) (a : ℕ → ℝ) (A : ℝ)
    (hn : 1 ≤ n) (hi : i ≤ n) (hA : 0 ≤ A) (ha : Bounded A a) :
    |execute (handoff n k) a i| ≤ residual n k A := by
  rw [handoff, execute_append]
  exact cleanup_blocks n k i _ A hn hi hA
    (fun j _ => execute_bounded (transfer n) A a hA ha j)

theorem residual_nonneg (n k : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    0 ≤ residual n k A := by unfold residual mass; positivity

/-- The source and destination identities are exact in the ideal word.
Only the bus projection contributes to the comparison error. -/
theorem handoff_error (n k : ℕ) (a : ℕ → ℝ) (A : ℝ)
    (hn : 1 ≤ n) (hA : 0 ≤ A) (ha : Bounded A a)
    (hz : ∀ i ≤ n, a i = 0) :
    Near (residual n k A) (execute (handoff n k) a) (reference n a) := by
  intro i
  by_cases hs : i = n+2
  · subst i
    simp [reference, handoff_source n k a (hz 0 (by omega)), residual_nonneg n k A hA]
  by_cases ht : i = n+1
  · subst i
    simp [reference, handoff_receiver n k a hz, residual_nonneg n k A hA]
  by_cases hb : i ≤ n
  · simpa [reference, hs, ht, hb] using handoff_bus n k i a A hn hb hA ha
  · have ho : n+2 < i := by omega
    simp [reference, hs, ht, hb, handoff_outside n k i a ho, residual_nonneg n k A hA]

theorem handoff_native_error (n k : ℕ) (b A : ℝ) (a : ℕ → ℝ)
    (hn : 1 ≤ n) (hA : 0 ≤ A) (ha : Bounded A a)
    (hz : ∀ i ≤ n, a i = 0) :
    Near (residual n k A) (run (compile (handoff n k)) (encode b a))
      (encode b (reference n a)) := by
  rw [program_native]
  intro ⟨i,r⟩
  have h := handoff_error n k a A hn hA ha hz i
  cases r
  · change |(b+execute (handoff n k) a i)-(b+reference n a i)| ≤ _
    convert h using 1; congr 1; ring
  · change |(b-execute (handoff n k) a i)-(b-reference n a i)| ≤ _
    have hneg : |-(execute (handoff n k) a i-reference n a i)| ≤ residual n k A :=
      by simpa only [abs_neg] using h
    convert hneg using 1; congr 1; ring

theorem handoff_length (n k : ℕ) :
    (compile (handoff n k)).length =
      5+2*n+(1+2*n)*(n+1)^2*k := by
  simp [handoff, transfer, pickup, compile_append, compile, word, clearWord,
    copyWord, SourceBusScaling.forward_length, SourceBusScaling.cleaning_length]
  ring

def freshHandoff (n k : ℕ) : List (Instruction ℕ) :=
  [.copy (n+2) 0] ++ forward (n+1) ++ cleaning n ((n+1)^2*k)

theorem freshHandoff_eq (n k : ℕ) (a : ℕ → ℝ) (hz : a (n+1) = 0) :
    execute (freshHandoff n k) a = execute (handoff n k) a := by
  have hc : cleared (n+1) a = a := by
    ext i
    by_cases hi : i = n+1 <;> simp [cleared, hi, hz]
  simp only [freshHandoff, handoff, transfer, pickup, execute_append, execute, step, hc]

/-- A destination that is blank in the comparison state needs no reset
rung. Its physical residual remains in the propagated initial error. -/
theorem freshHandoff_native_error (n k : ℕ) (b A : ℝ) (a : ℕ → ℝ)
    (hn : 1 ≤ n) (hA : 0 ≤ A) (ha : Bounded A a)
    (hz : ∀ i ≤ n+1, a i = 0) :
    Near (residual n k A) (run (compile (freshHandoff n k)) (encode b a))
      (encode b (reference n a)) := by
  rw [program_native, freshHandoff_eq n k a (hz _ (by omega))]
  have h := handoff_native_error n k b A a hn hA ha (fun i hi => hz i (by omega))
  simpa only [program_native] using h

theorem freshHandoff_length (n k : ℕ) :
    (compile (freshHandoff n k)).length =
      4+2*n+(1+2*n)*(n+1)^2*k := by
  simp [freshHandoff, compile_append, compile, word, copyWord,
    SourceBusScaling.forward_length, SourceBusScaling.cleaning_length]
  ring

end
end OPH.SourceNativeShuttle

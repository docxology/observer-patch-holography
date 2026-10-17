module
public import Geometry.SourceNativeRecords

@[expose] public section

/-!
# Reusable native accumulation

Cell zero is a mutable accumulator, cell one a workspace, and cells at
least two are input records. Logical values use explicit dyadic scales.
Only scalar pair means write the state. Preparation, the input request
sequence, the supported placement and the publication instrument are inputs.
-/

set_option autoImplicit false

namespace OPH.SourceNativeAccumulator
noncomputable section
open OPH.SourceEncodedMemory OPH.SourceReusableBus OPH.SourceNativeRecords
open ObserverPatchHolography.ScalarSeamRepair

def represented (v : ℕ → ℝ) (e : ℕ → ℕ) : ℕ → ℝ :=
  fun i => v i / (2:ℝ)^(e i)

def shrink (s : ℕ) : ℕ → List (Instruction ℕ)
  | 0 => []
  | k+1 => halve s 1 ++ shrink s k

theorem shrink_formula (s k : ℕ) (hs : s ≠ 1) (a : ℕ → ℝ) (hw : a 1 = 0) :
    execute (shrink s k) a =
      fun i => if i = 1 then 0 else if i = s then a s/(2:ℝ)^k else a i := by
  induction k generalizing a with
  | zero =>
    ext i
    by_cases hi : i = 1 <;> by_cases hj : i = s <;> simp [shrink, execute, hi, hj, hw, hs]
  | succ k ih =>
    rw [shrink, execute_append, halve_formula s 1 a hs hw]
    rw [ih (fun i => if i = 1 then 0 else if i = s then a s/2 else a i)
      (by simp)]
    ext i
    by_cases hi : i = 1 <;> by_cases hj : i = s <;>
      simp [hi, hj, hs, pow_succ, div_div, mul_comm]

theorem shrink_length (s k : ℕ) : (compile (shrink s k)).length = 3*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [shrink, halve, compile, word, copyWord, clearWord, ih]; omega

def commonScale (s : ℕ) (e : ℕ → ℕ) : ℕ := max (e 0) (e s+1)

def addedScales (s : ℕ) (e : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if i = 0 then commonScale s e+1 else if i = s then commonScale s e else e i

def addedValues (s : ℕ) (v : ℕ → ℝ) : ℕ → ℝ :=
  fun i => if i = 0 then v 0+v s else v i

def addWord (s : ℕ) (e : ℕ → ℕ) : List (Instruction ℕ) :=
  shrink 0 (commonScale s e-e 0) ++
  shrink s (commonScale s e-(e s+1)) ++
  [.copy s 1, .copy 0 1, .clear 1]

theorem divide_scale (x : ℝ) (j k : ℕ) (h : j ≤ k) :
    (x/(2:ℝ)^j)/(2:ℝ)^(k-j) = x/(2:ℝ)^k := by
  rw [div_div, ← pow_add, Nat.add_sub_of_le h]

/-- One addition changes only the accumulator and the source's representation
scale. The source's decoded value survives; the workspace is blank again. -/
theorem add_formula (s : ℕ) (hs : 2 ≤ s) (v : ℕ → ℝ) (e : ℕ → ℕ)
    (hw : v 1 = 0) :
    execute (addWord s e) (represented v e) =
      represented (addedValues s v) (addedScales s e) := by
  have hs0 : s ≠ 0 := by omega
  have hs1 : s ≠ 1 := by omega
  have h0 : e 0 ≤ commonScale s e := Nat.le_max_left _ _
  have h1 : e s+1 ≤ commonScale s e := Nat.le_max_right _ _
  rw [addWord, execute_append, execute_append]
  rw [shrink_formula 0 _ (by decide) _ (by simp [represented, hw])]
  rw [shrink_formula s _ hs1 _ (by simp)]
  have hx := divide_scale (v 0) (e 0) (commonScale s e) h0
  have hy : (v s/(2:ℝ)^(e s))/(2:ℝ)^(commonScale s e-(e s+1))/2 =
      v s/(2:ℝ)^(commonScale s e) := by
    have he : e s + (commonScale s e-(e s+1)+1) = commonScale s e := by omega
    rw [div_div, div_div, ← pow_succ, ← pow_add, he]
  ext i
  by_cases hi0 : i = 0
  · subst i
    simp [execute, step, copied, cleared, represented, addedValues, addedScales,
      hs0, hs1, hs0.symm, hs1.symm, hx]
    rw [hy]
    rw [pow_succ]
    ring
  by_cases hi1 : i = 1
  · subst i
    simp [execute, step, cleared, represented, addedValues, addedScales, hw]
  by_cases his : i = s
  · subst i
    simp [execute, step, copied, cleared, represented, addedValues, addedScales,
      hs0, hs1]
    exact hy
  · simp [execute, step, copied, cleared, represented, addedValues, addedScales,
      hi0, hi1, his]

theorem add_length (s : ℕ) (e : ℕ → ℕ) :
    (compile (addWord s e)).length =
      3*(commonScale s e-e 0) + 3*(commonScale s e-(e s+1)) + 5 := by
  simp [addWord, compile_append, shrink_length, compile, word, copyWord, clearWord]
  omega

theorem added_scales_bound (s M : ℕ) (e : ℕ → ℕ) (h : ∀ i, e i ≤ M) :
    ∀ i, addedScales s e i ≤ M+2 := by
  intro i
  have h0 := h 0
  have hs := h s
  have hc : commonScale s e ≤ M+1 := by simp only [commonScale]; omega
  simp only [addedScales]
  split_ifs <;> have hi := h i <;> omega

theorem add_cost_bound (s M : ℕ) (e : ℕ → ℕ) (h : ∀ i, e i ≤ M) :
    (compile (addWord s e)).length ≤ 8+3*M := by
  rw [add_length]
  have h0 := h 0
  have hs := h s
  unfold commonScale
  omega

def accumulatedScales : List ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | [], e => e
  | s::ss, e => accumulatedScales ss (addedScales s e)

def accumulatedValues : List ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | [], v => v
  | s::ss, v => accumulatedValues ss (addedValues s v)

def accumulation : List ℕ → (ℕ → ℕ) → List (Instruction ℕ)
  | [], _ => []
  | s::ss, e => addWord s e ++ accumulation ss (addedScales s e)

theorem accumulation_formula (ss : List ℕ) (hss : ∀ s ∈ ss, 2 ≤ s)
    (v : ℕ → ℝ) (e : ℕ → ℕ) (hw : v 1 = 0) :
    execute (accumulation ss e) (represented v e) =
      represented (accumulatedValues ss v) (accumulatedScales ss e) := by
  induction ss generalizing v e with
  | nil => rfl
  | cons s ss ih =>
    rw [accumulation, execute_append, add_formula s (hss s (by simp)) v e hw]
    exact ih (fun t ht => hss t (by simp [ht])) _ _ (by simp [addedValues, hw])

theorem accumulated_input (ss : List ℕ) (v : ℕ → ℝ) (i : ℕ) (hi : i ≠ 0) :
    accumulatedValues ss v i = v i := by
  induction ss generalizing v with
  | nil => rfl
  | cons s ss ih => simpa [accumulatedValues, addedValues, hi] using ih (addedValues s v)

/-- Every requested value contributes, including repeated reads of one input.
Input identities are separated from the accumulator and workspace. -/
theorem accumulated_sum (ss : List ℕ) (hss : ∀ s ∈ ss, 2 ≤ s) (v : ℕ → ℝ) :
    accumulatedValues ss v 0 = v 0 + (ss.map v).sum := by
  induction ss generalizing v with
  | nil => simp [accumulatedValues]
  | cons s ss ih =>
    have hs : s ≠ 0 := by have := hss s (by simp); omega
    have ht : ∀ t ∈ ss, 2 ≤ t := fun t ht => hss t (by simp [ht])
    have hm : ss.map (addedValues s v) = ss.map v := by
      apply List.map_congr_left
      intro t ht'
      have hne : t ≠ 0 := by have := ht t ht'; omega
      simp [addedValues, hne]
    rw [accumulatedValues, ih ht, hm]
    simp [addedValues]
    ring

theorem accumulated_scales_bound (ss : List ℕ) (e : ℕ → ℕ) (M : ℕ)
    (h : ∀ i, e i ≤ M) : ∀ i, accumulatedScales ss e i ≤ M+2*ss.length := by
  induction ss generalizing e M with
  | nil => simpa [accumulatedScales] using h
  | cons s ss ih =>
    have hb := ih (addedScales s e) (M+2) (added_scales_bound s M e h)
    simpa [accumulatedScales, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hb

/-- Quadratic sufficient native work for an arbitrary finite request list.
Every scale-alignment mean and workspace clear is included. -/
theorem accumulation_cost_bound (ss : List ℕ) (e : ℕ → ℕ) (M : ℕ)
    (h : ∀ i, e i ≤ M) :
    (compile (accumulation ss e)).length ≤ 3*ss.length*(M+ss.length)+5*ss.length := by
  induction ss generalizing e M with
  | nil => simp [accumulation, compile]
  | cons s ss ih =>
    have ha := add_cost_bound s M e h
    have ht := ih (addedScales s e) (M+2) (added_scales_bound s M e h)
    simp only [accumulation, compile_append, List.length_append, List.length_cons]
    nlinarith

def resetWord (s t : ℕ) : List ((ℕ × Bool) × (ℕ × Bool)) :=
  copyWord s t ++ [((s,false),(t,true)),((s,true),(t,false))]

/-- A supported four-edge rectangle clears both encoded amplitudes using
four means. No fresh blank or direct edge between either cell's rails is
needed. Implementation error is not reset by this ideal identity. -/
theorem reset_rectangle (s t : ℕ) (hne : s ≠ t) (b : ℝ) (a : ℕ → ℝ) :
    run (resetWord s t) (encode b a) = encode b (cleared s (cleared t a)) := by
  rw [resetWord, run_append, copy_native]
  ext ⟨i,r⟩
  cases r <;> by_cases hs : i = s <;> by_cases ht : i = t <;>
    simp [run, pairAverage, encode, copied, cleared, hs, ht, hne, hne.symm] <;> ring

def startedValues (v : ℕ → ℝ) : ℕ → ℝ :=
  fun i => if i = 0 then v 2 else if i = 1 then 0 else v i

def startedScales (e : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if i = 0 ∨ i = 2 then e 2+1 else e i

def startWord : List ((ℕ × Bool) × (ℕ × Bool)) :=
  resetWord 0 1 ++ copyWord 2 0

/-- Reuse the existing seed record. Its logical value survives at a smaller
amplitude; no unit-valued write is made after preparation. -/
theorem start_native (b : ℝ) (v : ℕ → ℝ) (e : ℕ → ℕ) :
    run startWord (encode b (represented v e)) =
      encode b (represented (startedValues v) (startedScales e)) := by
  rw [startWord, run_append, reset_rectangle 0 1 (by decide), copy_native]
  congr 1
  ext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;>
    simp [represented, startedValues, startedScales, copied, cleared, h0, h1, h2,
      pow_succ, div_div]

theorem start_length : startWord.length = 6 := rfl

theorem started_scales_bound (e : ℕ → ℕ) (M : ℕ) (h : ∀ i, e i ≤ M) :
    ∀ i, startedScales e i ≤ M+1 := by
  intro i
  have h2 := h 2
  have hi := h i
  simp only [startedScales]
  split_ifs <;> omega

def episodeWord (ss : List ℕ) (e : ℕ → ℕ) : List ((ℕ × Bool) × (ℕ × Bool)) :=
  startWord ++ compile (accumulation ss (startedScales e))

def episodeScales (ss : List ℕ) (e : ℕ → ℕ) : ℕ → ℕ :=
  accumulatedScales ss (startedScales e)

def episodeValues (ss : List ℕ) (v : ℕ → ℝ) : ℕ → ℝ :=
  accumulatedValues ss (startedValues v)

theorem episode_native (ss : List ℕ) (hss : ∀ s ∈ ss, 2 ≤ s)
    (b : ℝ) (v : ℕ → ℝ) (e : ℕ → ℕ) :
    run (episodeWord ss e) (encode b (represented v e)) =
      encode b (represented (episodeValues ss v) (episodeScales ss e)) := by
  rw [episodeWord, run_append, start_native, program_native,
    accumulation_formula ss hss _ _ (by simp [startedValues])]
  rfl

theorem episode_sum (ss : List ℕ) (hss : ∀ s ∈ ss, 2 ≤ s) (v : ℕ → ℝ) :
    episodeValues ss v 0 = v 2+(ss.map v).sum := by
  rw [episodeValues, accumulated_sum ss hss]
  have hm : ss.map (startedValues v) = ss.map v := by
    apply List.map_congr_left
    intro i hi
    have hh := hss i hi
    simp [startedValues, show i ≠ 0 by omega, show i ≠ 1 by omega]
  simp [hm, startedValues]

theorem episode_inputs (ss : List ℕ) (v : ℕ → ℝ) (i : ℕ) (hi : 2 ≤ i) :
    episodeValues ss v i = v i := by
  rw [episodeValues, accumulated_input ss _ i (by omega)]
  simp [startedValues, show i ≠ 0 by omega, show i ≠ 1 by omega]

end
end OPH.SourceNativeAccumulator

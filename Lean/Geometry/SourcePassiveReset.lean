module
public import Geometry.SourceNonlinearRecord

@[expose] public section

set_option autoImplicit false

namespace OPH.SourcePassiveReset

noncomputable section

open ObserverPatchHolography.ScalarSeamRepair
open SourceNonlinearRecord

variable {ι : Type*} [DecidableEq ι]

def run : List (ι × ι) → (ι → ℝ) → (ι → ℝ)
  | [], x => x
  | e :: es, x => run es (pairAverage e.1 e.2 x)

def touches (i : ι) : List (ι × ι) → ℕ
  | [] => 0
  | e :: es => (if i = e.1 ∨ i = e.2 then 1 else 0) + touches i es

theorem run_append (a b : List (ι × ι)) (x : ι → ℝ) :
    run (a ++ b) x = run b (run a x) := by
  induction a generalizing x with
  | nil => rfl
  | cons e es ih => exact ih _

theorem pairAverage_nonnegative (u v : ι) {x : ι → ℝ} (hx : Nonnegative x) :
    Nonnegative (pairAverage u v x) := by
  intro i
  by_cases h : i = u ∨ i = v
  · simp only [pairAverage, LinearMap.coe_mk, AddHom.coe_mk, h, ite_true]
    exact div_nonneg (add_nonneg (hx u) (hx v)) (by norm_num)
  · simpa [pairAverage, h] using hx i

theorem run_nonnegative (word : List (ι × ι)) {x : ι → ℝ} (hx : Nonnegative x) :
    Nonnegative (run word x) := by
  induction word generalizing x with
  | nil => exact hx
  | cons e es ih => exact ih (pairAverage_nonnegative e.1 e.2 hx)

/-- A nonnegative register retains at least half its old value per incident
mean. Other registers, including changing ancillas, are unrestricted except
for their nonnegativity. No return-to-initial-state hypothesis is used. -/
theorem incident_lower_bound (u v i : ι) (x : ι → ℝ) (hx : Nonnegative x)
    (hi : i = u ∨ i = v) : x i ≤ 2 * pairAverage u v x i := by
  rcases hi with rfl | rfl <;> simp only [pairAverage_left, pairAverage_right]
  · linarith [hx v]
  · linarith [hx u]

theorem retained_self_lower_bound (word : List (ι × ι)) (x : ι → ℝ)
    (hx : Nonnegative x) (i : ι) :
    x i ≤ (2 : ℝ) ^ touches i word * run word x i := by
  induction word generalizing x with
  | nil => simp [run, touches]
  | cons e es ih =>
    have h := ih (pairAverage e.1 e.2 x) (pairAverage_nonnegative e.1 e.2 hx)
    by_cases hi : i = e.1 ∨ i = e.2
    · have hs := incident_lower_bound e.1 e.2 i x hx hi
      simp only [touches, hi, ite_true, run, pow_add, pow_one]
      nlinarith
    · have hs := pairAverage_off_seam e.1 e.2 i x (fun h => hi (Or.inl h))
        (fun h => hi (Or.inr h))
      simpa [touches, hi, run, hs] using h

theorem positive_register_cannot_reset (word : List (ι × ι)) (x : ι → ℝ)
    (hx : Nonnegative x) (i : ι) (hi : 0 < x i) : 0 < run word x i := by
  have h := retained_self_lower_bound word x hx i
  have hp : 0 < (2 : ℝ)^touches i word := by positivity
  nlinarith

/-- A necessary operation count for any approximate native-zero reset.
It applies to each realized finite word, including a word selected adaptively. -/
theorem reset_tolerance_requires (word : List (ι × ι)) (x : ι → ℝ)
    (hx : Nonnegative x) (i : ι) (ε : ℝ) (hε : run word x i ≤ ε) :
    x i ≤ (2 : ℝ)^touches i word * ε := by
  exact (retained_self_lower_bound word x hx i).trans
    (mul_le_mul_of_nonneg_left hε (by positivity))

/-- Nat indexing describes a finite construction using exactly registers
0,...,m. Registers outside this set are never touched or allocated. -/
def coldWord : ℕ → List (ℕ × ℕ)
  | 0 => []
  | m+1 => coldWord m ++ [(0,m+1)]

def coldState (a : ℝ) (m i : ℕ) : ℝ :=
  if i = 0 then a / 2^m else if i ≤ m then a / 2^i else 0

theorem coldState_zero (a : ℝ) : coldState a 0 = Pi.single 0 a := by
  ext i
  by_cases hi : i = 0 <;> simp [coldState, hi]

theorem coldState_step (a : ℝ) (m : ℕ) :
    pairAverage 0 (m+1) (coldState a m) = coldState a (m+1) := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp [coldState, pow_succ]
    ring
  · by_cases hj : i = m+1
    · subst i
      simp [coldState, pow_succ]
      ring
    · rw [pairAverage_off_seam _ _ _ _ hi hj]
      have he : (i ≤ m+1) ↔ i ≤ m := by omega
      simp [coldState, hi, he]

theorem coldWord_exact (a : ℝ) (m : ℕ) :
    run (coldWord m) (Pi.single 0 a) = coldState a m := by
  induction m with
  | zero => simp [coldWord, run, coldState_zero]
  | succ m ih =>
    rw [coldWord, run_append, ih]
    exact coldState_step a m

theorem coldWord_residual (a : ℝ) (m : ℕ) :
    run (coldWord m) (Pi.single 0 a) 0 = a / 2^m := by
  rw [coldWord_exact]
  simp [coldState]

theorem coldWord_length (m : ℕ) : (coldWord m).length = m := by
  induction m <;> simp_all [coldWord]

theorem coldWord_support (m : ℕ) (e : ℕ × ℕ) (he : e ∈ coldWord m) :
    e.1 = 0 ∧ 0 < e.2 ∧ e.2 ≤ m := by
  induction m with
  | zero => simp [coldWord] at he
  | succ m ih =>
    simp only [coldWord, List.mem_append, List.mem_singleton] at he
    rcases he with he | he
    · obtain ⟨hl, hp, hu⟩ := ih he
      exact ⟨hl, hp, by omega⟩
    · subst e
      simp

/-- The allegedly fresh zero is zero because it has not been touched.
After use its state is explicitly retained as a/2^(m+1), not erased. -/
theorem coldWord_next_zero (a : ℝ) (m : ℕ) :
    run (coldWord m) (Pi.single 0 a) (m+1) = 0 := by
  rw [coldWord_exact]
  simp [coldState]

end
end OPH.SourcePassiveReset

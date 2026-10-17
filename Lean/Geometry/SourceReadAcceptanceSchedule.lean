module
public import Geometry.SourceReadAcceptance

@[expose] public section

/-!
# Complete finite histories and native stopping work

Every event identity remains in the finite word space. A stopped physical
prefix is distinct from its full probabilistic history. The recurrences are
uniform counting laws on a supplied alphabet, not a source selection theorem.
-/

set_option autoImplicit false

namespace OPH.SourceReadAcceptanceSchedule
noncomputable section
open OPH.SourceReadAcceptance

def History (d : ℕ) : ℕ → Type
  | 0 => Unit
  | n+1 => History d n × Fin d

instance historyFinite (d n : ℕ) : Fintype (History d n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact @instFintypeProd _ _ ih inferInstance

def letters {d : ℕ} : {n : ℕ} → History d n → List ℕ
  | 0, _ => []
  | _+1, h => letters h.1 ++ [h.2.val]

def frontier {d : ℕ} : {n : ℕ} → History d n → ℕ
  | 0, _ => 0
  | _+1, h => advance (frontier h.1) h.2.val

def stopped {d : ℕ} : {n : ℕ} → History d n → List ℕ
  | 0, _ => []
  | _+1, h => if frontier h.1 < d then stopped h.1 ++ [h.2.val] else stopped h.1

def cost {d n : ℕ} (h : History d n) : ℕ := 2*(stopped h).length

theorem history_card (d n : ℕ) : Fintype.card (History d n) = d^n := by
  induction n with
  | zero => exact @Fintype.card_unique Unit inferInstance (historyFinite d 0)
  | succ n ih => simp [History, Fintype.card_prod, ih, pow_succ]

theorem letters_length {d n : ℕ} (h : History d n) : (letters h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [letters, ih]

theorem progress_append (xs ys : List ℕ) (k : ℕ) :
    progress k (xs++ys) = progress (progress k xs) ys := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => exact ih (advance k x)

theorem history_frontier {d n : ℕ} (h : History d n) :
    frontier h = progress 0 (letters h) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [frontier, letters, progress_append, progress, ih]

theorem frontier_bound {d n : ℕ} (h : History d n) : frontier h ≤ d := by
  induction n with
  | zero => exact Nat.zero_le d
  | succ n ih =>
    have hb := ih h.1
    have hm := h.2.isLt
    simp only [frontier, advance]
    split_ifs <;> omega

/-- A complete history and its stopped physical prefix have identical final
influence frontiers. No unexecuted suffix is needed for the claimed read. -/
theorem stopped_frontier {d n : ℕ} (h : History d n) :
    progress 0 (stopped h) = frontier h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hf : frontier h.1 < d
    · simp [stopped, hf, progress_append, progress, ih, frontier]
    · have he : frontier h.1 = d := by have hb := frontier_bound h.1; omega
      simp [stopped, ih, frontier, he, completed_frontier_absorbs]

theorem stopped_length_bound {d n : ℕ} (h : History d n) : (stopped h).length ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hb := ih h.1
    by_cases hf : frontier h.1 < d
    · simpa only [stopped, ite_eq_left hf, List.length_append, List.length_singleton]
        using Nat.add_le_add_right hb 1
    · simpa only [stopped, ite_eq_right hf] using hb.trans (Nat.le_succ n)

theorem cost_step {d n : ℕ} (h : History d n) (move : Fin d) :
    cost (d:=d) (n:=n+1) (h,move) = cost h + if frontier h < d then 2 else 0 := by
  unfold cost
  simp only [stopped]
  split_ifs
  · simp only [List.length_append, List.length_singleton]
    omega
  · omega

/-- The scalar mean count is the actual native compilation length of the
stopped word, including every unsuccessful attempt before the deadline. -/
theorem stopped_native_cost {d n : ℕ} (h : History d n) :
    (OPH.SourceReusableBus.compile
      (paired ((stopped h).map fun j => (j,j+1)))).length = cost h := by
  simp [paired_cost, cost]

theorem stopped_native_frontier {d n : ℕ} (h : History d n)
    (amplitude : ℝ) (ha : 0 < amplitude) :
    ∀ i, 0 < OPH.SourceEncodedMemory.run ((stopped h).map fun j => (j,j+1))
      (OPH.SourceEncodedMemory.signal 0 amplitude) i ↔ i ≤ frontier h := by
  simpa [stopped_frontier] using source_path_frontier (stopped h) amplitude ha

/-- Exact weighted counting of the unique advancing letter. -/
theorem one_step_reward (d k : ℕ) (hk : k ≤ d) (reward : ℕ → ℝ) :
    (∑ move : Fin d, reward (advance k move.val)) =
      if k < d then (d:ℝ)*reward k + (reward (k+1)-reward k) else (d:ℝ)*reward k := by
  classical
  by_cases hf : k < d
  · rw [ite_eq_left hf]
    have he (move : Fin d) : reward (advance k move.val) =
        reward k + if move.val = k then reward (k+1)-reward k else 0 := by
      unfold advance; split_ifs <;> ring
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    have single : (∑ move : Fin d, if move.val = k then reward (k+1)-reward k else 0) =
        reward (k+1)-reward k := by
      rw [Finset.sum_eq_single (⟨k,hf⟩ : Fin d)]
      · simp
      · intro b _ hb
        have hne : b.val ≠ k := fun he => hb (Fin.ext he)
        simp [hne]
      · simp
    rw [single]
    simp
  · have he : k = d := by omega
    subst k
    simp [completed_frontier_absorbs]

/-- A recurrence over the entire finite history space, with no discarded
failed histories or conditioning. Indicator rewards give exact arrival laws. -/
theorem full_history_reward (d n : ℕ) (reward : ℕ → ℝ) :
    (∑ h : History d (n+1), reward (frontier h)) =
      ∑ h : History d n,
        if frontier h < d then (d:ℝ)*reward (frontier h) +
          (reward (frontier h+1)-reward (frontier h)) else (d:ℝ)*reward (frontier h) := by
  change (∑ h : History d n × Fin d, reward (advance (frontier h.1) h.2.val)) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  exact one_step_reward d (frontier h) (frontier_bound h) reward

/-- Dividing by d^(n+1) gives the unconditional expected-work recurrence.
The added work is two scalar means for every unfinished prefix and every
possible next letter, including letters that make no progress. -/
theorem full_history_cost (d n : ℕ) :
    (∑ h : History d (n+1), (cost h:ℝ)) =
      (d:ℝ)*(∑ h : History d n, (cost h:ℝ)) +
      2*d*(∑ h : History d n, if frontier h < d then (1:ℝ) else 0) := by
  classical
  change (∑ h : History d n × Fin d, (cost (d:=d) (n:=n+1) h:ℝ)) = _
  rw [Fintype.sum_prod_type]
  have step (h : History d n) (move : Fin d) : (cost (d:=d) (n:=n+1) (h,move):ℝ) =
      (cost h:ℝ) + if frontier h < d then 2 else 0 := by
    rw [cost_step]
    split_ifs <;> simp
  simp_rw [step]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have indicator (h : History d n) : (if frontier h < d then (2:ℝ) else 0) =
      2*(if frontier h < d then (1:ℝ) else 0) := by split_ifs <;> ring
  simp_rw [indicator]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end
end OPH.SourceReadAcceptanceSchedule

module
public import Geometry.SourceTemporalGuard

@[expose] public section

/-!
# Unconditional proposal counts for native completion

Any fixed completing block yields a finite-horizon failure bound under
uniform full proposal words. All rejected and unsuccessful proposals remain
in the denominator. This counting theorem does not derive a uniform or
independent proposal law from the full axioms.
-/

set_option autoImplicit false

namespace OPH.SourceTemporalAttempts
noncomputable section

variable {E : Type*} [Fintype E]

def avoidEquiv (B k : ℕ) (word : Fin B → E) :
    {w : Fin k → Fin B → E // ∀ i, w i ≠ word} ≃
      (Fin k → {v : Fin B → E // v ≠ word}) where
  toFun w i := ⟨w.1 i,w.2 i⟩
  invFun w := ⟨fun i => (w i).1,fun i => (w i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem avoiding_block_count (B k : ℕ) (word : Fin B → E) :
    Nat.card {w : Fin k → Fin B → E // ∀ i, w i ≠ word} =
      (Fintype.card E ^ B - 1) ^ k := by
  classical
  rw [Nat.card_congr (avoidEquiv B k word),Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype_compl]

/-- Every run lacking completion avoids the fixed completing block in each
disjoint block position. This bound charges every proposal word. -/
theorem failure_count (B k : ℕ) (word : Fin B → E)
    (success : (Fin k → Fin B → E) → Prop)
    (hit : ∀ w, (∃ i, w i = word) → success w) :
    Nat.card {w : Fin k → Fin B → E // ¬ success w} ≤
      (Fintype.card E ^ B - 1) ^ k := by
  classical
  have hsub : {w : Fin k → Fin B → E | ¬ success w} ⊆
      {w | ∀ i, w i ≠ word} := by
    intro w hw i he
    exact hw (hit w ⟨i,he⟩)
  have h := Set.ncard_le_ncard hsub
  exact h.trans_eq (avoiding_block_count B k word)

theorem full_attempt_count (B k : ℕ) :
    Fintype.card (Fin k → Fin B → E) = (Fintype.card E ^ B) ^ k := by simp

/-- The exact full-simplex denominator is positive whenever the completing
word exists, including the empty-word case. -/
theorem attempt_denominator_positive (B k : ℕ) (word : Fin B → E) :
    0 < (Fintype.card E ^ B) ^ k := by
  have hi : Nonempty (Fin B → E) := ⟨word⟩
  have h : 0 < Fintype.card (Fin B → E) := Fintype.card_pos_iff.mpr hi
  simpa using pow_pos h k

theorem failure_fraction (B k : ℕ) (word : Fin B → E)
    (success : (Fin k → Fin B → E) → Prop)
    (hit : ∀ w, (∃ i, w i = word) → success w) :
    (Nat.card {w : Fin k → Fin B → E // ¬ success w} : ℝ) /
        Fintype.card (Fin k → Fin B → E) ≤
      ((Fintype.card E ^ B - 1 : ℕ) : ℝ) ^ k /
        ((Fintype.card E ^ B : ℕ) : ℝ) ^ k := by
  rw [full_attempt_count]
  push_cast
  apply div_le_div_of_nonneg_right
  · exact_mod_cast failure_count B k word success hit
  · positivity

def blockProgram {P : Type*} {B k : ℕ} (seam : E → P × P)
    (w : Fin k → Fin B → E) : List (P × P) :=
  (List.ofFn (fun i => (List.ofFn (w i)).map seam)).flatten

omit [Fintype E] in
theorem block_occurrence [_instFintypeE : Fintype E] {P : Type*} (B k : ℕ) (seam : E → P × P)
    (word : Fin B → E) (w : Fin k → Fin B → E) (hit : ∃ i, w i = word) :
    ∃ before after, blockProgram seam w = before ++ (List.ofFn word).map seam ++ after := by
  obtain ⟨i,hi⟩ := hit
  have hm : (List.ofFn word).map seam ∈
      List.ofFn (fun j => (List.ofFn (w j)).map seam) := by
    apply List.mem_ofFn.mpr
    exact ⟨i,by rw [hi]⟩
  obtain ⟨before,after,he⟩ := List.mem_iff_append.mp hm
  refine ⟨before.flatten,after.flatten,?_⟩
  unfold blockProgram
  rw [he]
  simp only [List.flatten_append,List.flatten_cons,List.append_assoc]

/-- Composition with the native guard theorem: the failure count concerns
actual guarded executions of proposal words, not an abstract success oracle.
The alphabet-to-seam map and encoding of the topology-derived word are
explicit, so their identities cannot be replaced by a quotient count. -/
theorem guarded_failure_count {P X : Type*} [DecidableEq P] {root : P}
    (plan : SourceTemporalTomography.Plan root {root})
    (c : SourceTemporalGuard.Checkpoint X P)
    (hp : SourceTemporalGuard.Protected c) (hr : SourceTemporalGuard.HasRoot root c)
    (B k : ℕ) (seam : E → P × P) (word : Fin B → E)
    (encoded : (List.ofFn word).map seam = SourceTemporalTomography.lower plan) :
    Nat.card {w : Fin k → Fin B → E //
      ¬ Function.Injective (SourceTemporalGuard.guardedRun root (blockProgram seam w) c).record} ≤
      (Fintype.card E ^ B - 1) ^ k := by
  apply failure_count B k word
  intro w hit
  obtain ⟨before,after,he⟩ := block_occurrence B k seam word w hit
  rw [he,encoded]
  exact SourceTemporalGuard.completing_occurrence plan before after c hp hr

end
end OPH.SourceTemporalAttempts

module
public import Geometry.SourceTemporalObservation
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# Essential direct reads and the aggregate-read boundary

For a supplied linear record meaning, unrestricted direct coordinate reads
must include every coordinate with a nonzero coefficient, and that condition
is sufficient. Aggregate observations obey a different condition. Neither
the coefficient vector nor a metric radius is selected by this theorem.
-/

set_option autoImplicit false

namespace OPH.SourceTemporalMenu
noncomputable section
open OPH.SourceTemporalObservation

variable {N : Type*} [Fintype N] [DecidableEq N]

def coordinate (j : N) : (N → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj j

def meaning (c : N → ℝ) : (N → ℝ) →ₗ[ℝ] ℝ := ∑ j, c j • coordinate j

omit [DecidableEq N] in
theorem meaning_apply [_instDecidableEqN : DecidableEq N] (c x : N → ℝ) : meaning c x = ∑ j, c j*x j := by
  simp [meaning,coordinate]

theorem meaning_single (c : N → ℝ) (j : N) : meaning c (Pi.single j 1) = c j := by
  classical
  simp [meaning_apply,Pi.single_apply]

def direct (S : Finset N) : {j // j ∈ S} → (N → ℝ) →ₗ[ℝ] ℝ :=
  fun j => coordinate j.val

/-- The menu of reconstructible individual records is computed from the
observation interface, independently of a desired metric-neighbour menu. -/
def availableMenu {I : Type*} [Fintype I]
    (L : I → (N → ℝ) →ₗ[ℝ] ℝ) : Set N := {j | Observable L (coordinate j)}

omit [Fintype N] [DecidableEq N] in
theorem availableMenu_iff_kernel [_instFintypeN : Fintype N] [_instDecidableEqN : DecidableEq N] {I : Type*} [Fintype I]
    (L : I → (N → ℝ) →ₗ[ℝ] ℝ) (j : N) :
    j ∈ availableMenu L ↔ ∀ z, (∀ i, L i z = 0) → z j = 0 := by
  rw [availableMenu,Set.mem_ofPred_eq,observable_iff_kernel]
  constructor
  · intro h z hz
    exact h ((Submodule.mem_iInf _).mpr hz)
  · intro h z hz
    exact h z ((Submodule.mem_iInf _).mp hz)

/-- A deletion witness is an intervention in one unread coordinate.
The proof does not inspect payload values or supply an expected answer. -/
theorem direct_observable_iff (S : Finset N) (c : N → ℝ) :
    Observable (direct S) (meaning c) ↔ ∀ j, c j ≠ 0 → j ∈ S := by
  classical
  constructor
  · intro h j hc
    by_contra hj
    have he : meaning c (Pi.single j 1) = meaning c 0 := by
      apply h
      intro i
      have hn : i.val ≠ j := fun he => hj (he ▸ i.property)
      simp [direct,coordinate,hn]
    rw [meaning_single,map_zero] at he
    exact hc he
  · intro h x y hxy
    rw [meaning_apply,meaning_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hc : c j = 0
    · simp [hc]
    · have he := hxy ⟨j,h j hc⟩
      change x j = y j at he
      rw [he]

omit [DecidableEq N] in
/-- A fixed additive unit does not alter which initial records are required
for a specified one-plus-sum meaning. -/
theorem affine_agreement_iff [_instDecidableEqN : DecidableEq N] (c : N → ℝ) (b : ℝ) (x y : N → ℝ) :
    b+meaning c x = b+meaning c y ↔ meaning c x = meaning c y := by simp

def sumRead : Fin 1 → (Fin 2 → ℝ) →ₗ[ℝ] ℝ := fun _ => meaning (fun _ => 1)

theorem aggregate_sum_observable : Observable sumRead (meaning (fun _ : Fin 2 => 1)) := by
  intro x y h
  exact h 0

/-- Recovering a sum does not reconstruct its separate records. This blocks
inferring M1's individual read-from edges from recurrence agreement alone. -/
theorem aggregate_first_unobservable : ¬ Observable sumRead (coordinate (0 : Fin 2)) := by
  intro h
  have he := h ![1,0] ![0,1] (by
    intro i
    norm_num [sumRead,meaning_apply,Fin.sum_univ_two])
  norm_num [coordinate] at he

theorem aggregate_second_unobservable : ¬ Observable sumRead (coordinate (1 : Fin 2)) := by
  intro h
  have he := h ![1,0] ![0,1] (by
    intro i
    norm_num [sumRead,meaning_apply,Fin.sum_univ_two])
  norm_num [coordinate] at he

end
end OPH.SourceTemporalMenu

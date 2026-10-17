module
public import Geometry.SourceTemporalMenu
public import Mathlib.Logic.Function.DependsOn

@[expose] public section

/-!
# Required direct records for arbitrary finite product meanings

A coordinate is required precisely when varying it alone can change the
public meaning. For a finite independent product domain these coordinates
form the unique minimal direct-read set. Linearity is not needed. Selecting
the meaning and establishing the product domain are separate source duties;
correlated admissible preparations do not inherit this theorem unchanged.
-/

set_option autoImplicit false

namespace OPH.SourceTemporalEssential
noncomputable section

variable {N A B : Type*} [DecidableEq N]

def Essential (f : (N → A) → B) (i : N) : Prop :=
  ∃ x y, (∀ j, j ≠ i → x j = y j) ∧ f x ≠ f y

omit [DecidableEq N] in
theorem inessential_agreement [_instDecidableEqN : DecidableEq N] (f : (N → A) → B) (i : N) (hi : ¬ Essential f i)
    (x y : N → A) (h : ∀ j, j ≠ i → x j = y j) : f x = f y := by
  by_contra hn
  exact hi ⟨x,y,h,hn⟩

theorem inessential_finite_changes (f : (N → A) → B) (T : Finset N)
    (hT : ∀ j ∈ T, ¬ Essential f j) (x y : N → A)
    (hxy : ∀ j, j ∉ T → x j = y j) : f x = f y := by
  classical
  induction T using Finset.induction_on generalizing x y with
  | empty => exact congrArg f (funext (fun j => hxy j (by simp)))
  | @insert i T hi ih =>
    let z := Function.update x i (y i)
    have hfirst : f x = f z := by
      apply inessential_agreement f i (hT i (by simp))
      intro j hj
      simp [z,hj]
    have hrest : f z = f y := by
      apply ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)) z y
      intro j hj
      by_cases he : j=i
      · simp [z,he]
      · simpa [z,he] using hxy j (by simp [he,hj])
    exact hfirst.trans hrest

/-- Exact minimality, including nonlinear meanings on arbitrary value types.
The only read model here is direct access to independently variable records. -/
theorem dependsOn_iff_essential_subset [Fintype N] (f : (N → A) → B) (S : Set N) :
    DependsOn f S ↔ {i | Essential f i} ⊆ S := by
  classical
  constructor
  · intro h i hi
    by_contra hs
    obtain ⟨x,y,hxy,hf⟩ := hi
    apply hf
    apply h
    intro j hj
    exact hxy j (fun he => hs (he ▸ hj))
  · intro h x y hxy
    have hT : ∀ j ∈ Finset.univ.filter (fun j => j ∉ S), ¬ Essential f j := by
      intro j hj he
      exact (Finset.mem_filter.mp hj).2 (h he)
    exact inessential_finite_changes f _ hT x y (fun j hj => hxy j (by simpa using hj))

theorem essential_is_minimal [Fintype N] (f : (N → A) → B) :
    DependsOn f {i | Essential f i} ∧
      ∀ S, DependsOn f S → {i | Essential f i} ⊆ S := by
  constructor
  · exact (dependsOn_iff_essential_subset f _).mpr Set.Subset.rfl
  · intro S h
    exact (dependsOn_iff_essential_subset f S).mp h

omit [DecidableEq N] in
/-- A missing essential record supplies a deletion intervention that every
sound direct-read service must distinguish. -/
theorem omitted_record_witness [_instDecidableEqN : DecidableEq N] (f : (N → A) → B) (S : Set N) (i : N)
    (hi : Essential f i) (hs : i ∉ S) :
    ∃ x y, (∀ j ∈ S, x j = y j) ∧ f x ≠ f y := by
  obtain ⟨x,y,hxy,hf⟩ := hi
  exact ⟨x,y,fun j hj => hxy j (fun he => hs (he ▸ hj)),hf⟩

end
end OPH.SourceTemporalEssential

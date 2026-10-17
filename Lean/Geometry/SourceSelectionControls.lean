module
public import Geometry.SourceConstrainedSelection
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact constrained and observer-cover controls

The four-word example proves an optimizer over the complete affine feasible
family, not a numerical grid. The three-history example holds the feasible
family and faithful compatible reference fixed while changing the entropy
cover. Both covers determine the feasible state, but their unique minimizers
have different supports. These are finite classical controls of a proposed
selection inference, not full A1--A3 source countermodels.
-/

set_option autoImplicit false

namespace OPH.SourceSelectionControls
noncomputable section
open OPH.SourceConstrainedSelection

def wordReference (i : Fin 4) : ℝ := if i.val=0 then 1/8 else if i.val=1 then 3/8 else 1/4
def wordSelected (i : Fin 4) : ℝ := if i.val=0 then 3/16 else if i.val=1 then 9/16 else 1/8

theorem word_reference_positive : ∀ i, 0 < wordReference i := by
  intro i
  fin_cases i <;> norm_num [wordReference]

theorem word_selected_positive : ∀ i, 0 < wordSelected i := by
  intro i
  fin_cases i <;> norm_num [wordSelected]

theorem word_selected_constraints :
    wordSelected 0+wordSelected 1=3/4 ∧
    wordSelected 2+wordSelected 3=1/4 ∧
    (∑ i, wordSelected i)=1 := by
  norm_num [wordSelected, Fin.sum_univ_four,
    show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide]

/-- Conditioning the first letter's marginal does not make the selected
two-letter law independent. A zero determinant is necessary for a product. -/
theorem word_selected_correlated :
    wordSelected 0*wordSelected 3 ≠ wordSelected 1*wordSelected 2 := by
  norm_num [wordSelected]

theorem constrained_word_unique_minimum (q : Fin 4 → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hfirst : q 0+q 1=3/4) (hsecond : q 2+q 3=1/4) :
    weightedKL (fun _ => 1) wordReference wordSelected ≤
        weightedKL (fun _ => 1) wordReference q ∧
      (weightedKL (fun _ => 1) wordReference wordSelected =
        weightedKL (fun _ => 1) wordReference q ↔ q=wordSelected) := by
  apply affine_certificate_unique_minimum _ _ _ q (by intro i; norm_num)
    word_reference_positive word_selected_positive hq
  norm_num [Fin.sum_univ_four, wordSelected, wordReference,
    show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide]
  calc
    _ = (q 0+q 1-3/4)*Real.log (3/2) +
        (q 2+q 3-1/4)*Real.log (1/2) := by ring
    _ = 0 := by rw [hfirst,hsecond]; ring

def historyFamily (t : ℝ) (i : Fin 3) : ℝ := if i.val=0 then t else if i.val=1 then 1/2 else 1/2-t

def historyFeasible : Set (Fin 3 → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ p 0+p 1+p 2=1 ∧ p 1=1/2}

def coarseCover (p : Fin 3 → ℝ) (i : Fin 2) : ℝ := if i.val=0 then p 0+p 1 else p 2

def historyReference (i : Fin 3) : ℝ := if i.val=2 then 1/2 else 1/4
def coverReference (_ : Fin 2) : ℝ := 1/2
def fullSelected (i : Fin 3) : ℝ := if i.val=0 then 1/6 else if i.val=1 then 1/2 else 1/3

theorem historyFamily_feasible (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1/2) :
    historyFamily t ∈ historyFeasible := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [historyFamily] <;> linarith
  · norm_num [historyFamily]; ring
  · rfl

theorem historyFeasible_convex : Convex ℝ historyFeasible := by
  intro p hp q hq a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg ha (hp.1 i)) (mul_nonneg hb (hq.1 i))
  · change (a*p 0+b*q 0)+(a*p 1+b*q 1)+(a*p 2+b*q 2)=1
    calc
      _ = a*(p 0+p 1+p 2)+b*(q 0+q 1+q 2) := by ring
      _ = 1 := by rw [hp.2.1,hq.2.1]; simpa using hab
  · change a*p 1+b*q 1=1/2
    rw [hp.2.2,hq.2.2]
    nlinarith

/-- The coarse restriction loses a history coordinate on the ambient
simplex, yet it determines every state in this constrained feasible family. -/
theorem coarseCover_state_determining (p q : Fin 3 → ℝ)
    (hp : p ∈ historyFeasible) (hq : q ∈ historyFeasible)
    (h : coarseCover p=coarseCover q) : p=q := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  norm_num [coarseCover] at h0 h1
  funext i
  fin_cases i
  · change p 0=q 0
    linarith [hp.2.2,hq.2.2]
  · exact hp.2.2.trans hq.2.2.symm
  · exact h1

theorem history_atom_recovered_with_negative_offset (p : Fin 3 → ℝ)
    (hp : p ∈ historyFeasible) : p 0=coarseCover p 0-1/2 := by
  simp [coarseCover, hp.2.2]

theorem compatible_faithful_reference :
    (∀ i, 0 < historyReference i) ∧ (∑ i, historyReference i)=1 ∧
      coarseCover historyReference=coverReference ∧ (∀ j, 0 < coverReference j) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i; fin_cases i <;> norm_num [historyReference]
  · norm_num [historyReference, Fin.sum_univ_three]
  · ext j; fin_cases j <;> norm_num [coarseCover, historyReference, coverReference]
  · intro j; fin_cases j <;> norm_num [coverReference]

theorem coarse_selected_readout : coarseCover (historyFamily 0)=coverReference := by
  ext j
  fin_cases j <;> norm_num [coarseCover, historyFamily, coverReference]

/-- A faithful compatible reference and an injective feasible cover do not
force the union of feasible *history* supports. The actual scored cover
coordinates remain strictly positive, as the general theorem requires. -/
theorem coarse_cover_unique_minimum (p : Fin 3 → ℝ) (hp : p ∈ historyFeasible) :
    0 ≤ weightedKL (fun _ => 1) coverReference (coarseCover p) ∧
      (weightedKL (fun _ => 1) coverReference (coarseCover p)=0 ↔ p=historyFamily 0) := by
  have hr := compatible_faithful_reference.2.2.2
  have hnonneg : ∀ j, 0 ≤ coarseCover p j := by
    intro j
    fin_cases j
    · exact add_nonneg (hp.1 0) (hp.1 1)
    · exact hp.1 2
  refine ⟨weightedKL_nonnegative _ _ _ (by intro j; norm_num) hr hnonneg, ?_⟩
  rw [weightedKL_zero_iff _ _ _ (by intro j; norm_num) hr hnonneg]
  constructor
  · intro h
    apply coarseCover_state_determining p (historyFamily 0) hp
      (historyFamily_feasible 0 (by norm_num) (by norm_num))
    exact h.trans coarse_selected_readout.symm
  · rintro rfl
    exact coarse_selected_readout

theorem full_selected_feasible : fullSelected ∈ historyFeasible := by
  refine ⟨?_,?_,?_⟩
  · intro i; fin_cases i <;> norm_num [fullSelected]
  · norm_num [fullSelected]
  · norm_num [fullSelected]

theorem full_cover_unique_minimum (q : Fin 3 → ℝ) (hq : q ∈ historyFeasible) :
    weightedKL (fun _ => 1) historyReference fullSelected ≤
        weightedKL (fun _ => 1) historyReference q ∧
      (weightedKL (fun _ => 1) historyReference fullSelected =
        weightedKL (fun _ => 1) historyReference q ↔ q=fullSelected) := by
  have hp : ∀ i, 0 < fullSelected i := by
    intro i; fin_cases i <;> norm_num [fullSelected]
  apply affine_certificate_unique_minimum _ _ _ q (by intro i; norm_num)
    compatible_faithful_reference.1 hp hq.1
  norm_num [Fin.sum_univ_three, fullSelected, historyReference,
    show (2 : Fin 3) ≠ 0 by decide]
  calc
    _ = (q 0+q 2-1/2)*Real.log (2/3)+(q 1-1/2)*Real.log 2 := by ring
    _ = 0 := by
      have hsum : q 0+q 2=1/2 := by linarith [hq.2.1,hq.2.2]
      rw [hsum,hq.2.2]
      ring

theorem cover_choice_changes_support :
    historyFamily 0 ∈ historyFeasible ∧ fullSelected ∈ historyFeasible ∧
      historyFamily 0 0=0 ∧ 0 < fullSelected 0 ∧
      historyFamily (1/4) ∈ historyFeasible ∧ 0 < historyFamily (1/4) 0 := by
  refine ⟨historyFamily_feasible 0 (by norm_num) (by norm_num), full_selected_feasible,
    ?_, ?_, historyFamily_feasible (1/4) (by norm_num) (by norm_num), ?_⟩ <;>
    norm_num [historyFamily, fullSelected]

end
end OPH.SourceSelectionControls

module
public import Geometry.SourcePassiveReset

@[expose] public section

set_option autoImplicit false

namespace OPH.SourcePassiveMemoryBudget

noncomputable section

open ObserverPatchHolography.ScalarSeamRepair
open SourcePassiveReset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A scalar convexity ledger, not a derived physical energy. -/
def quadratic (x : ι → ℝ) : ℝ := ∑ i, (x i)^2

omit [DecidableEq ι] in
theorem quadratic_nonnegative (x : ι → ℝ) : 0 ≤ quadratic x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

theorem pairAverage_quadratic_defect (u v : ι) (x : ι → ℝ) :
    quadratic (pairAverage u v x) + (x u - x v)^2/2 = quadratic x := by
  by_cases huv : u = v
  · subst v
    simp [pairAverage_fixes_agreement]
  · have hpoint (i : ι) : (pairAverage u v x i)^2 - (x i)^2 =
        (if i = u then ((x u+x v)/2)^2-(x u)^2 else 0) +
        (if i = v then ((x u+x v)/2)^2-(x v)^2 else 0) := by
      by_cases hiu : i = u
      · subst i; simp [huv]
      · by_cases hiv : i = v
        · subst i; simp [Ne.symm huv]
        · simp [pairAverage_off_seam u v i x hiu hiv, hiu, hiv]
    have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpoint i)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
    unfold quadratic
    nlinarith [hsum]

def loss : List (ι × ι) → (ι → ℝ) → ℝ
  | [], _ => 0
  | e :: es, x => (x e.1-x e.2)^2/2 + loss es (pairAverage e.1 e.2 x)

omit [Fintype ι] in
theorem loss_nonnegative (word : List (ι × ι)) (x : ι → ℝ) : 0 ≤ loss word x := by
  induction word generalizing x with
  | nil => exact le_rfl
  | cons e es ih =>
    exact add_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) (ih _)

theorem quadratic_ledger (word : List (ι × ι)) (x : ι → ℝ) :
    quadratic (run word x) + loss word x = quadratic x := by
  induction word generalizing x with
  | nil => simp [run, loss]
  | cons e es ih =>
    have hs := pairAverage_quadratic_defect e.1 e.2 x
    have ht := ih (pairAverage e.1 e.2 x)
    simp only [run, loss]
    linarith

theorem quadratic_nonincreasing (word : List (ι × ι)) (x : ι → ℝ) :
    quadratic (run word x) ≤ quadratic x := by
  have h := quadratic_ledger word x
  linarith [loss_nonnegative word x]

def Quiescent : List (ι × ι) → (ι → ℝ) → Prop
  | [], _ => True
  | e :: es, x => x e.1 = x e.2 ∧ Quiescent es x

/-- Equality in the convexity ledger means that every scheduled seam joins
equal loads: an exact closed cycle cannot contain a nontrivial pair mean. -/
theorem quadratic_eq_iff_quiescent (word : List (ι × ι)) (x : ι → ℝ) :
    quadratic (run word x) = quadratic x ↔ Quiescent word x := by
  induction word generalizing x with
  | nil => simp [run, Quiescent]
  | cons e es ih =>
    constructor
    · intro h
      have ht := quadratic_nonincreasing es (pairAverage e.1 e.2 x)
      have hd := pairAverage_quadratic_defect e.1 e.2 x
      have hz : (x e.1-x e.2)^2 = 0 := by
        change quadratic (run es (pairAverage e.1 e.2 x)) = quadratic x at h
        nlinarith [sq_nonneg (x e.1-x e.2)]
      have he : x e.1 = x e.2 := sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
      refine ⟨he, (ih x).mp ?_⟩
      simpa [run, pairAverage_fixes_agreement _ _ _ he] using h
    · intro h
      obtain ⟨he, ht⟩ := h
      simpa [run, pairAverage_fixes_agreement _ _ _ he] using (ih x).mpr ht

theorem closed_cycle_quiescent (word : List (ι × ι)) (x : ι → ℝ)
    (hcycle : run word x = x) : Quiescent word x :=
  (quadratic_eq_iff_quiescent word x).mp (congrArg quadratic hcycle)

omit [Fintype ι] in
theorem quiescent_run (word : List (ι × ι)) (x : ι → ℝ)
    (hq : Quiescent word x) : run word x = x := by
  induction word with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨he, ht⟩ := hq
    simpa [run, pairAverage_fixes_agreement _ _ _ he] using ih ht

omit [Fintype ι] in
/-- Centre every load at a common baseline without changing the mean law.
This permits balanced deviations to be realized with nonnegative raw loads. -/
theorem pairAverage_shift (u v : ι) (x : ι → ℝ) (b : ℝ) :
    pairAverage u v (fun i => b+x i) = fun i => b+pairAverage u v x i := by
  ext i
  by_cases h : i = u ∨ i = v
  · simp only [pairAverage, LinearMap.coe_mk, AddHom.coe_mk, h, ite_true]
    ring
  · simp [pairAverage, h]

omit [Fintype ι] in
theorem run_shift (word : List (ι × ι)) (x : ι → ℝ) (b : ℝ) :
    run word (fun i => b+x i) = fun i => b+run word x i := by
  induction word generalizing x with
  | nil => rfl
  | cons e es ih => simpa only [run, pairAverage_shift] using ih (pairAverage e.1 e.2 x)

/-- Two memory rails, two initially blank output rails, and ALL ancillary
registers. Values here are deviations from the common raw-load baseline. -/
def beforeCopy (a : ℝ) (r : ι → ℝ) : Fin 4 ⊕ ι → ℝ :=
  Sum.elim ![a, -a, 0, 0] r

def afterCopy (a : ℝ) (r : ι → ℝ) : Fin 4 ⊕ ι → ℝ :=
  Sum.elim ![a, -a, a, -a] r

omit [DecidableEq ι] in
theorem quadratic_beforeCopy (a : ℝ) (r : ι → ℝ) :
    quadratic (beforeCopy a r) = 2*a^2 + quadratic r := by
  simp [quadratic, beforeCopy, Fintype.sum_sum_type, Fin.sum_univ_succ]
  ring

omit [DecidableEq ι] in
theorem quadratic_afterCopy (a : ℝ) (r : ι → ℝ) :
    quadratic (afterCopy a r) = 4*a^2 + quadratic r := by
  simp [quadratic, afterCopy, Fintype.sum_sum_type, Fin.sum_univ_succ]
  ring

omit [DecidableEq ι] in
/-- This balanced copy preserves total load. The quadratic ledger
charges the changed ancillary state, so a reusable catalyst cannot hide
the cost by using zero-sum encodings. -/
theorem copy_total_unchanged (a : ℝ) (r : ι → ℝ) :
    ∑ i, beforeCopy a r i = ∑ i, afterCopy a r i := by
  simp [beforeCopy, afterCopy, Fintype.sum_sum_type, Fin.sum_univ_succ]

theorem copy_ancillary_budget (word : List ((Fin 4 ⊕ ι) × (Fin 4 ⊕ ι)))
    (a : ℝ) (r s : ι → ℝ) (hcopy : run word (beforeCopy a r) = afterCopy a s) :
    quadratic s + 2*a^2 + loss word (beforeCopy a r) = quadratic r := by
  have h := quadratic_ledger word (beforeCopy a r)
  rw [hcopy, quadratic_afterCopy, quadratic_beforeCopy] at h
  linarith

theorem no_catalytic_balanced_copy (word : List ((Fin 4 ⊕ ι) × (Fin 4 ⊕ ι)))
    (a : ℝ) (ha : a ≠ 0) (r : ι → ℝ) :
    run word (beforeCopy a r) ≠ afterCopy a r := by
  intro hcopy
  have h := copy_ancillary_budget word a r r hcopy
  have hp := sq_pos_of_ne_zero ha
  linarith [loss_nonnegative word (beforeCopy a r)]

end
end OPH.SourcePassiveMemoryBudget

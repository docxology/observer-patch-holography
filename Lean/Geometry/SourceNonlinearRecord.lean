module
public import Geometry.SourceRecordProtection

@[expose] public section

set_option autoImplicit false

namespace OPH.SourceNonlinearRecord

open ObserverPatchHolography.ScalarSeamRepair
open scoped BigOperators

variable {ι β : Type*} [DecidableEq ι]

def Nonnegative (x : ι → ℝ) : Prop := ∀ i, 0 ≤ x i

/-- State-only readout invariance on the whole nonnegative state cone.
There is no continuity, linearity, measurability or finite-range assumption. -/
def Protects (E : ι → ι → Prop) (f : (ι → ℝ) → β) : Prop :=
  ∀ u v, E u v → ∀ x, Nonnegative x → f (pairAverage u v x) = f x

theorem nonnegative_single (i : ι) {a : ℝ} (ha : 0 ≤ a) :
    Nonnegative (Pi.single i a) := by
  intro j
  by_cases h : j = i <;> simp [h, ha]

omit [DecidableEq ι] in
theorem nonnegative_add {x y : ι → ℝ} (hx : Nonnegative x) (hy : Nonnegative y) :
    Nonnegative (x + y) := fun i => add_nonneg (hx i) (hy i)

omit [DecidableEq ι] in
theorem nonnegative_sum (s : Finset ι) (x : ι → ι → ℝ)
    (hx : ∀ i ∈ s, Nonnegative (x i)) : Nonnegative (∑ i ∈ s, x i) := by
  intro j
  simpa only [Finset.sum_apply] using Finset.sum_nonneg (fun i hi => hx i hi j)

/-- Both placements have the same image under the actual pair-mean map.
This is a fibre identity, not a claim that the inverse transfer is executable. -/
theorem pairAverage_single_same (u v : ι) (a : ℝ) :
    pairAverage u v (Pi.single u a) = pairAverage u v (Pi.single v a) := by
  by_cases h : u = v
  · subst v; rfl
  · ext j
    by_cases hju : j = u
    · subst j; simp [h, Ne.symm h]
    · by_cases hjv : j = v
      · subst j; simp [h, Ne.symm h]
      · simp [pairAverage_off_seam u v j _ hju hjv, hju, hjv]

theorem protected_move_addend (E : ι → ι → Prop) (f : (ι → ℝ) → β)
    (hf : Protects E f) {u v : ι} (huv : E u v) (z : ι → ℝ)
    (hz : Nonnegative z) {a : ℝ} (ha : 0 ≤ a) :
    f (z + Pi.single u a) = f (z + Pi.single v a) := by
  have hm : pairAverage u v (z + Pi.single u a) =
      pairAverage u v (z + Pi.single v a) := by
    rw [map_add, map_add, pairAverage_single_same]
  rw [← hf u v huv _ (nonnegative_add hz (nonnegative_single u ha)), hm,
      hf u v huv _ (nonnegative_add hz (nonnegative_single v ha))]

theorem protected_move_along_path (E : ι → ι → Prop) (f : (ι → ℝ) → β)
    (hf : Protects E f) {u v : ι} (path : Relation.ReflTransGen E u v)
    (z : ι → ℝ) (hz : Nonnegative z) {a : ℝ} (ha : 0 ≤ a) :
    f (z + Pi.single u a) = f (z + Pi.single v a) := by
  induction path with
  | refl => rfl
  | tail path edge ih => exact ih.trans (protected_move_addend E f hf edge z hz ha)

theorem concentrate_finite_sum (E : ι → ι → Prop) (f : (ι → ℝ) → β)
    (root : ι) (connected : ∀ i, Relation.ReflTransGen E root i) (hf : Protects E f)
    (s : Finset ι) (x : ι → ℝ) (hx : Nonnegative x) :
    ∀ z, Nonnegative z →
      f (z + ∑ i ∈ s, Pi.single i (x i)) =
      f (z + Pi.single root (∑ i ∈ s, x i)) := by
  induction s using Finset.induction_on with
  | empty => intro z hz; simp
  | @insert i s his ih =>
    intro z hz
    have hsum : Nonnegative (∑ j ∈ s, Pi.single j (x j)) :=
      nonnegative_sum s _ (fun j _ => nonnegative_single j (hx j))
    have moved := protected_move_along_path E f hf (connected i)
      (z + ∑ j ∈ s, Pi.single j (x j)) (nonnegative_add hz hsum) (hx i)
    calc
      _ = f ((z + ∑ j ∈ s, Pi.single j (x j)) + Pi.single i (x i)) := by
        congr 1
        rw [Finset.sum_insert his]
        abel
      _ = f ((z + ∑ j ∈ s, Pi.single j (x j)) + Pi.single root (x i)) := moved.symm
      _ = f ((z + Pi.single root (x i)) + ∑ j ∈ s, Pi.single j (x j)) := by
        congr 1; abel
      _ = f ((z + Pi.single root (x i)) + Pi.single root (∑ j ∈ s, x j)) :=
        ih _ (nonnegative_add hz (nonnegative_single root (hx i)))
      _ = _ := by
        congr 1
        rw [Finset.sum_insert his]
        ext j
        by_cases hj : j = root
        · subst j; simp; ring
        · simp [hj]

variable [Fintype ι]

/-- Every invariant state-only record on a connected support factors through
total load, even if its decoder is nonlinear or discontinuous. The quantifier
over ALL nonnegative inputs is essential; restricted code spaces are excluded. -/
theorem protected_record_factors_total (E : ι → ι → Prop) (f : (ι → ℝ) → β)
    (root : ι) (connected : ∀ i, Relation.ReflTransGen E root i) (hf : Protects E f)
    (x : ι → ℝ) (hx : Nonnegative x) :
    f x = f (Pi.single root (∑ i, x i)) := by
  have h := concentrate_finite_sum E f root connected hf Finset.univ x hx 0
    (fun _ => le_rfl)
  have he : (∑ i, Pi.single i (x i)) = x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  simpa [he] using h

theorem sum_pairAverage (u v : ι) (x : ι → ℝ) :
    ∑ i, pairAverage u v x i = ∑ i, x i := by
  have h := (SourceRecordProtection.invariant_iff_equal_coefficients (fun _ : ι => (1 : ℝ))
    u v).mpr rfl x
  simpa [SourceRecordProtection.linearRecord] using h

theorem total_readout_protected (E : ι → ι → Prop) (g : ℝ → β) :
    Protects E (fun x => g (∑ i, x i)) := by
  intro u v _ x _
  change g (∑ i, pairAverage u v x i) = g (∑ i, x i)
  rw [sum_pairAverage]

theorem same_total_same_protected_record (E : ι → ι → Prop) (f : (ι → ℝ) → β)
    (root : ι) (connected : ∀ i, Relation.ReflTransGen E root i) (hf : Protects E f)
    (x y : ι → ℝ) (hx : Nonnegative x) (hy : Nonnegative y)
    (hsum : ∑ i, x i = ∑ i, y i) : f x = f y := by
  rw [protected_record_factors_total E f root connected hf x hx,
      protected_record_factors_total E f root connected hf y hy, hsum]

end OPH.SourceNonlinearRecord

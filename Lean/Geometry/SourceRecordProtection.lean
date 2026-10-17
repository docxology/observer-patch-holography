module
public import ObserverPatchHolography.ScalarSeamRepair

@[expose] public section

/-!
# Linear records protected by seam averaging

For the specified scalar pair-mean law, a linear readout is invariant under
every allowed seam exactly when its endpoint coefficients agree on every
seam. Connected components therefore carry only their total-load linear
records. This class-specific characterization does not exclude persistent
memory, driven repairs, nonlinear records or other accepted dynamics.
-/

namespace OPH.SourceRecordProtection

open ObserverPatchHolography.ScalarSeamRepair
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def linearRecord (w x : ι → ℝ) : ℝ := ∑ i, w i * x i

omit [DecidableEq ι] in
theorem linearRecord_add (w x y : ι → ℝ) :
    linearRecord w (x + y) = linearRecord w x + linearRecord w y := by
  simp [linearRecord, mul_add, Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem linearRecord_sub (w x y : ι → ℝ) :
    linearRecord w (x - y) = linearRecord w x - linearRecord w y := by
  simp [linearRecord, mul_sub, Finset.sum_sub_distrib]

theorem linearRecord_single (w : ι → ℝ) (u : ι) (a : ℝ) :
    linearRecord w (Pi.single u a) = w u * a := by
  simp [linearRecord, Pi.single_apply]

omit [Fintype ι] in
theorem pairAverage_single_difference (u v : ι) (hne : u ≠ v) (x : ι → ℝ) :
    pairAverage u v x =
      x + Pi.single u ((x v - x u) / 2) - Pi.single v ((x v - x u) / 2) := by
  funext i
  by_cases hiu : i = u
  · subst i
    simp [hne]
    ring
  · by_cases hiv : i = v
    · subst i
      simp [Ne.symm hne]
      ring
    · simp [pairAverage_off_seam u v i x hiu hiv, hiu, hiv]

theorem linearRecord_repair_defect (w x : ι → ℝ) (u v : ι) (hne : u ≠ v) :
    linearRecord w (pairAverage u v x) - linearRecord w x =
      (w u - w v) * (x v - x u) / 2 := by
  rw [pairAverage_single_difference u v hne, linearRecord_sub,
    linearRecord_add, linearRecord_single, linearRecord_single]
  ring

theorem invariant_iff_equal_coefficients (w : ι → ℝ) (u v : ι) :
    (∀ x, linearRecord w (pairAverage u v x) = linearRecord w x) ↔ w u = w v := by
  by_cases huv : u = v
  · subst v
    simp [pairAverage_fixes_agreement]
  · constructor
    · intro h
      have hd := linearRecord_repair_defect w (Pi.single v 1) u v huv
      rw [h] at hd
      simp [huv] at hd
      linarith
    · intro h x
      have hd := linearRecord_repair_defect w x u v huv
      rw [h] at hd
      linarith

def Protects (E : ι → ι → Prop) (w : ι → ℝ) : Prop :=
  ∀ u v, E u v → ∀ x, linearRecord w (pairAverage u v x) = linearRecord w x

theorem protects_iff_edge_constant (E : ι → ι → Prop) (w : ι → ℝ) :
    Protects E w ↔ ∀ u v, E u v → w u = w v := by
  simp only [Protects, invariant_iff_equal_coefficients]

theorem protected_equal_along_path (E : ι → ι → Prop) (w : ι → ℝ)
    (hw : Protects E w) {u v : ι} (h : Relation.ReflTransGen E u v) : w u = w v := by
  induction h with
  | refl => rfl
  | @tail v z _ hvz ih =>
    exact ih.trans ((protects_iff_edge_constant E w).mp hw v z hvz)

theorem connected_protected_record_factors_through_total
    (E : ι → ι → Prop) (w : ι → ℝ) (root : ι)
    (hconnected : ∀ i, Relation.ReflTransGen E root i) (hw : Protects E w)
    (x : ι → ℝ) : linearRecord w x = w root * ∑ i, x i := by
  unfold linearRecord
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [protected_equal_along_path E w hw (hconnected i)]

theorem constant_coefficients_protect (E : ι → ι → Prop) (c : ℝ) :
    Protects E (fun _ => c) := by
  rw [protects_iff_edge_constant]
  intros
  rfl

/-- One active seam changes every linear coordinate distinguishing its endpoints. -/
theorem active_distinguishing_seam_changes_record (w x : ι → ℝ) (u v : ι)
    (hw : w u ≠ w v) (hx : x u ≠ x v) :
    linearRecord w (pairAverage u v x) ≠ linearRecord w x := by
  have huv : u ≠ v := by
    intro h
    exact hw (congrArg w h)
  intro heq
  have hd := linearRecord_repair_defect w x u v huv
  rw [heq, sub_self] at hd
  have hn : (w u - w v) * (x v - x u) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hw) (sub_ne_zero.mpr hx.symm)) (by norm_num)
  exact hn hd.symm

end OPH.SourceRecordProtection

#print axioms OPH.SourceRecordProtection.invariant_iff_equal_coefficients
#print axioms OPH.SourceRecordProtection.connected_protected_record_factors_through_total
#print axioms OPH.SourceRecordProtection.active_distinguishing_seam_changes_record

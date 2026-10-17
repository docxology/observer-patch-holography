module
public import Geometry.SourcePublicationNative
public import Geometry.SourceCheckpointEntropy

@[expose] public section

/-! Common-space record-menu selection.
The joint entropy problem includes a public-demand label as an actual random
variable. Its marginal weights are prior times continuation mass; positive
recoverability prevents deterministic selection of a single competing label.
This is a theorem about this declared common algebra, not full A1--A3. -/

set_option autoImplicit false

namespace OPH.SourcePublicationMenu
noncomputable section
open OPH.SourceCheckpointPolicy OPH.SourcePublicationMass
open OPH.SourcePublicationNative OPH.SourceTemporalGuard
open OPH.SourceCheckpointMeaning Filter
open scoped Topology

variable {M S A : Type*} [Fintype M] [Fintype A]

def selected (prior h : M → ℝ) (m : M) : ℝ :=
  prior m*h m / ∑ j, prior j*h j

omit [Fintype A] in
theorem selected_positive_of_recoverable (prior h : M → ℝ)
    (hp : ∀ m, 0 < prior m) (hn : ∀ m, 0 ≤ h m) (m : M) (hm : 0 < h m) :
    0 < selected prior h m := by
  have hz : 0 < ∑ j, prior j*h j :=
    (Finset.single_le_sum (fun j _ => mul_nonneg (hp j).le (hn j))
      (Finset.mem_univ m)).trans_lt' (mul_pos (hp m) hm)
  exact div_pos (mul_pos (hp m) hm) hz

omit [Fintype A] in
theorem selected_positive (prior h : M → ℝ) (hp : ∀ m, 0 < prior m)
    (hh : ∀ m, 0 < h m) (m : M) : 0 < selected prior h m := by
  exact selected_positive_of_recoverable prior h hp (fun j => (hh j).le) m (hh m)

omit [Fintype A] in
theorem selected_zero_of_unrecoverable (prior h : M → ℝ) (m : M) (hm : h m = 0) :
    selected prior h m = 0 := by simp [selected,hm]

omit [Fintype A] in
theorem cannot_exclude_recoverable (prior h : M → ℝ) (hp : ∀ m, 0 < prior m)
    (hh : ∀ m, 0 < h m) (m : M) : selected prior h m ≠ 0 :=
  ne_of_gt (selected_positive prior h hp hh m)

omit [Fintype A] in
/-- If native dynamics publishes every candidate demand almost surely,
the joint information projection leaves the demand prior unchanged. -/
theorem automatic_demands_unchanged (prior : M → ℝ) (hp : ∑ m, prior m = 1)
    (m : M) : selected prior (fun _ => 1) m = prior m := by
  simp only [selected,mul_one,hp,div_one]

/-- The finite joint information projection's demand marginal tends to
prior times eventual publication mass, without a supplied deadline. -/
theorem selected_tendsto (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (hs : ∀ s, ∑ a, weight s a = 1)
    (f : M → S → ℝ) (hf : ∀ m s, f m s ≤ 1)
    (hp : ∀ m s, f m s ≤ ∑ a, weight s a*f m (step s a))
    (prior : M → ℝ) (s : S)
    (hz : (∑ j, prior j*eventual step weight (f j) s) ≠ 0) (m : M) :
    Tendsto (fun n => selected prior (fun j => mass step weight (f j) n s) m) atTop
      (𝓝 (selected prior (fun j => eventual step weight (f j) s) m)) := by
  have ht (j : M) := (mass_tendsto step weight hw hs (f j) (hf j) (hp j) s).const_mul (prior j)
  exact (ht m).div (tendsto_finsetSum Finset.univ (fun j _ => ht j)) hz

omit [Fintype A] in
/-- Sum over all finite history atoms, retaining the inherited joint prior. -/
theorem joint_marginal {W : Type*} [Fintype W]
    (prior : M → ℝ) (r : W → ℝ) (accept : M → W → ℝ) (m : M) :
    (∑ w, prior m*r w*accept m w /
      (∑ j, prior j*(∑ v, r v*accept j v))) =
        selected prior (fun j => ∑ w, r w*accept j w) m := by
  unfold selected
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  ring

theorem two_meaning_control :
    selected (fun _ : Fin 2 => (1/2 : ℝ)) ![1/2,1] 0 = 1/3 ∧
      selected (fun _ : Fin 2 => (1/2 : ℝ)) ![1/2,1] 1 = 2/3 := by
  norm_num [selected,Fin.sum_univ_two]

/-- An impossible competing label is removed without excluding either
recoverable label. The all-positive-menu premise is unnecessary. -/
theorem mixed_meaning_control :
    selected (fun _ : Fin 3 => (1/3 : ℝ)) ![0,1/2,1] 0 = 0 ∧
    selected (fun _ : Fin 3 => (1/3 : ℝ)) ![0,1/2,1] 1 = 1/3 ∧
    selected (fun _ : Fin 3 => (1/3 : ℝ)) ![0,1/2,1] 2 = 2/3 := by
  have hlast : (![0,1/2,1] : Fin 3 → ℝ) 2 = 1 := rfl
  norm_num [selected,Fin.sum_univ_three,hlast]

end
end OPH.SourcePublicationMenu
